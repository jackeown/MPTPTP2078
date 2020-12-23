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
% DateTime   : Thu Dec  3 13:19:33 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  196 ( 433 expanded)
%              Number of leaves         :   47 ( 194 expanded)
%              Depth                    :   11
%              Number of atoms          :  819 (2065 expanded)
%              Number of equality atoms :  121 ( 332 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f579,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f91,f92,f96,f100,f104,f108,f117,f125,f127,f134,f139,f167,f205,f239,f250,f257,f267,f272,f287,f345,f362,f496,f503,f510,f518,f519,f524,f548,f561,f562,f578])).

fof(f578,plain,
    ( ~ spl3_5
    | ~ spl3_44
    | spl3_12
    | ~ spl3_71 ),
    inference(avatar_split_clause,[],[f570,f545,f137,f333,f98])).

fof(f98,plain,
    ( spl3_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f333,plain,
    ( spl3_44
  <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f137,plain,
    ( spl3_12
  <=> v3_pre_topc(u1_struct_0(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f545,plain,
    ( spl3_71
  <=> r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_71])])).

fof(f570,plain,
    ( v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_71 ),
    inference(resolution,[],[f546,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f546,plain,
    ( r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ spl3_71 ),
    inference(avatar_component_clause,[],[f545])).

fof(f562,plain,
    ( u1_pre_topc(sK0) != u1_pre_topc(k8_tmap_1(sK0,sK1))
    | k8_tmap_1(sK0,sK1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k8_tmap_1(sK0,sK1)))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f561,plain,
    ( u1_pre_topc(sK0) != u1_pre_topc(k8_tmap_1(sK0,sK1))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK0)
    | k8_tmap_1(sK0,sK1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k8_tmap_1(sK0,sK1)))
    | k8_tmap_1(sK0,sK1) = k8_tmap_1(sK0,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f548,plain,
    ( spl3_71
    | ~ spl3_44
    | ~ spl3_2
    | spl3_4
    | ~ spl3_33
    | ~ spl3_49
    | ~ spl3_68 ),
    inference(avatar_split_clause,[],[f543,f508,f360,f265,f94,f81,f333,f545])).

fof(f81,plain,
    ( spl3_2
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f94,plain,
    ( spl3_4
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f265,plain,
    ( spl3_33
  <=> u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f360,plain,
    ( spl3_49
  <=> ! [X1] :
        ( u1_pre_topc(sK0) != u1_pre_topc(k8_tmap_1(sK0,X1))
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(u1_struct_0(X1),u1_pre_topc(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f508,plain,
    ( spl3_68
  <=> k8_tmap_1(sK0,sK1) = k8_tmap_1(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_68])])).

fof(f543,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ spl3_33
    | ~ spl3_49
    | ~ spl3_68 ),
    inference(trivial_inequality_removal,[],[f542])).

fof(f542,plain,
    ( u1_pre_topc(sK0) != u1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ spl3_33
    | ~ spl3_49
    | ~ spl3_68 ),
    inference(forward_demodulation,[],[f536,f266])).

fof(f266,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK0))
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f265])).

fof(f536,plain,
    ( u1_pre_topc(sK0) != u1_pre_topc(k8_tmap_1(sK0,sK0))
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ spl3_49
    | ~ spl3_68 ),
    inference(superposition,[],[f361,f509])).

fof(f509,plain,
    ( k8_tmap_1(sK0,sK1) = k8_tmap_1(sK0,sK0)
    | ~ spl3_68 ),
    inference(avatar_component_clause,[],[f508])).

fof(f361,plain,
    ( ! [X1] :
        ( u1_pre_topc(sK0) != u1_pre_topc(k8_tmap_1(sK0,X1))
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(u1_struct_0(X1),u1_pre_topc(sK0)) )
    | ~ spl3_49 ),
    inference(avatar_component_clause,[],[f360])).

fof(f524,plain,
    ( ~ spl3_12
    | ~ spl3_44
    | ~ spl3_2
    | spl3_70
    | spl3_4
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f258,f254,f94,f522,f81,f333,f137])).

fof(f522,plain,
    ( spl3_70
  <=> u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_70])])).

fof(f254,plain,
    ( spl3_31
  <=> ! [X1] :
        ( u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,X1))
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(u1_struct_0(X1),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f258,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | spl3_4
    | ~ spl3_31 ),
    inference(resolution,[],[f255,f95])).

fof(f95,plain,
    ( ~ v2_struct_0(sK1)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f94])).

fof(f255,plain,
    ( ! [X1] :
        ( v2_struct_0(X1)
        | u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,X1))
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(u1_struct_0(X1),sK0) )
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f254])).

fof(f519,plain,
    ( ~ spl3_5
    | spl3_69
    | ~ spl3_23
    | ~ spl3_33
    | ~ spl3_66 ),
    inference(avatar_split_clause,[],[f505,f494,f265,f203,f513,f98])).

fof(f513,plain,
    ( spl3_69
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).

fof(f203,plain,
    ( spl3_23
  <=> u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f494,plain,
    ( spl3_66
  <=> ! [X1] :
        ( k8_tmap_1(sK0,X1) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,X1)),u1_pre_topc(k8_tmap_1(sK0,X1)))
        | ~ m1_pre_topc(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).

fof(f505,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_23
    | ~ spl3_33
    | ~ spl3_66 ),
    inference(forward_demodulation,[],[f504,f204])).

fof(f204,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK0))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f203])).

fof(f504,plain,
    ( k8_tmap_1(sK0,sK0) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK0)),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_33
    | ~ spl3_66 ),
    inference(forward_demodulation,[],[f498,f266])).

fof(f498,plain,
    ( k8_tmap_1(sK0,sK0) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK0)),u1_pre_topc(k8_tmap_1(sK0,sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_66 ),
    inference(resolution,[],[f495,f58])).

fof(f58,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f495,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | k8_tmap_1(sK0,X1) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,X1)),u1_pre_topc(k8_tmap_1(sK0,X1))) )
    | ~ spl3_66 ),
    inference(avatar_component_clause,[],[f494])).

fof(f518,plain,
    ( ~ spl3_5
    | ~ spl3_2
    | ~ spl3_1
    | spl3_12 ),
    inference(avatar_split_clause,[],[f140,f137,f78,f81,f98])).

fof(f78,plain,
    ( spl3_1
  <=> v1_tsep_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f140,plain,
    ( ~ v1_tsep_1(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | spl3_12 ),
    inference(resolution,[],[f138,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(global_subsumption,[],[f60,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( v3_pre_topc(X3,X0)
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tsep_1(X1,X0)
              | ( ~ v3_pre_topc(sK2(X0,X1),X0)
                & u1_struct_0(X1) = sK2(X0,X1)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tsep_1(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK2(X0,X1),X0)
        & u1_struct_0(X1) = sK2(X0,X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tsep_1(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tsep_1(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tsep_1(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v3_pre_topc(X2,X0)
                  | u1_struct_0(X1) != X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tsep_1(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tsep_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f138,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | spl3_12 ),
    inference(avatar_component_clause,[],[f137])).

fof(f510,plain,
    ( ~ spl3_5
    | spl3_68
    | ~ spl3_3
    | ~ spl3_23
    | ~ spl3_33
    | ~ spl3_66 ),
    inference(avatar_split_clause,[],[f506,f494,f265,f203,f84,f508,f98])).

fof(f84,plain,
    ( spl3_3
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f506,plain,
    ( k8_tmap_1(sK0,sK1) = k8_tmap_1(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_3
    | ~ spl3_23
    | ~ spl3_33
    | ~ spl3_66 ),
    inference(forward_demodulation,[],[f505,f88])).

fof(f88,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f84])).

fof(f503,plain,
    ( spl3_67
    | ~ spl3_2
    | ~ spl3_17
    | ~ spl3_66 ),
    inference(avatar_split_clause,[],[f499,f494,f165,f81,f501])).

fof(f501,plain,
    ( spl3_67
  <=> k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k8_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_67])])).

fof(f165,plain,
    ( spl3_17
  <=> u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f499,plain,
    ( k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k8_tmap_1(sK0,sK1)))
    | ~ spl3_2
    | ~ spl3_17
    | ~ spl3_66 ),
    inference(forward_demodulation,[],[f497,f166])).

fof(f166,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f165])).

fof(f497,plain,
    ( k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK1)),u1_pre_topc(k8_tmap_1(sK0,sK1)))
    | ~ spl3_2
    | ~ spl3_66 ),
    inference(resolution,[],[f495,f87])).

fof(f87,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f496,plain,
    ( spl3_66
    | ~ spl3_5
    | ~ spl3_6
    | spl3_7 ),
    inference(avatar_split_clause,[],[f492,f106,f102,f98,f494])).

fof(f102,plain,
    ( spl3_6
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f106,plain,
    ( spl3_7
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f492,plain,
    ( ! [X1] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | k8_tmap_1(sK0,X1) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,X1)),u1_pre_topc(k8_tmap_1(sK0,X1)))
        | ~ m1_pre_topc(X1,sK0) )
    | spl3_7 ),
    inference(resolution,[],[f448,f107])).

fof(f107,plain,
    ( ~ v2_struct_0(sK0)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f106])).

fof(f448,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | k8_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(k8_tmap_1(X0,X1)),u1_pre_topc(k8_tmap_1(X0,X1)))
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f447])).

fof(f447,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | k8_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(k8_tmap_1(X0,X1)),u1_pre_topc(k8_tmap_1(X0,X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f128,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_tmap_1)).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(k8_tmap_1(X1,X0))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | k8_tmap_1(X1,X0) = g1_pre_topc(u1_struct_0(k8_tmap_1(X1,X0)),u1_pre_topc(k8_tmap_1(X1,X0)))
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(resolution,[],[f72,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f72,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f362,plain,
    ( spl3_7
    | ~ spl3_6
    | ~ spl3_5
    | spl3_49
    | ~ spl3_36 ),
    inference(avatar_split_clause,[],[f356,f285,f360,f98,f102,f106])).

fof(f285,plain,
    ( spl3_36
  <=> ! [X1] :
        ( u1_pre_topc(sK0) != k5_tmap_1(sK0,X1)
        | r2_hidden(X1,u1_pre_topc(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f356,plain,
    ( ! [X1] :
        ( u1_pre_topc(sK0) != u1_pre_topc(k8_tmap_1(sK0,X1))
        | r2_hidden(u1_struct_0(X1),u1_pre_topc(sK0))
        | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl3_36 ),
    inference(superposition,[],[f286,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(global_subsumption,[],[f60,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ! [X2] :
                ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ! [X2] :
                ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) ) )
            & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_tmap_1)).

fof(f286,plain,
    ( ! [X1] :
        ( u1_pre_topc(sK0) != k5_tmap_1(sK0,X1)
        | r2_hidden(X1,u1_pre_topc(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f285])).

fof(f345,plain,
    ( ~ spl3_5
    | ~ spl3_2
    | spl3_44 ),
    inference(avatar_split_clause,[],[f340,f333,f81,f98])).

fof(f340,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | spl3_44 ),
    inference(resolution,[],[f334,f60])).

fof(f334,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_44 ),
    inference(avatar_component_clause,[],[f333])).

fof(f287,plain,
    ( ~ spl3_6
    | ~ spl3_5
    | spl3_36
    | spl3_7 ),
    inference(avatar_split_clause,[],[f283,f106,f285,f98,f102])).

fof(f283,plain,
    ( ! [X1] :
        ( u1_pre_topc(sK0) != k5_tmap_1(sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | r2_hidden(X1,u1_pre_topc(sK0)) )
    | spl3_7 ),
    inference(resolution,[],[f68,f107])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | u1_pre_topc(X0) != k5_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | r2_hidden(X1,u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X1,u1_pre_topc(X0))
              | u1_pre_topc(X0) != k5_tmap_1(X0,X1) )
            & ( u1_pre_topc(X0) = k5_tmap_1(X0,X1)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).

fof(f272,plain,(
    spl3_32 ),
    inference(avatar_contradiction_clause,[],[f271])).

fof(f271,plain,
    ( $false
    | spl3_32 ),
    inference(resolution,[],[f263,f109])).

fof(f109,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f55,f54])).

fof(f54,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f55,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f263,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_32 ),
    inference(avatar_component_clause,[],[f262])).

fof(f262,plain,
    ( spl3_32
  <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f267,plain,
    ( ~ spl3_10
    | ~ spl3_32
    | ~ spl3_29
    | spl3_33
    | spl3_7
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f259,f254,f106,f265,f233,f262,f123])).

fof(f123,plain,
    ( spl3_10
  <=> v3_pre_topc(u1_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f233,plain,
    ( spl3_29
  <=> m1_pre_topc(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f259,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK0))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(u1_struct_0(sK0),sK0)
    | spl3_7
    | ~ spl3_31 ),
    inference(resolution,[],[f255,f107])).

fof(f257,plain,
    ( spl3_7
    | ~ spl3_6
    | ~ spl3_5
    | spl3_31
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f252,f248,f254,f98,f102,f106])).

fof(f248,plain,
    ( spl3_30
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X1,sK0)
        | u1_pre_topc(sK0) = k5_tmap_1(sK0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f252,plain,
    ( ! [X0] :
        ( u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,X0))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ v3_pre_topc(u1_struct_0(X0),sK0)
        | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_30 ),
    inference(superposition,[],[f111,f249])).

fof(f249,plain,
    ( ! [X1] :
        ( u1_pre_topc(sK0) = k5_tmap_1(sK0,X1)
        | ~ v3_pre_topc(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f248])).

fof(f250,plain,
    ( ~ spl3_6
    | ~ spl3_5
    | spl3_30
    | spl3_7 ),
    inference(avatar_split_clause,[],[f246,f106,f248,f98,f102])).

fof(f246,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | u1_pre_topc(sK0) = k5_tmap_1(sK0,X1)
        | ~ v3_pre_topc(X1,sK0) )
    | spl3_7 ),
    inference(resolution,[],[f237,f107])).

fof(f237,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | u1_pre_topc(X0) = k5_tmap_1(X0,X1)
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f236])).

fof(f236,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(X0) = k5_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f67,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,u1_pre_topc(X0))
      | u1_pre_topc(X0) = k5_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f239,plain,
    ( ~ spl3_5
    | spl3_29 ),
    inference(avatar_split_clause,[],[f238,f233,f98])).

fof(f238,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_29 ),
    inference(resolution,[],[f234,f58])).

fof(f234,plain,
    ( ~ m1_pre_topc(sK0,sK0)
    | spl3_29 ),
    inference(avatar_component_clause,[],[f233])).

fof(f205,plain,
    ( ~ spl3_6
    | ~ spl3_5
    | spl3_23
    | spl3_7 ),
    inference(avatar_split_clause,[],[f201,f106,f203,f98,f102])).

fof(f201,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl3_7 ),
    inference(resolution,[],[f147,f107])).

fof(f147,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(global_subsumption,[],[f58,f146])).

fof(f146,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ m1_pre_topc(X0,X0)
      | u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(factoring,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f167,plain,
    ( ~ spl3_2
    | ~ spl3_6
    | ~ spl3_5
    | spl3_17
    | spl3_4
    | spl3_7 ),
    inference(avatar_split_clause,[],[f149,f106,f94,f165,f98,f102,f81])).

fof(f149,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | spl3_4
    | spl3_7 ),
    inference(resolution,[],[f144,f107])).

fof(f144,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,sK1))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_pre_topc(sK1,X0) )
    | spl3_4 ),
    inference(resolution,[],[f69,f95])).

fof(f139,plain,
    ( ~ spl3_5
    | ~ spl3_2
    | spl3_1
    | ~ spl3_12
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f135,f132,f137,f78,f81,f98])).

fof(f132,plain,
    ( spl3_11
  <=> u1_struct_0(sK1) = sK2(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f135,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | v1_tsep_1(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_11 ),
    inference(superposition,[],[f64,f133])).

fof(f133,plain,
    ( u1_struct_0(sK1) = sK2(sK0,sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f132])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(sK2(X0,X1),X0)
      | v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f134,plain,
    ( ~ spl3_5
    | ~ spl3_2
    | spl3_11
    | spl3_1 ),
    inference(avatar_split_clause,[],[f130,f78,f132,f81,f98])).

fof(f130,plain,
    ( u1_struct_0(sK1) = sK2(sK0,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | spl3_1 ),
    inference(resolution,[],[f63,f79])).

fof(f79,plain,
    ( ~ v1_tsep_1(sK1,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | u1_struct_0(X1) = sK2(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f127,plain,
    ( ~ spl3_5
    | spl3_9 ),
    inference(avatar_split_clause,[],[f126,f120,f98])).

fof(f120,plain,
    ( spl3_9
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f126,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_9 ),
    inference(resolution,[],[f121,f57])).

fof(f57,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f121,plain,
    ( ~ l1_struct_0(sK0)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f120])).

fof(f125,plain,
    ( ~ spl3_9
    | spl3_10
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f118,f114,f123,f120])).

fof(f114,plain,
    ( spl3_8
  <=> v3_pre_topc(k2_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f118,plain,
    ( v3_pre_topc(u1_struct_0(sK0),sK0)
    | ~ l1_struct_0(sK0)
    | ~ spl3_8 ),
    inference(superposition,[],[f115,f56])).

fof(f56,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f115,plain,
    ( v3_pre_topc(k2_struct_0(sK0),sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f114])).

fof(f117,plain,
    ( spl3_8
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f112,f102,f98,f114])).

fof(f112,plain,
    ( ~ l1_pre_topc(sK0)
    | v3_pre_topc(k2_struct_0(sK0),sK0)
    | ~ spl3_6 ),
    inference(resolution,[],[f71,f103])).

fof(f103,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f102])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(k2_struct_0(X0),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f108,plain,(
    ~ spl3_7 ),
    inference(avatar_split_clause,[],[f46,f106])).

fof(f46,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1)
      | ~ m1_pre_topc(sK1,sK0)
      | ~ v1_tsep_1(sK1,sK0) )
    & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
      | ( m1_pre_topc(sK1,sK0)
        & v1_tsep_1(sK1,sK0) ) )
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f38,f37])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1)
              | ~ m1_pre_topc(X1,X0)
              | ~ v1_tsep_1(X1,X0) )
            & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)
              | ( m1_pre_topc(X1,X0)
                & v1_tsep_1(X1,X0) ) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,X1)
            | ~ m1_pre_topc(X1,sK0)
            | ~ v1_tsep_1(X1,sK0) )
          & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,X1)
            | ( m1_pre_topc(X1,sK0)
              & v1_tsep_1(X1,sK0) ) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X1] :
        ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,X1)
          | ~ m1_pre_topc(X1,sK0)
          | ~ v1_tsep_1(X1,sK0) )
        & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,X1)
          | ( m1_pre_topc(X1,sK0)
            & v1_tsep_1(X1,sK0) ) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1)
        | ~ m1_pre_topc(sK1,sK0)
        | ~ v1_tsep_1(sK1,sK0) )
      & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
        | ( m1_pre_topc(sK1,sK0)
          & v1_tsep_1(sK1,sK0) ) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1)
            | ~ m1_pre_topc(X1,X0)
            | ~ v1_tsep_1(X1,X0) )
          & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)
            | ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) ) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1)
            | ~ m1_pre_topc(X1,X0)
            | ~ v1_tsep_1(X1,X0) )
          & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)
            | ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) ) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ( ( m1_pre_topc(X1,X0)
                & v1_tsep_1(X1,X0) )
            <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_tmap_1)).

fof(f104,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f47,f102])).

fof(f47,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f100,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f48,f98])).

fof(f48,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f96,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f49,f94])).

fof(f49,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f92,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f50,f81])).

fof(f50,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f91,plain,
    ( spl3_1
    | spl3_3 ),
    inference(avatar_split_clause,[],[f51,f84,f78])).

fof(f51,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
    | v1_tsep_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f86,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f53,f84,f81,f78])).

fof(f53,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v1_tsep_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:15:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.42  % (11025)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.42  % (11017)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.44  % (11017)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.44  % SZS output start Proof for theBenchmark
% 0.20/0.44  fof(f579,plain,(
% 0.20/0.44    $false),
% 0.20/0.44    inference(avatar_sat_refutation,[],[f86,f91,f92,f96,f100,f104,f108,f117,f125,f127,f134,f139,f167,f205,f239,f250,f257,f267,f272,f287,f345,f362,f496,f503,f510,f518,f519,f524,f548,f561,f562,f578])).
% 0.20/0.44  fof(f578,plain,(
% 0.20/0.44    ~spl3_5 | ~spl3_44 | spl3_12 | ~spl3_71),
% 0.20/0.44    inference(avatar_split_clause,[],[f570,f545,f137,f333,f98])).
% 0.20/0.44  fof(f98,plain,(
% 0.20/0.44    spl3_5 <=> l1_pre_topc(sK0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.44  fof(f333,plain,(
% 0.20/0.44    spl3_44 <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 0.20/0.44  fof(f137,plain,(
% 0.20/0.44    spl3_12 <=> v3_pre_topc(u1_struct_0(sK1),sK0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.44  fof(f545,plain,(
% 0.20/0.44    spl3_71 <=> r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_71])])).
% 0.20/0.44  fof(f570,plain,(
% 0.20/0.44    v3_pre_topc(u1_struct_0(sK1),sK0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_71),
% 0.20/0.44    inference(resolution,[],[f546,f66])).
% 0.20/0.44  fof(f66,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r2_hidden(X1,u1_pre_topc(X0)) | v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f44])).
% 0.20/0.44  fof(f44,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.44    inference(nnf_transformation,[],[f26])).
% 0.20/0.44  fof(f26,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.44    inference(ennf_transformation,[],[f5])).
% 0.20/0.44  fof(f5,axiom,(
% 0.20/0.44    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).
% 0.20/0.44  fof(f546,plain,(
% 0.20/0.44    r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) | ~spl3_71),
% 0.20/0.44    inference(avatar_component_clause,[],[f545])).
% 0.20/0.44  fof(f562,plain,(
% 0.20/0.44    u1_pre_topc(sK0) != u1_pre_topc(k8_tmap_1(sK0,sK1)) | k8_tmap_1(sK0,sK1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k8_tmap_1(sK0,sK1))) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)),
% 0.20/0.44    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.44  fof(f561,plain,(
% 0.20/0.44    u1_pre_topc(sK0) != u1_pre_topc(k8_tmap_1(sK0,sK1)) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK0) | k8_tmap_1(sK0,sK1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k8_tmap_1(sK0,sK1))) | k8_tmap_1(sK0,sK1) = k8_tmap_1(sK0,sK0)),
% 0.20/0.44    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.44  fof(f548,plain,(
% 0.20/0.44    spl3_71 | ~spl3_44 | ~spl3_2 | spl3_4 | ~spl3_33 | ~spl3_49 | ~spl3_68),
% 0.20/0.44    inference(avatar_split_clause,[],[f543,f508,f360,f265,f94,f81,f333,f545])).
% 0.20/0.44  fof(f81,plain,(
% 0.20/0.44    spl3_2 <=> m1_pre_topc(sK1,sK0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.44  fof(f94,plain,(
% 0.20/0.44    spl3_4 <=> v2_struct_0(sK1)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.44  fof(f265,plain,(
% 0.20/0.44    spl3_33 <=> u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK0))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.20/0.44  fof(f360,plain,(
% 0.20/0.44    spl3_49 <=> ! [X1] : (u1_pre_topc(sK0) != u1_pre_topc(k8_tmap_1(sK0,X1)) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(u1_struct_0(X1),u1_pre_topc(sK0)))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 0.20/0.44  fof(f508,plain,(
% 0.20/0.44    spl3_68 <=> k8_tmap_1(sK0,sK1) = k8_tmap_1(sK0,sK0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_68])])).
% 0.20/0.44  fof(f543,plain,(
% 0.20/0.44    v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) | (~spl3_33 | ~spl3_49 | ~spl3_68)),
% 0.20/0.44    inference(trivial_inequality_removal,[],[f542])).
% 0.20/0.44  fof(f542,plain,(
% 0.20/0.44    u1_pre_topc(sK0) != u1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) | (~spl3_33 | ~spl3_49 | ~spl3_68)),
% 0.20/0.44    inference(forward_demodulation,[],[f536,f266])).
% 0.20/0.44  fof(f266,plain,(
% 0.20/0.44    u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK0)) | ~spl3_33),
% 0.20/0.44    inference(avatar_component_clause,[],[f265])).
% 0.20/0.44  fof(f536,plain,(
% 0.20/0.44    u1_pre_topc(sK0) != u1_pre_topc(k8_tmap_1(sK0,sK0)) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) | (~spl3_49 | ~spl3_68)),
% 0.20/0.44    inference(superposition,[],[f361,f509])).
% 0.20/0.44  fof(f509,plain,(
% 0.20/0.44    k8_tmap_1(sK0,sK1) = k8_tmap_1(sK0,sK0) | ~spl3_68),
% 0.20/0.44    inference(avatar_component_clause,[],[f508])).
% 0.20/0.44  fof(f361,plain,(
% 0.20/0.44    ( ! [X1] : (u1_pre_topc(sK0) != u1_pre_topc(k8_tmap_1(sK0,X1)) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(u1_struct_0(X1),u1_pre_topc(sK0))) ) | ~spl3_49),
% 0.20/0.44    inference(avatar_component_clause,[],[f360])).
% 0.20/0.44  fof(f524,plain,(
% 0.20/0.44    ~spl3_12 | ~spl3_44 | ~spl3_2 | spl3_70 | spl3_4 | ~spl3_31),
% 0.20/0.44    inference(avatar_split_clause,[],[f258,f254,f94,f522,f81,f333,f137])).
% 0.20/0.44  fof(f522,plain,(
% 0.20/0.44    spl3_70 <=> u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_70])])).
% 0.20/0.44  fof(f254,plain,(
% 0.20/0.44    spl3_31 <=> ! [X1] : (u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,X1)) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(u1_struct_0(X1),sK0))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.20/0.44  fof(f258,plain,(
% 0.20/0.44    u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1)) | ~m1_pre_topc(sK1,sK0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(u1_struct_0(sK1),sK0) | (spl3_4 | ~spl3_31)),
% 0.20/0.44    inference(resolution,[],[f255,f95])).
% 0.20/0.44  fof(f95,plain,(
% 0.20/0.44    ~v2_struct_0(sK1) | spl3_4),
% 0.20/0.44    inference(avatar_component_clause,[],[f94])).
% 0.20/0.44  fof(f255,plain,(
% 0.20/0.44    ( ! [X1] : (v2_struct_0(X1) | u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,X1)) | ~m1_pre_topc(X1,sK0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(u1_struct_0(X1),sK0)) ) | ~spl3_31),
% 0.20/0.44    inference(avatar_component_clause,[],[f254])).
% 0.20/0.44  fof(f519,plain,(
% 0.20/0.44    ~spl3_5 | spl3_69 | ~spl3_23 | ~spl3_33 | ~spl3_66),
% 0.20/0.44    inference(avatar_split_clause,[],[f505,f494,f265,f203,f513,f98])).
% 0.20/0.44  fof(f513,plain,(
% 0.20/0.44    spl3_69 <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).
% 0.20/0.44  fof(f203,plain,(
% 0.20/0.44    spl3_23 <=> u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK0))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.20/0.44  fof(f494,plain,(
% 0.20/0.44    spl3_66 <=> ! [X1] : (k8_tmap_1(sK0,X1) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,X1)),u1_pre_topc(k8_tmap_1(sK0,X1))) | ~m1_pre_topc(X1,sK0))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).
% 0.20/0.44  fof(f505,plain,(
% 0.20/0.44    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK0) | ~l1_pre_topc(sK0) | (~spl3_23 | ~spl3_33 | ~spl3_66)),
% 0.20/0.44    inference(forward_demodulation,[],[f504,f204])).
% 0.20/0.44  fof(f204,plain,(
% 0.20/0.44    u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK0)) | ~spl3_23),
% 0.20/0.44    inference(avatar_component_clause,[],[f203])).
% 0.20/0.44  fof(f504,plain,(
% 0.20/0.44    k8_tmap_1(sK0,sK0) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK0)),u1_pre_topc(sK0)) | ~l1_pre_topc(sK0) | (~spl3_33 | ~spl3_66)),
% 0.20/0.44    inference(forward_demodulation,[],[f498,f266])).
% 0.20/0.44  fof(f498,plain,(
% 0.20/0.44    k8_tmap_1(sK0,sK0) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK0)),u1_pre_topc(k8_tmap_1(sK0,sK0))) | ~l1_pre_topc(sK0) | ~spl3_66),
% 0.20/0.44    inference(resolution,[],[f495,f58])).
% 0.20/0.44  fof(f58,plain,(
% 0.20/0.44    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f20])).
% 0.20/0.44  fof(f20,plain,(
% 0.20/0.44    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.20/0.44    inference(ennf_transformation,[],[f13])).
% 0.20/0.44  fof(f13,axiom,(
% 0.20/0.44    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.20/0.44  fof(f495,plain,(
% 0.20/0.44    ( ! [X1] : (~m1_pre_topc(X1,sK0) | k8_tmap_1(sK0,X1) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,X1)),u1_pre_topc(k8_tmap_1(sK0,X1)))) ) | ~spl3_66),
% 0.20/0.44    inference(avatar_component_clause,[],[f494])).
% 0.20/0.44  fof(f518,plain,(
% 0.20/0.44    ~spl3_5 | ~spl3_2 | ~spl3_1 | spl3_12),
% 0.20/0.44    inference(avatar_split_clause,[],[f140,f137,f78,f81,f98])).
% 0.20/0.44  fof(f78,plain,(
% 0.20/0.44    spl3_1 <=> v1_tsep_1(sK1,sK0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.44  fof(f140,plain,(
% 0.20/0.44    ~v1_tsep_1(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | spl3_12),
% 0.20/0.44    inference(resolution,[],[f138,f110])).
% 0.20/0.44  fof(f110,plain,(
% 0.20/0.44    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.44    inference(global_subsumption,[],[f60,f75])).
% 0.20/0.44  fof(f75,plain,(
% 0.20/0.44    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.44    inference(equality_resolution,[],[f61])).
% 0.20/0.44  fof(f61,plain,(
% 0.20/0.44    ( ! [X0,X3,X1] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f43])).
% 0.20/0.44  fof(f43,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | (~v3_pre_topc(sK2(X0,X1),X0) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).
% 0.20/0.44  fof(f42,plain,(
% 0.20/0.44    ! [X1,X0] : (? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK2(X0,X1),X0) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f41,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.44    inference(rectify,[],[f40])).
% 0.20/0.44  fof(f40,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.44    inference(nnf_transformation,[],[f25])).
% 0.20/0.44  fof(f25,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.44    inference(flattening,[],[f24])).
% 0.20/0.44  fof(f24,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.44    inference(ennf_transformation,[],[f8])).
% 0.20/0.44  fof(f8,axiom,(
% 0.20/0.44    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tsep_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v3_pre_topc(X2,X0))))))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tsep_1)).
% 0.20/0.44  fof(f60,plain,(
% 0.20/0.44    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f23])).
% 0.20/0.44  fof(f23,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.44    inference(ennf_transformation,[],[f12])).
% 0.20/0.44  fof(f12,axiom,(
% 0.20/0.44    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.20/0.44  fof(f138,plain,(
% 0.20/0.44    ~v3_pre_topc(u1_struct_0(sK1),sK0) | spl3_12),
% 0.20/0.44    inference(avatar_component_clause,[],[f137])).
% 0.20/0.44  fof(f510,plain,(
% 0.20/0.44    ~spl3_5 | spl3_68 | ~spl3_3 | ~spl3_23 | ~spl3_33 | ~spl3_66),
% 0.20/0.44    inference(avatar_split_clause,[],[f506,f494,f265,f203,f84,f508,f98])).
% 0.20/0.44  fof(f84,plain,(
% 0.20/0.44    spl3_3 <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.44  fof(f506,plain,(
% 0.20/0.44    k8_tmap_1(sK0,sK1) = k8_tmap_1(sK0,sK0) | ~l1_pre_topc(sK0) | (~spl3_3 | ~spl3_23 | ~spl3_33 | ~spl3_66)),
% 0.20/0.44    inference(forward_demodulation,[],[f505,f88])).
% 0.20/0.44  fof(f88,plain,(
% 0.20/0.44    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) | ~spl3_3),
% 0.20/0.44    inference(avatar_component_clause,[],[f84])).
% 0.20/0.44  fof(f503,plain,(
% 0.20/0.44    spl3_67 | ~spl3_2 | ~spl3_17 | ~spl3_66),
% 0.20/0.44    inference(avatar_split_clause,[],[f499,f494,f165,f81,f501])).
% 0.20/0.44  fof(f501,plain,(
% 0.20/0.44    spl3_67 <=> k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k8_tmap_1(sK0,sK1)))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_67])])).
% 0.20/0.44  fof(f165,plain,(
% 0.20/0.44    spl3_17 <=> u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.44  fof(f499,plain,(
% 0.20/0.44    k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k8_tmap_1(sK0,sK1))) | (~spl3_2 | ~spl3_17 | ~spl3_66)),
% 0.20/0.44    inference(forward_demodulation,[],[f497,f166])).
% 0.20/0.44  fof(f166,plain,(
% 0.20/0.44    u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) | ~spl3_17),
% 0.20/0.44    inference(avatar_component_clause,[],[f165])).
% 0.20/0.44  fof(f497,plain,(
% 0.20/0.44    k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK1)),u1_pre_topc(k8_tmap_1(sK0,sK1))) | (~spl3_2 | ~spl3_66)),
% 0.20/0.44    inference(resolution,[],[f495,f87])).
% 0.20/0.44  fof(f87,plain,(
% 0.20/0.44    m1_pre_topc(sK1,sK0) | ~spl3_2),
% 0.20/0.44    inference(avatar_component_clause,[],[f81])).
% 0.20/0.44  fof(f496,plain,(
% 0.20/0.44    spl3_66 | ~spl3_5 | ~spl3_6 | spl3_7),
% 0.20/0.44    inference(avatar_split_clause,[],[f492,f106,f102,f98,f494])).
% 0.20/0.44  fof(f102,plain,(
% 0.20/0.44    spl3_6 <=> v2_pre_topc(sK0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.44  fof(f106,plain,(
% 0.20/0.44    spl3_7 <=> v2_struct_0(sK0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.44  fof(f492,plain,(
% 0.20/0.44    ( ! [X1] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | k8_tmap_1(sK0,X1) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,X1)),u1_pre_topc(k8_tmap_1(sK0,X1))) | ~m1_pre_topc(X1,sK0)) ) | spl3_7),
% 0.20/0.44    inference(resolution,[],[f448,f107])).
% 0.20/0.44  fof(f107,plain,(
% 0.20/0.44    ~v2_struct_0(sK0) | spl3_7),
% 0.20/0.44    inference(avatar_component_clause,[],[f106])).
% 0.20/0.44  fof(f448,plain,(
% 0.20/0.44    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | k8_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(k8_tmap_1(X0,X1)),u1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0)) )),
% 0.20/0.44    inference(duplicate_literal_removal,[],[f447])).
% 0.20/0.44  fof(f447,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | k8_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(k8_tmap_1(X0,X1)),u1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.44    inference(resolution,[],[f128,f74])).
% 0.20/0.44  fof(f74,plain,(
% 0.20/0.44    ( ! [X0,X1] : (l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f34])).
% 0.20/0.44  fof(f34,plain,(
% 0.20/0.44    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.44    inference(flattening,[],[f33])).
% 0.20/0.44  fof(f33,plain,(
% 0.20/0.44    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f9])).
% 0.20/0.44  fof(f9,axiom,(
% 0.20/0.44    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_tmap_1)).
% 0.20/0.44  fof(f128,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~l1_pre_topc(k8_tmap_1(X1,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | k8_tmap_1(X1,X0) = g1_pre_topc(u1_struct_0(k8_tmap_1(X1,X0)),u1_pre_topc(k8_tmap_1(X1,X0))) | ~m1_pre_topc(X0,X1)) )),
% 0.20/0.44    inference(resolution,[],[f72,f59])).
% 0.20/0.44  fof(f59,plain,(
% 0.20/0.44    ( ! [X0] : (~v1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~l1_pre_topc(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f22])).
% 0.20/0.44  fof(f22,plain,(
% 0.20/0.44    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 0.20/0.44    inference(flattening,[],[f21])).
% 0.20/0.44  fof(f21,plain,(
% 0.20/0.44    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 0.20/0.44    inference(ennf_transformation,[],[f3])).
% 0.20/0.44  fof(f3,axiom,(
% 0.20/0.44    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 0.20/0.44  fof(f72,plain,(
% 0.20/0.44    ( ! [X0,X1] : (v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f34])).
% 0.20/0.44  fof(f362,plain,(
% 0.20/0.44    spl3_7 | ~spl3_6 | ~spl3_5 | spl3_49 | ~spl3_36),
% 0.20/0.44    inference(avatar_split_clause,[],[f356,f285,f360,f98,f102,f106])).
% 0.20/0.45  fof(f285,plain,(
% 0.20/0.45    spl3_36 <=> ! [X1] : (u1_pre_topc(sK0) != k5_tmap_1(sK0,X1) | r2_hidden(X1,u1_pre_topc(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.20/0.45  fof(f356,plain,(
% 0.20/0.45    ( ! [X1] : (u1_pre_topc(sK0) != u1_pre_topc(k8_tmap_1(sK0,X1)) | r2_hidden(u1_struct_0(X1),u1_pre_topc(sK0)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl3_36),
% 0.20/0.45    inference(superposition,[],[f286,f111])).
% 0.20/0.45  fof(f111,plain,(
% 0.20/0.45    ( ! [X0,X1] : (u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.45    inference(global_subsumption,[],[f60,f76])).
% 0.20/0.45  fof(f76,plain,(
% 0.20/0.45    ( ! [X0,X1] : (u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.45    inference(equality_resolution,[],[f70])).
% 0.20/0.45  fof(f70,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f30])).
% 0.20/0.45  fof(f30,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : ((! [X2] : (u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.45    inference(flattening,[],[f29])).
% 0.20/0.45  fof(f29,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : ((! [X2] : ((u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f11])).
% 0.20/0.45  fof(f11,axiom,(
% 0.20/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_tmap_1)).
% 0.20/0.45  fof(f286,plain,(
% 0.20/0.45    ( ! [X1] : (u1_pre_topc(sK0) != k5_tmap_1(sK0,X1) | r2_hidden(X1,u1_pre_topc(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_36),
% 0.20/0.45    inference(avatar_component_clause,[],[f285])).
% 0.20/0.45  fof(f345,plain,(
% 0.20/0.45    ~spl3_5 | ~spl3_2 | spl3_44),
% 0.20/0.45    inference(avatar_split_clause,[],[f340,f333,f81,f98])).
% 0.20/0.45  fof(f340,plain,(
% 0.20/0.45    ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | spl3_44),
% 0.20/0.45    inference(resolution,[],[f334,f60])).
% 0.20/0.45  fof(f334,plain,(
% 0.20/0.45    ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_44),
% 0.20/0.45    inference(avatar_component_clause,[],[f333])).
% 0.20/0.45  fof(f287,plain,(
% 0.20/0.45    ~spl3_6 | ~spl3_5 | spl3_36 | spl3_7),
% 0.20/0.45    inference(avatar_split_clause,[],[f283,f106,f285,f98,f102])).
% 0.20/0.45  fof(f283,plain,(
% 0.20/0.45    ( ! [X1] : (u1_pre_topc(sK0) != k5_tmap_1(sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | r2_hidden(X1,u1_pre_topc(sK0))) ) | spl3_7),
% 0.20/0.45    inference(resolution,[],[f68,f107])).
% 0.20/0.45  fof(f68,plain,(
% 0.20/0.45    ( ! [X0,X1] : (v2_struct_0(X0) | u1_pre_topc(X0) != k5_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | r2_hidden(X1,u1_pre_topc(X0))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f45])).
% 0.20/0.45  fof(f45,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (((r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) != k5_tmap_1(X0,X1)) & (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.45    inference(nnf_transformation,[],[f28])).
% 0.20/0.45  fof(f28,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.45    inference(flattening,[],[f27])).
% 0.20/0.45  fof(f27,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f10])).
% 0.20/0.45  fof(f10,axiom,(
% 0.20/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).
% 0.20/0.45  fof(f272,plain,(
% 0.20/0.45    spl3_32),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f271])).
% 0.20/0.45  fof(f271,plain,(
% 0.20/0.45    $false | spl3_32),
% 0.20/0.45    inference(resolution,[],[f263,f109])).
% 0.20/0.45  fof(f109,plain,(
% 0.20/0.45    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.20/0.45    inference(forward_demodulation,[],[f55,f54])).
% 0.20/0.45  fof(f54,plain,(
% 0.20/0.45    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.45    inference(cnf_transformation,[],[f1])).
% 0.20/0.45  fof(f1,axiom,(
% 0.20/0.45    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.45  fof(f55,plain,(
% 0.20/0.45    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.20/0.45  fof(f263,plain,(
% 0.20/0.45    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_32),
% 0.20/0.45    inference(avatar_component_clause,[],[f262])).
% 0.20/0.45  fof(f262,plain,(
% 0.20/0.45    spl3_32 <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.20/0.45  fof(f267,plain,(
% 0.20/0.45    ~spl3_10 | ~spl3_32 | ~spl3_29 | spl3_33 | spl3_7 | ~spl3_31),
% 0.20/0.45    inference(avatar_split_clause,[],[f259,f254,f106,f265,f233,f262,f123])).
% 0.20/0.45  fof(f123,plain,(
% 0.20/0.45    spl3_10 <=> v3_pre_topc(u1_struct_0(sK0),sK0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.45  fof(f233,plain,(
% 0.20/0.45    spl3_29 <=> m1_pre_topc(sK0,sK0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.20/0.45  fof(f259,plain,(
% 0.20/0.45    u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK0)) | ~m1_pre_topc(sK0,sK0) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(u1_struct_0(sK0),sK0) | (spl3_7 | ~spl3_31)),
% 0.20/0.45    inference(resolution,[],[f255,f107])).
% 0.20/0.45  fof(f257,plain,(
% 0.20/0.45    spl3_7 | ~spl3_6 | ~spl3_5 | spl3_31 | ~spl3_30),
% 0.20/0.45    inference(avatar_split_clause,[],[f252,f248,f254,f98,f102,f106])).
% 0.20/0.45  fof(f248,plain,(
% 0.20/0.45    spl3_30 <=> ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X1,sK0) | u1_pre_topc(sK0) = k5_tmap_1(sK0,X1))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.20/0.45  fof(f252,plain,(
% 0.20/0.45    ( ! [X0] : (u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,X0)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~v3_pre_topc(u1_struct_0(X0),sK0) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_30),
% 0.20/0.45    inference(superposition,[],[f111,f249])).
% 0.20/0.45  fof(f249,plain,(
% 0.20/0.45    ( ! [X1] : (u1_pre_topc(sK0) = k5_tmap_1(sK0,X1) | ~v3_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_30),
% 0.20/0.45    inference(avatar_component_clause,[],[f248])).
% 0.20/0.45  fof(f250,plain,(
% 0.20/0.45    ~spl3_6 | ~spl3_5 | spl3_30 | spl3_7),
% 0.20/0.45    inference(avatar_split_clause,[],[f246,f106,f248,f98,f102])).
% 0.20/0.45  fof(f246,plain,(
% 0.20/0.45    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | u1_pre_topc(sK0) = k5_tmap_1(sK0,X1) | ~v3_pre_topc(X1,sK0)) ) | spl3_7),
% 0.20/0.45    inference(resolution,[],[f237,f107])).
% 0.20/0.45  fof(f237,plain,(
% 0.20/0.45    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) )),
% 0.20/0.45    inference(duplicate_literal_removal,[],[f236])).
% 0.20/0.45  fof(f236,plain,(
% 0.20/0.45    ( ! [X0,X1] : (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.45    inference(resolution,[],[f67,f65])).
% 0.20/0.45  fof(f65,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f44])).
% 0.20/0.45  fof(f67,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f45])).
% 0.20/0.45  fof(f239,plain,(
% 0.20/0.45    ~spl3_5 | spl3_29),
% 0.20/0.45    inference(avatar_split_clause,[],[f238,f233,f98])).
% 0.20/0.45  fof(f238,plain,(
% 0.20/0.45    ~l1_pre_topc(sK0) | spl3_29),
% 0.20/0.45    inference(resolution,[],[f234,f58])).
% 0.20/0.45  fof(f234,plain,(
% 0.20/0.45    ~m1_pre_topc(sK0,sK0) | spl3_29),
% 0.20/0.45    inference(avatar_component_clause,[],[f233])).
% 0.20/0.45  fof(f205,plain,(
% 0.20/0.45    ~spl3_6 | ~spl3_5 | spl3_23 | spl3_7),
% 0.20/0.45    inference(avatar_split_clause,[],[f201,f106,f203,f98,f102])).
% 0.20/0.45  fof(f201,plain,(
% 0.20/0.45    u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | spl3_7),
% 0.20/0.45    inference(resolution,[],[f147,f107])).
% 0.20/0.45  fof(f147,plain,(
% 0.20/0.45    ( ! [X0] : (v2_struct_0(X0) | u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.45    inference(global_subsumption,[],[f58,f146])).
% 0.20/0.45  fof(f146,plain,(
% 0.20/0.45    ( ! [X0] : (v2_struct_0(X0) | ~m1_pre_topc(X0,X0) | u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.45    inference(factoring,[],[f69])).
% 0.20/0.45  fof(f69,plain,(
% 0.20/0.45    ( ! [X0,X1] : (v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f30])).
% 0.20/0.45  fof(f167,plain,(
% 0.20/0.45    ~spl3_2 | ~spl3_6 | ~spl3_5 | spl3_17 | spl3_4 | spl3_7),
% 0.20/0.45    inference(avatar_split_clause,[],[f149,f106,f94,f165,f98,f102,f81])).
% 0.20/0.45  fof(f149,plain,(
% 0.20/0.45    u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | (spl3_4 | spl3_7)),
% 0.20/0.45    inference(resolution,[],[f144,f107])).
% 0.20/0.45  fof(f144,plain,(
% 0.20/0.45    ( ! [X0] : (v2_struct_0(X0) | u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,sK1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(sK1,X0)) ) | spl3_4),
% 0.20/0.45    inference(resolution,[],[f69,f95])).
% 0.20/0.45  fof(f139,plain,(
% 0.20/0.45    ~spl3_5 | ~spl3_2 | spl3_1 | ~spl3_12 | ~spl3_11),
% 0.20/0.45    inference(avatar_split_clause,[],[f135,f132,f137,f78,f81,f98])).
% 0.20/0.45  fof(f132,plain,(
% 0.20/0.45    spl3_11 <=> u1_struct_0(sK1) = sK2(sK0,sK1)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.45  fof(f135,plain,(
% 0.20/0.45    ~v3_pre_topc(u1_struct_0(sK1),sK0) | v1_tsep_1(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~spl3_11),
% 0.20/0.45    inference(superposition,[],[f64,f133])).
% 0.20/0.45  fof(f133,plain,(
% 0.20/0.45    u1_struct_0(sK1) = sK2(sK0,sK1) | ~spl3_11),
% 0.20/0.45    inference(avatar_component_clause,[],[f132])).
% 0.20/0.45  fof(f64,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~v3_pre_topc(sK2(X0,X1),X0) | v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f43])).
% 0.20/0.45  fof(f134,plain,(
% 0.20/0.45    ~spl3_5 | ~spl3_2 | spl3_11 | spl3_1),
% 0.20/0.45    inference(avatar_split_clause,[],[f130,f78,f132,f81,f98])).
% 0.20/0.45  fof(f130,plain,(
% 0.20/0.45    u1_struct_0(sK1) = sK2(sK0,sK1) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | spl3_1),
% 0.20/0.45    inference(resolution,[],[f63,f79])).
% 0.20/0.45  fof(f79,plain,(
% 0.20/0.45    ~v1_tsep_1(sK1,sK0) | spl3_1),
% 0.20/0.45    inference(avatar_component_clause,[],[f78])).
% 0.20/0.45  fof(f63,plain,(
% 0.20/0.45    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | u1_struct_0(X1) = sK2(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f43])).
% 0.20/0.45  fof(f127,plain,(
% 0.20/0.45    ~spl3_5 | spl3_9),
% 0.20/0.45    inference(avatar_split_clause,[],[f126,f120,f98])).
% 0.20/0.45  fof(f120,plain,(
% 0.20/0.45    spl3_9 <=> l1_struct_0(sK0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.45  fof(f126,plain,(
% 0.20/0.45    ~l1_pre_topc(sK0) | spl3_9),
% 0.20/0.45    inference(resolution,[],[f121,f57])).
% 0.20/0.45  fof(f57,plain,(
% 0.20/0.45    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f19])).
% 0.20/0.45  fof(f19,plain,(
% 0.20/0.45    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f6])).
% 0.20/0.45  fof(f6,axiom,(
% 0.20/0.45    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.45  fof(f121,plain,(
% 0.20/0.45    ~l1_struct_0(sK0) | spl3_9),
% 0.20/0.45    inference(avatar_component_clause,[],[f120])).
% 0.20/0.45  fof(f125,plain,(
% 0.20/0.45    ~spl3_9 | spl3_10 | ~spl3_8),
% 0.20/0.45    inference(avatar_split_clause,[],[f118,f114,f123,f120])).
% 0.20/0.45  fof(f114,plain,(
% 0.20/0.45    spl3_8 <=> v3_pre_topc(k2_struct_0(sK0),sK0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.45  fof(f118,plain,(
% 0.20/0.45    v3_pre_topc(u1_struct_0(sK0),sK0) | ~l1_struct_0(sK0) | ~spl3_8),
% 0.20/0.45    inference(superposition,[],[f115,f56])).
% 0.20/0.45  fof(f56,plain,(
% 0.20/0.45    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f18])).
% 0.20/0.45  fof(f18,plain,(
% 0.20/0.45    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f4])).
% 0.20/0.45  fof(f4,axiom,(
% 0.20/0.45    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.45  fof(f115,plain,(
% 0.20/0.45    v3_pre_topc(k2_struct_0(sK0),sK0) | ~spl3_8),
% 0.20/0.45    inference(avatar_component_clause,[],[f114])).
% 0.20/0.45  fof(f117,plain,(
% 0.20/0.45    spl3_8 | ~spl3_5 | ~spl3_6),
% 0.20/0.45    inference(avatar_split_clause,[],[f112,f102,f98,f114])).
% 0.20/0.45  fof(f112,plain,(
% 0.20/0.45    ~l1_pre_topc(sK0) | v3_pre_topc(k2_struct_0(sK0),sK0) | ~spl3_6),
% 0.20/0.45    inference(resolution,[],[f71,f103])).
% 0.20/0.45  fof(f103,plain,(
% 0.20/0.45    v2_pre_topc(sK0) | ~spl3_6),
% 0.20/0.45    inference(avatar_component_clause,[],[f102])).
% 0.20/0.45  fof(f71,plain,(
% 0.20/0.45    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v3_pre_topc(k2_struct_0(X0),X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f32])).
% 0.20/0.45  fof(f32,plain,(
% 0.20/0.45    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.45    inference(flattening,[],[f31])).
% 0.20/0.45  fof(f31,plain,(
% 0.20/0.45    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f7])).
% 0.20/0.45  fof(f7,axiom,(
% 0.20/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).
% 0.20/0.45  fof(f108,plain,(
% 0.20/0.45    ~spl3_7),
% 0.20/0.45    inference(avatar_split_clause,[],[f46,f106])).
% 0.20/0.45  fof(f46,plain,(
% 0.20/0.45    ~v2_struct_0(sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f39])).
% 0.20/0.45  fof(f39,plain,(
% 0.20/0.45    ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1) | ~m1_pre_topc(sK1,sK0) | ~v1_tsep_1(sK1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) | (m1_pre_topc(sK1,sK0) & v1_tsep_1(sK1,sK0))) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f38,f37])).
% 0.20/0.45  fof(f37,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,X1) | ~m1_pre_topc(X1,sK0) | ~v1_tsep_1(X1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,X1) | (m1_pre_topc(X1,sK0) & v1_tsep_1(X1,sK0))) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f38,plain,(
% 0.20/0.45    ? [X1] : ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,X1) | ~m1_pre_topc(X1,sK0) | ~v1_tsep_1(X1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,X1) | (m1_pre_topc(X1,sK0) & v1_tsep_1(X1,sK0))) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1) | ~m1_pre_topc(sK1,sK0) | ~v1_tsep_1(sK1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) | (m1_pre_topc(sK1,sK0) & v1_tsep_1(sK1,sK0))) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f36,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.45    inference(flattening,[],[f35])).
% 0.20/0.45  fof(f35,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : (((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.45    inference(nnf_transformation,[],[f17])).
% 0.20/0.45  fof(f17,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.45    inference(flattening,[],[f16])).
% 0.20/0.45  fof(f16,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f15])).
% 0.20/0.45  fof(f15,negated_conjecture,(
% 0.20/0.45    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1))))),
% 0.20/0.45    inference(negated_conjecture,[],[f14])).
% 0.20/0.45  fof(f14,conjecture,(
% 0.20/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_tmap_1)).
% 0.20/0.45  fof(f104,plain,(
% 0.20/0.45    spl3_6),
% 0.20/0.45    inference(avatar_split_clause,[],[f47,f102])).
% 0.20/0.45  fof(f47,plain,(
% 0.20/0.45    v2_pre_topc(sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f39])).
% 0.20/0.45  fof(f100,plain,(
% 0.20/0.45    spl3_5),
% 0.20/0.45    inference(avatar_split_clause,[],[f48,f98])).
% 0.20/0.45  fof(f48,plain,(
% 0.20/0.45    l1_pre_topc(sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f39])).
% 0.20/0.45  fof(f96,plain,(
% 0.20/0.45    ~spl3_4),
% 0.20/0.45    inference(avatar_split_clause,[],[f49,f94])).
% 0.20/0.45  fof(f49,plain,(
% 0.20/0.45    ~v2_struct_0(sK1)),
% 0.20/0.45    inference(cnf_transformation,[],[f39])).
% 0.20/0.45  fof(f92,plain,(
% 0.20/0.45    spl3_2),
% 0.20/0.45    inference(avatar_split_clause,[],[f50,f81])).
% 0.20/0.45  fof(f50,plain,(
% 0.20/0.45    m1_pre_topc(sK1,sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f39])).
% 0.20/0.45  fof(f91,plain,(
% 0.20/0.45    spl3_1 | spl3_3),
% 0.20/0.45    inference(avatar_split_clause,[],[f51,f84,f78])).
% 0.20/0.45  fof(f51,plain,(
% 0.20/0.45    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) | v1_tsep_1(sK1,sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f39])).
% 0.20/0.45  fof(f86,plain,(
% 0.20/0.45    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 0.20/0.45    inference(avatar_split_clause,[],[f53,f84,f81,f78])).
% 0.20/0.45  fof(f53,plain,(
% 0.20/0.45    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1) | ~m1_pre_topc(sK1,sK0) | ~v1_tsep_1(sK1,sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f39])).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (11017)------------------------------
% 0.20/0.45  % (11017)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (11017)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (11017)Memory used [KB]: 11001
% 0.20/0.45  % (11017)Time elapsed: 0.023 s
% 0.20/0.45  % (11017)------------------------------
% 0.20/0.45  % (11017)------------------------------
% 0.20/0.45  % (11010)Success in time 0.094 s
%------------------------------------------------------------------------------
