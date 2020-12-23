%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1337+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 380 expanded)
%              Number of leaves         :   42 ( 180 expanded)
%              Depth                    :   13
%              Number of atoms          :  834 (2806 expanded)
%              Number of equality atoms :   70 ( 329 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f577,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f92,f96,f100,f104,f108,f112,f116,f120,f124,f128,f144,f161,f170,f211,f248,f250,f537,f542,f552,f559,f566,f571,f576])).

fof(f576,plain,
    ( ~ spl10_11
    | spl10_1
    | ~ spl10_3
    | ~ spl10_55 ),
    inference(avatar_split_clause,[],[f573,f569,f94,f86,f126])).

fof(f126,plain,
    ( spl10_11
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f86,plain,
    ( spl10_1
  <=> v2_tops_2(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f94,plain,
    ( spl10_3
  <=> m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f569,plain,
    ( spl10_55
  <=> ! [X0] :
        ( ~ r2_hidden(sK6(sK0,X0),sK4)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_55])])).

fof(f573,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v2_tops_2(sK4,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_55 ),
    inference(duplicate_literal_removal,[],[f572])).

fof(f572,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v2_tops_2(sK4,sK0)
    | v2_tops_2(sK4,sK0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ spl10_55 ),
    inference(resolution,[],[f570,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X1)
      | v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ( ~ v4_pre_topc(sK6(X0,X1),X0)
                & r2_hidden(sK6(X0,X1),X1)
                & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v4_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f38,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v4_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK6(X0,X1),X0)
        & r2_hidden(sK6(X0,X1),X1)
        & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v4_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v4_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v4_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v4_pre_topc(X2,X0)
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v4_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_2)).

fof(f570,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK6(sK0,X0),sK4)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X0,sK0) )
    | ~ spl10_55 ),
    inference(avatar_component_clause,[],[f569])).

fof(f571,plain,
    ( ~ spl10_11
    | spl10_55
    | ~ spl10_54 ),
    inference(avatar_split_clause,[],[f567,f564,f569,f126])).

fof(f564,plain,
    ( spl10_54
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK4)
        | v4_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_54])])).

fof(f567,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK6(sK0,X0),sK4)
        | v2_tops_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ l1_pre_topc(sK0) )
    | ~ spl10_54 ),
    inference(resolution,[],[f565,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(sK6(X0,X1),X0)
      | v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f565,plain,
    ( ! [X0] :
        ( v4_pre_topc(X0,sK0)
        | ~ r2_hidden(X0,sK4) )
    | ~ spl10_54 ),
    inference(avatar_component_clause,[],[f564])).

fof(f566,plain,
    ( ~ spl10_6
    | ~ spl10_22
    | ~ spl10_23
    | spl10_54
    | ~ spl10_2
    | ~ spl10_53 ),
    inference(avatar_split_clause,[],[f562,f557,f90,f564,f236,f233,f106])).

fof(f106,plain,
    ( spl10_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f233,plain,
    ( spl10_22
  <=> v1_relat_1(k3_funct_3(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f236,plain,
    ( spl10_23
  <=> v1_funct_1(k3_funct_3(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).

fof(f90,plain,
    ( spl10_2
  <=> k9_relat_1(k3_funct_3(sK2),sK3) = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f557,plain,
    ( spl10_53
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK4)
        | v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(sK9(k3_funct_3(sK2),sK3,X0),k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_53])])).

fof(f562,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK4)
        | v4_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_funct_3(sK2))
        | ~ v1_relat_1(k3_funct_3(sK2))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
    | ~ spl10_2
    | ~ spl10_53 ),
    inference(duplicate_literal_removal,[],[f561])).

fof(f561,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK4)
        | v4_pre_topc(X0,sK0)
        | ~ r2_hidden(X0,sK4)
        | ~ v1_funct_1(k3_funct_3(sK2))
        | ~ v1_relat_1(k3_funct_3(sK2))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
    | ~ spl10_2
    | ~ spl10_53 ),
    inference(forward_demodulation,[],[f560,f91])).

fof(f91,plain,
    ( k9_relat_1(k3_funct_3(sK2),sK3) = sK4
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f560,plain,
    ( ! [X0] :
        ( v4_pre_topc(X0,sK0)
        | ~ r2_hidden(X0,sK4)
        | ~ v1_funct_1(k3_funct_3(sK2))
        | ~ v1_relat_1(k3_funct_3(sK2))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
        | ~ r2_hidden(X0,k9_relat_1(k3_funct_3(sK2),sK3)) )
    | ~ spl10_53 ),
    inference(resolution,[],[f558,f129])).

fof(f129,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK9(X1,X2,X0),X3)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
      | ~ r2_hidden(X0,k9_relat_1(X1,X2)) ) ),
    inference(resolution,[],[f83,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f83,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( k1_funct_1(X0,X4) != sK7(X0,X1,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                | ~ r2_hidden(sK7(X0,X1,X2),X2) )
              & ( ( sK7(X0,X1,X2) = k1_funct_1(X0,sK8(X0,X1,X2))
                  & r2_hidden(sK8(X0,X1,X2),X1)
                  & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK9(X0,X1,X6)) = X6
                    & r2_hidden(sK9(X0,X1,X6),X1)
                    & r2_hidden(sK9(X0,X1,X6),k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f42,f45,f44,f43])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( k1_funct_1(X0,X4) != X3
                | ~ r2_hidden(X4,X1)
                | ~ r2_hidden(X4,k1_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( k1_funct_1(X0,X5) = X3
                & r2_hidden(X5,X1)
                & r2_hidden(X5,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( k1_funct_1(X0,X4) != sK7(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK7(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = sK7(X0,X1,X2)
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( sK7(X0,X1,X2) = k1_funct_1(X0,sK8(X0,X1,X2))
        & r2_hidden(sK8(X0,X1,X2),X1)
        & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK9(X0,X1,X6)) = X6
        & r2_hidden(sK9(X0,X1,X6),X1)
        & r2_hidden(sK9(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( k1_funct_1(X0,X5) = X3
                      & r2_hidden(X5,X1)
                      & r2_hidden(X5,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ? [X8] :
                      ( k1_funct_1(X0,X8) = X6
                      & r2_hidden(X8,X1)
                      & r2_hidden(X8,k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) ) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).

fof(f558,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK9(k3_funct_3(sK2),sK3,X0),k1_zfmisc_1(u1_struct_0(sK1)))
        | v4_pre_topc(X0,sK0)
        | ~ r2_hidden(X0,sK4) )
    | ~ spl10_53 ),
    inference(avatar_component_clause,[],[f557])).

fof(f559,plain,
    ( ~ spl10_22
    | ~ spl10_23
    | spl10_53
    | ~ spl10_2
    | ~ spl10_52 ),
    inference(avatar_split_clause,[],[f555,f550,f90,f557,f236,f233])).

fof(f550,plain,
    ( spl10_52
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK4)
        | ~ m1_subset_1(sK9(k3_funct_3(sK2),sK3,X0),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ r2_hidden(sK9(k3_funct_3(sK2),sK3,X0),k1_relat_1(k3_funct_3(sK2)))
        | v4_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_52])])).

fof(f555,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK4)
        | ~ m1_subset_1(sK9(k3_funct_3(sK2),sK3,X0),k1_zfmisc_1(u1_struct_0(sK1)))
        | v4_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_funct_3(sK2))
        | ~ v1_relat_1(k3_funct_3(sK2)) )
    | ~ spl10_2
    | ~ spl10_52 ),
    inference(duplicate_literal_removal,[],[f554])).

fof(f554,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK4)
        | ~ m1_subset_1(sK9(k3_funct_3(sK2),sK3,X0),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ r2_hidden(X0,sK4)
        | v4_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_funct_3(sK2))
        | ~ v1_relat_1(k3_funct_3(sK2)) )
    | ~ spl10_2
    | ~ spl10_52 ),
    inference(forward_demodulation,[],[f553,f91])).

fof(f553,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK9(k3_funct_3(sK2),sK3,X0),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ r2_hidden(X0,sK4)
        | v4_pre_topc(X0,sK0)
        | ~ r2_hidden(X0,k9_relat_1(k3_funct_3(sK2),sK3))
        | ~ v1_funct_1(k3_funct_3(sK2))
        | ~ v1_relat_1(k3_funct_3(sK2)) )
    | ~ spl10_52 ),
    inference(resolution,[],[f551,f84])).

fof(f84,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f551,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK9(k3_funct_3(sK2),sK3,X0),k1_relat_1(k3_funct_3(sK2)))
        | ~ m1_subset_1(sK9(k3_funct_3(sK2),sK3,X0),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ r2_hidden(X0,sK4)
        | v4_pre_topc(X0,sK0) )
    | ~ spl10_52 ),
    inference(avatar_component_clause,[],[f550])).

fof(f552,plain,
    ( ~ spl10_22
    | ~ spl10_23
    | spl10_52
    | ~ spl10_2
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_51 ),
    inference(avatar_split_clause,[],[f548,f540,f209,f167,f90,f550,f236,f233])).

fof(f167,plain,
    ( spl10_16
  <=> ! [X3,X2] :
        ( k10_relat_1(sK2,sK9(k3_funct_3(sK2),X2,X3)) = X3
        | ~ r2_hidden(sK9(k3_funct_3(sK2),X2,X3),k1_relat_1(k3_funct_3(sK2)))
        | ~ r2_hidden(X3,k9_relat_1(k3_funct_3(sK2),X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f209,plain,
    ( spl10_20
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | v4_pre_topc(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f540,plain,
    ( spl10_51
  <=> ! [X0] :
        ( v4_pre_topc(k10_relat_1(sK2,X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v4_pre_topc(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_51])])).

fof(f548,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK4)
        | v4_pre_topc(X0,sK0)
        | ~ r2_hidden(sK9(k3_funct_3(sK2),sK3,X0),k1_relat_1(k3_funct_3(sK2)))
        | ~ m1_subset_1(sK9(k3_funct_3(sK2),sK3,X0),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v1_funct_1(k3_funct_3(sK2))
        | ~ v1_relat_1(k3_funct_3(sK2)) )
    | ~ spl10_2
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_51 ),
    inference(forward_demodulation,[],[f547,f91])).

fof(f547,plain,
    ( ! [X0] :
        ( v4_pre_topc(X0,sK0)
        | ~ r2_hidden(sK9(k3_funct_3(sK2),sK3,X0),k1_relat_1(k3_funct_3(sK2)))
        | ~ r2_hidden(X0,k9_relat_1(k3_funct_3(sK2),sK3))
        | ~ m1_subset_1(sK9(k3_funct_3(sK2),sK3,X0),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v1_funct_1(k3_funct_3(sK2))
        | ~ v1_relat_1(k3_funct_3(sK2)) )
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_51 ),
    inference(duplicate_literal_removal,[],[f546])).

fof(f546,plain,
    ( ! [X0] :
        ( v4_pre_topc(X0,sK0)
        | ~ r2_hidden(sK9(k3_funct_3(sK2),sK3,X0),k1_relat_1(k3_funct_3(sK2)))
        | ~ r2_hidden(X0,k9_relat_1(k3_funct_3(sK2),sK3))
        | ~ m1_subset_1(sK9(k3_funct_3(sK2),sK3,X0),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ r2_hidden(X0,k9_relat_1(k3_funct_3(sK2),sK3))
        | ~ v1_funct_1(k3_funct_3(sK2))
        | ~ v1_relat_1(k3_funct_3(sK2)) )
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_51 ),
    inference(resolution,[],[f545,f83])).

fof(f545,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK9(k3_funct_3(sK2),X0,X1),sK3)
        | v4_pre_topc(X1,sK0)
        | ~ r2_hidden(sK9(k3_funct_3(sK2),X0,X1),k1_relat_1(k3_funct_3(sK2)))
        | ~ r2_hidden(X1,k9_relat_1(k3_funct_3(sK2),X0))
        | ~ m1_subset_1(sK9(k3_funct_3(sK2),X0,X1),k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_51 ),
    inference(duplicate_literal_removal,[],[f544])).

fof(f544,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK9(k3_funct_3(sK2),X0,X1),k1_zfmisc_1(u1_struct_0(sK1)))
        | v4_pre_topc(X1,sK0)
        | ~ r2_hidden(sK9(k3_funct_3(sK2),X0,X1),k1_relat_1(k3_funct_3(sK2)))
        | ~ r2_hidden(X1,k9_relat_1(k3_funct_3(sK2),X0))
        | ~ r2_hidden(sK9(k3_funct_3(sK2),X0,X1),sK3)
        | ~ m1_subset_1(sK9(k3_funct_3(sK2),X0,X1),k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_51 ),
    inference(resolution,[],[f543,f210])).

fof(f210,plain,
    ( ! [X0] :
        ( v4_pre_topc(X0,sK1)
        | ~ r2_hidden(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl10_20 ),
    inference(avatar_component_clause,[],[f209])).

fof(f543,plain,
    ( ! [X0,X1] :
        ( ~ v4_pre_topc(sK9(k3_funct_3(sK2),X0,X1),sK1)
        | ~ m1_subset_1(sK9(k3_funct_3(sK2),X0,X1),k1_zfmisc_1(u1_struct_0(sK1)))
        | v4_pre_topc(X1,sK0)
        | ~ r2_hidden(sK9(k3_funct_3(sK2),X0,X1),k1_relat_1(k3_funct_3(sK2)))
        | ~ r2_hidden(X1,k9_relat_1(k3_funct_3(sK2),X0)) )
    | ~ spl10_16
    | ~ spl10_51 ),
    inference(superposition,[],[f541,f168])).

fof(f168,plain,
    ( ! [X2,X3] :
        ( k10_relat_1(sK2,sK9(k3_funct_3(sK2),X2,X3)) = X3
        | ~ r2_hidden(sK9(k3_funct_3(sK2),X2,X3),k1_relat_1(k3_funct_3(sK2)))
        | ~ r2_hidden(X3,k9_relat_1(k3_funct_3(sK2),X2)) )
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f167])).

fof(f541,plain,
    ( ! [X0] :
        ( v4_pre_topc(k10_relat_1(sK2,X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v4_pre_topc(X0,sK1) )
    | ~ spl10_51 ),
    inference(avatar_component_clause,[],[f540])).

fof(f542,plain,
    ( ~ spl10_7
    | spl10_51
    | ~ spl10_50 ),
    inference(avatar_split_clause,[],[f538,f535,f540,f110])).

fof(f110,plain,
    ( spl10_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f535,plain,
    ( spl10_50
  <=> ! [X0] :
        ( ~ v4_pre_topc(X0,sK1)
        | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_50])])).

fof(f538,plain,
    ( ! [X0] :
        ( v4_pre_topc(k10_relat_1(sK2,X0),sK0)
        | ~ v4_pre_topc(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) )
    | ~ spl10_50 ),
    inference(superposition,[],[f536,f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f536,plain,
    ( ! [X0] :
        ( v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0)
        | ~ v4_pre_topc(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl10_50 ),
    inference(avatar_component_clause,[],[f535])).

fof(f537,plain,
    ( ~ spl10_11
    | ~ spl10_10
    | ~ spl10_9
    | ~ spl10_7
    | ~ spl10_5
    | spl10_50
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f530,f114,f535,f102,f110,f118,f122,f126])).

fof(f122,plain,
    ( spl10_10
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f118,plain,
    ( spl10_9
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f102,plain,
    ( spl10_5
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f114,plain,
    ( spl10_8
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f530,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0)
        | ~ v1_funct_1(sK2)
        | ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(sK0) )
    | ~ spl10_8 ),
    inference(resolution,[],[f58,f115])).

fof(f115,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f114])).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v4_pre_topc(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK5(X0,X1,X2)),X0)
                    & v4_pre_topc(sK5(X0,X1,X2),X1)
                    & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v4_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f35])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v4_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK5(X0,X1,X2)),X0)
        & v4_pre_topc(sK5(X0,X1,X2),X1)
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v4_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v4_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v4_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      | ~ v4_pre_topc(X3,X1)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( v4_pre_topc(X3,X1)
                     => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_pre_topc)).

fof(f250,plain,
    ( ~ spl10_12
    | ~ spl10_9
    | spl10_23 ),
    inference(avatar_split_clause,[],[f249,f236,f118,f135])).

fof(f135,plain,
    ( spl10_12
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f249,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl10_23 ),
    inference(resolution,[],[f237,f67])).

% (29011)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% (29009)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% (29005)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% (29005)Refutation not found, incomplete strategy% (29005)------------------------------
% (29005)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (29005)Termination reason: Refutation not found, incomplete strategy

% (29005)Memory used [KB]: 10618
% (29005)Time elapsed: 0.081 s
% (29005)------------------------------
% (29005)------------------------------
% (29012)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% (29019)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% (29007)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% (29024)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% (29024)Refutation not found, incomplete strategy% (29024)------------------------------
% (29024)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (29024)Termination reason: Refutation not found, incomplete strategy

% (29024)Memory used [KB]: 10618
% (29024)Time elapsed: 0.054 s
% (29024)------------------------------
% (29024)------------------------------
% (29020)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% (29016)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% (29021)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% (29022)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% (29004)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% (29023)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% (29008)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% (29015)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
fof(f67,plain,(
    ! [X0] :
      ( v1_funct_1(k3_funct_3(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_funct_1(k3_funct_3(X0))
        & v1_relat_1(k3_funct_3(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_funct_1(k3_funct_3(X0))
        & v1_relat_1(k3_funct_3(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k3_funct_3(X0))
        & v1_relat_1(k3_funct_3(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_funct_3)).

fof(f237,plain,
    ( ~ v1_funct_1(k3_funct_3(sK2))
    | spl10_23 ),
    inference(avatar_component_clause,[],[f236])).

fof(f248,plain,
    ( ~ spl10_12
    | ~ spl10_9
    | spl10_22 ),
    inference(avatar_split_clause,[],[f246,f233,f118,f135])).

fof(f246,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl10_22 ),
    inference(resolution,[],[f234,f66])).

fof(f66,plain,(
    ! [X0] :
      ( v1_relat_1(k3_funct_3(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f234,plain,
    ( ~ v1_relat_1(k3_funct_3(sK2))
    | spl10_22 ),
    inference(avatar_component_clause,[],[f233])).

fof(f211,plain,
    ( ~ spl10_10
    | ~ spl10_6
    | spl10_20
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f205,f98,f209,f106,f122])).

fof(f98,plain,
    ( spl10_4
  <=> v2_tops_2(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f205,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | v4_pre_topc(X0,sK1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
        | ~ l1_pre_topc(sK1) )
    | ~ spl10_4 ),
    inference(resolution,[],[f62,f99])).

fof(f99,plain,
    ( v2_tops_2(sK3,sK1)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f98])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_tops_2(X1,X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f170,plain,
    ( ~ spl10_12
    | ~ spl10_9
    | spl10_16
    | ~ spl10_15 ),
    inference(avatar_split_clause,[],[f164,f159,f167,f118,f135])).

fof(f159,plain,
    ( spl10_15
  <=> ! [X1,X0] :
        ( k1_funct_1(k3_funct_3(sK2),sK9(k3_funct_3(sK2),X0,X1)) = X1
        | ~ r2_hidden(X1,k9_relat_1(k3_funct_3(sK2),X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f164,plain,
    ( ! [X0,X1] :
        ( k10_relat_1(sK2,sK9(k3_funct_3(sK2),X0,X1)) = X1
        | ~ r2_hidden(sK9(k3_funct_3(sK2),X0,X1),k1_relat_1(k3_funct_3(sK2)))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | ~ r2_hidden(X1,k9_relat_1(k3_funct_3(sK2),X0)) )
    | ~ spl10_15 ),
    inference(superposition,[],[f76,f160])).

fof(f160,plain,
    ( ! [X0,X1] :
        ( k1_funct_1(k3_funct_3(sK2),sK9(k3_funct_3(sK2),X0,X1)) = X1
        | ~ r2_hidden(X1,k9_relat_1(k3_funct_3(sK2),X0)) )
    | ~ spl10_15 ),
    inference(avatar_component_clause,[],[f159])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k3_funct_3(X1),X0) = k10_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(k3_funct_3(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k3_funct_3(X1),X0) = k10_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(k3_funct_3(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k3_funct_3(X1),X0) = k10_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(k3_funct_3(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(k3_funct_3(X1)))
       => k1_funct_1(k3_funct_3(X1),X0) = k10_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_3)).

fof(f161,plain,
    ( ~ spl10_12
    | spl10_15
    | ~ spl10_9 ),
    inference(avatar_split_clause,[],[f156,f118,f159,f135])).

fof(f156,plain,
    ( ! [X0,X1] :
        ( k1_funct_1(k3_funct_3(sK2),sK9(k3_funct_3(sK2),X0,X1)) = X1
        | ~ r2_hidden(X1,k9_relat_1(k3_funct_3(sK2),X0))
        | ~ v1_relat_1(sK2) )
    | ~ spl10_9 ),
    inference(resolution,[],[f141,f119])).

fof(f119,plain,
    ( v1_funct_1(sK2)
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f118])).

fof(f141,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_funct_1(X3)
      | k1_funct_1(k3_funct_3(X3),sK9(k3_funct_3(X3),X4,X2)) = X2
      | ~ r2_hidden(X2,k9_relat_1(k3_funct_3(X3),X4))
      | ~ v1_relat_1(X3) ) ),
    inference(global_subsumption,[],[f66,f133])).

fof(f133,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X2,k9_relat_1(k3_funct_3(X3),X4))
      | k1_funct_1(k3_funct_3(X3),sK9(k3_funct_3(X3),X4,X2)) = X2
      | ~ v1_relat_1(k3_funct_3(X3))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f82,f67])).

fof(f82,plain,(
    ! [X6,X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | k1_funct_1(X0,sK9(X0,X1,X6)) = X6
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_funct_1(X0,sK9(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f144,plain,
    ( ~ spl10_7
    | spl10_12 ),
    inference(avatar_contradiction_clause,[],[f143])).

fof(f143,plain,
    ( $false
    | ~ spl10_7
    | spl10_12 ),
    inference(subsumption_resolution,[],[f111,f142])).

fof(f142,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl10_12 ),
    inference(resolution,[],[f136,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f136,plain,
    ( ~ v1_relat_1(sK2)
    | spl10_12 ),
    inference(avatar_component_clause,[],[f135])).

fof(f111,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f110])).

fof(f128,plain,(
    spl10_11 ),
    inference(avatar_split_clause,[],[f47,f126])).

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ~ v2_tops_2(sK4,sK0)
    & k9_relat_1(k3_funct_3(sK2),sK3) = sK4
    & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & v2_tops_2(sK3,sK1)
    & v5_pre_topc(sK2,sK0,sK1)
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f12,f31,f30,f29,f28,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ~ v2_tops_2(X4,X0)
                        & k9_relat_1(k3_funct_3(X2),X3) = X4
                        & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                    & v2_tops_2(X3,X1)
                    & v5_pre_topc(X2,X0,X1)
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ v2_tops_2(X4,sK0)
                      & k9_relat_1(k3_funct_3(X2),X3) = X4
                      & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
                  & v2_tops_2(X3,X1)
                  & v5_pre_topc(X2,sK0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ~ v2_tops_2(X4,sK0)
                    & k9_relat_1(k3_funct_3(X2),X3) = X4
                    & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
                & v2_tops_2(X3,X1)
                & v5_pre_topc(X2,sK0,X1)
                & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ v2_tops_2(X4,sK0)
                  & k9_relat_1(k3_funct_3(X2),X3) = X4
                  & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
              & v2_tops_2(X3,sK1)
              & v5_pre_topc(X2,sK0,sK1)
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ~ v2_tops_2(X4,sK0)
                & k9_relat_1(k3_funct_3(X2),X3) = X4
                & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
            & v2_tops_2(X3,sK1)
            & v5_pre_topc(X2,sK0,sK1)
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ~ v2_tops_2(X4,sK0)
              & k9_relat_1(k3_funct_3(sK2),X3) = X4
              & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & v2_tops_2(X3,sK1)
          & v5_pre_topc(sK2,sK0,sK1)
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ~ v2_tops_2(X4,sK0)
            & k9_relat_1(k3_funct_3(sK2),X3) = X4
            & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
        & v2_tops_2(X3,sK1)
        & v5_pre_topc(sK2,sK0,sK1)
        & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
   => ( ? [X4] :
          ( ~ v2_tops_2(X4,sK0)
          & k9_relat_1(k3_funct_3(sK2),sK3) = X4
          & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & v2_tops_2(sK3,sK1)
      & v5_pre_topc(sK2,sK0,sK1)
      & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X4] :
        ( ~ v2_tops_2(X4,sK0)
        & k9_relat_1(k3_funct_3(sK2),sK3) = X4
        & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ~ v2_tops_2(sK4,sK0)
      & k9_relat_1(k3_funct_3(sK2),sK3) = sK4
      & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ v2_tops_2(X4,X0)
                      & k9_relat_1(k3_funct_3(X2),X3) = X4
                      & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                  & v2_tops_2(X3,X1)
                  & v5_pre_topc(X2,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ v2_tops_2(X4,X0)
                      & k9_relat_1(k3_funct_3(X2),X3) = X4
                      & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                  & v2_tops_2(X3,X1)
                  & v5_pre_topc(X2,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                   => ( ( v2_tops_2(X3,X1)
                        & v5_pre_topc(X2,X0,X1) )
                     => ! [X4] :
                          ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                         => ( k9_relat_1(k3_funct_3(X2),X3) = X4
                           => v2_tops_2(X4,X0) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                 => ( ( v2_tops_2(X3,X1)
                      & v5_pre_topc(X2,X0,X1) )
                   => ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                       => ( k9_relat_1(k3_funct_3(X2),X3) = X4
                         => v2_tops_2(X4,X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_tops_2)).

fof(f124,plain,(
    spl10_10 ),
    inference(avatar_split_clause,[],[f48,f122])).

fof(f48,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f120,plain,(
    spl10_9 ),
    inference(avatar_split_clause,[],[f49,f118])).

fof(f49,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f116,plain,(
    spl10_8 ),
    inference(avatar_split_clause,[],[f50,f114])).

fof(f50,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f112,plain,(
    spl10_7 ),
    inference(avatar_split_clause,[],[f51,f110])).

fof(f51,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f32])).

fof(f108,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f52,f106])).

fof(f52,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f32])).

fof(f104,plain,(
    spl10_5 ),
    inference(avatar_split_clause,[],[f53,f102])).

fof(f53,plain,(
    v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f100,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f54,f98])).

fof(f54,plain,(
    v2_tops_2(sK3,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f96,plain,(
    spl10_3 ),
    inference(avatar_split_clause,[],[f55,f94])).

fof(f55,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f32])).

fof(f92,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f56,f90])).

fof(f56,plain,(
    k9_relat_1(k3_funct_3(sK2),sK3) = sK4 ),
    inference(cnf_transformation,[],[f32])).

fof(f88,plain,(
    ~ spl10_1 ),
    inference(avatar_split_clause,[],[f57,f86])).

fof(f57,plain,(
    ~ v2_tops_2(sK4,sK0) ),
    inference(cnf_transformation,[],[f32])).

%------------------------------------------------------------------------------
