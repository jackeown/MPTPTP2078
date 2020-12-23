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
% DateTime   : Thu Dec  3 13:18:16 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 353 expanded)
%              Number of leaves         :   22 ( 145 expanded)
%              Depth                    :   31
%              Number of atoms          :  583 (3724 expanded)
%              Number of equality atoms :   50 ( 358 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f283,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f95,f105,f165,f277,f282])).

fof(f282,plain,(
    ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f281])).

fof(f281,plain,
    ( $false
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f280,f45])).

fof(f45,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))
    & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    & v1_funct_1(sK3)
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f40,f39,f38,f37])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2))
                    & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                & m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(sK0),u1_struct_0(X2),u1_struct_0(sK0),X3,k2_tmap_1(X1,sK0,X3,X2))
                  & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(sK0),u1_struct_0(X2),u1_struct_0(sK0),X3,k2_tmap_1(X1,sK0,X3,X2))
                & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0))
                & v1_funct_1(X3) )
            & m1_pre_topc(X2,X1)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(X2),u1_struct_0(sK0),X3,k2_tmap_1(sK1,sK0,X3,X2))
              & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
              & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0))
              & v1_funct_1(X3) )
          & m1_pre_topc(X2,sK1)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(X2),u1_struct_0(sK0),X3,k2_tmap_1(sK1,sK0,X3,X2))
            & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
            & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0))
            & v1_funct_1(X3) )
        & m1_pre_topc(X2,sK1)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),X3,k2_tmap_1(sK1,sK0,X3,sK2))
          & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
          & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0))
          & v1_funct_1(X3) )
      & m1_pre_topc(sK2,sK1)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X3] :
        ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),X3,k2_tmap_1(sK1,sK0,X3,sK2))
        & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0))
        & v1_funct_1(X3) )
   => ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))
      & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2))
                  & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2))
                  & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
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
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X1)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                      & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                      & v1_funct_1(X3) )
                   => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                     => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                 => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                   => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_tmap_1)).

fof(f280,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_8 ),
    inference(resolution,[],[f279,f57])).

fof(f57,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f279,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f278,f43])).

fof(f43,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f278,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_8 ),
    inference(resolution,[],[f160,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f160,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl4_8
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f277,plain,
    ( spl4_8
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f276,f162,f93,f158])).

fof(f93,plain,
    ( spl4_2
  <=> ! [X1,X0] :
        ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
        | u1_struct_0(sK2) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f162,plain,
    ( spl4_9
  <=> v1_partfun1(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f276,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f275,f51])).

fof(f51,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f41])).

% (29355)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
fof(f275,plain,
    ( ~ v1_funct_1(sK3)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f274,f52])).

fof(f52,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f274,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f273,f53])).

fof(f53,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f41])).

fof(f273,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(duplicate_literal_removal,[],[f272])).

fof(f272,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(condensation,[],[f271])).

fof(f271,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(sK3)
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(duplicate_literal_removal,[],[f269])).

fof(f269,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(sK3)
        | v1_xboole_0(u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(resolution,[],[f268,f72])).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => r1_funct_2(X0,X1,X2,X3,X4,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r1_funct_2)).

fof(f268,plain,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3)
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f267,f77])).

fof(f77,plain,(
    v4_relat_1(sK3,u1_struct_0(sK1)) ),
    inference(resolution,[],[f69,f53])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f267,plain,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3)
    | ~ v4_relat_1(sK3,u1_struct_0(sK1))
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f266,f164])).

fof(f164,plain,
    ( v1_partfun1(sK3,u1_struct_0(sK1))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f162])).

fof(f266,plain,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3)
    | ~ v1_partfun1(sK3,u1_struct_0(sK1))
    | ~ v4_relat_1(sK3,u1_struct_0(sK1))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f265,f76])).

fof(f76,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f68,f53])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f265,plain,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_partfun1(sK3,u1_struct_0(sK1))
    | ~ v4_relat_1(sK3,u1_struct_0(sK1))
    | ~ spl4_2 ),
    inference(superposition,[],[f263,f82])).

fof(f82,plain,(
    ! [X2,X3] :
      ( k7_relat_1(X2,X3) = X2
      | ~ v1_relat_1(X2)
      | ~ v1_partfun1(X2,X3)
      | ~ v4_relat_1(X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f81])).

fof(f81,plain,(
    ! [X2,X3] :
      ( k7_relat_1(X2,X3) = X2
      | ~ v1_relat_1(X2)
      | ~ v1_partfun1(X2,X3)
      | ~ v4_relat_1(X2,X3)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f56,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f56,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

% (29375)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
fof(f263,plain,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k7_relat_1(sK3,u1_struct_0(sK1)))
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f262,f107])).

fof(f107,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK2)
    | ~ spl4_2 ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
        | u1_struct_0(sK2) = X0 )
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f262,plain,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k7_relat_1(sK3,u1_struct_0(sK2)))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f261,f46])).

fof(f46,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f261,plain,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k7_relat_1(sK3,u1_struct_0(sK2)))
    | v2_struct_0(sK1)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f260,f47])).

fof(f47,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f260,plain,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k7_relat_1(sK3,u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f259,f48])).

fof(f48,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f259,plain,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k7_relat_1(sK3,u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f258,f43])).

fof(f258,plain,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k7_relat_1(sK3,u1_struct_0(sK2)))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f257,f44])).

fof(f44,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f257,plain,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k7_relat_1(sK3,u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f256,f45])).

fof(f256,plain,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k7_relat_1(sK3,u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f255,f52])).

fof(f255,plain,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k7_relat_1(sK3,u1_struct_0(sK2)))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f254,f50])).

fof(f50,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f254,plain,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k7_relat_1(sK3,u1_struct_0(sK2)))
    | ~ m1_pre_topc(sK2,sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f253,f51])).

fof(f253,plain,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k7_relat_1(sK3,u1_struct_0(sK2)))
    | ~ v1_funct_1(sK3)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f252,f53])).

fof(f252,plain,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k7_relat_1(sK3,u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK3)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_2 ),
    inference(superposition,[],[f110,f221])).

fof(f221,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tmap_1(X0,X1,X2,X3) = k7_relat_1(X2,u1_struct_0(X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f220])).

fof(f220,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tmap_1(X0,X1,X2,X3) = k7_relat_1(X2,u1_struct_0(X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f71,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

% (29370)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f110,plain,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f55,f107])).

fof(f55,plain,(
    ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f41])).

fof(f165,plain,
    ( spl4_8
    | spl4_9 ),
    inference(avatar_split_clause,[],[f156,f162,f158])).

fof(f156,plain,
    ( v1_partfun1(sK3,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f155,f51])).

fof(f155,plain,
    ( ~ v1_funct_1(sK3)
    | v1_partfun1(sK3,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f154,f52])).

fof(f154,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3)
    | v1_partfun1(sK3,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f63,f53])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_partfun1(X2,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f105,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f104])).

fof(f104,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f103,f75])).

fof(f75,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f74,f48])).

fof(f74,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f59,f50])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f103,plain,
    ( ~ l1_pre_topc(sK2)
    | spl4_1 ),
    inference(resolution,[],[f91,f58])).

fof(f58,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f91,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl4_1
  <=> m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f95,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f85,f93,f89])).

fof(f85,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
      | u1_struct_0(sK2) = X0
      | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ) ),
    inference(superposition,[],[f64,f54])).

fof(f54,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f41])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:35:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.49  % (29360)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.19/0.49  % (29356)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.19/0.49  % (29366)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.19/0.49  % (29354)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.19/0.49  % (29373)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.19/0.49  % (29358)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.19/0.50  % (29356)Refutation found. Thanks to Tanya!
% 0.19/0.50  % SZS status Theorem for theBenchmark
% 0.19/0.50  % SZS output start Proof for theBenchmark
% 0.19/0.50  fof(f283,plain,(
% 0.19/0.50    $false),
% 0.19/0.50    inference(avatar_sat_refutation,[],[f95,f105,f165,f277,f282])).
% 0.19/0.50  fof(f282,plain,(
% 0.19/0.50    ~spl4_8),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f281])).
% 0.19/0.50  fof(f281,plain,(
% 0.19/0.50    $false | ~spl4_8),
% 0.19/0.50    inference(subsumption_resolution,[],[f280,f45])).
% 0.19/0.50  fof(f45,plain,(
% 0.19/0.50    l1_pre_topc(sK0)),
% 0.19/0.50    inference(cnf_transformation,[],[f41])).
% 0.19/0.50  fof(f41,plain,(
% 0.19/0.50    (((~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.19/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f40,f39,f38,f37])).
% 0.19/0.50  fof(f37,plain,(
% 0.19/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(sK0),u1_struct_0(X2),u1_struct_0(sK0),X3,k2_tmap_1(X1,sK0,X3,X2)) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f38,plain,(
% 0.19/0.50    ? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(sK0),u1_struct_0(X2),u1_struct_0(sK0),X3,k2_tmap_1(X1,sK0,X3,X2)) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(X2),u1_struct_0(sK0),X3,k2_tmap_1(sK1,sK0,X3,X2)) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f39,plain,(
% 0.19/0.50    ? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(X2),u1_struct_0(sK0),X3,k2_tmap_1(sK1,sK0,X3,X2)) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) => (? [X3] : (~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),X3,k2_tmap_1(sK1,sK0,X3,sK2)) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f40,plain,(
% 0.19/0.50    ? [X3] : (~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),X3,k2_tmap_1(sK1,sK0,X3,sK2)) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X3)) => (~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK3))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f17,plain,(
% 0.19/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.19/0.50    inference(flattening,[],[f16])).
% 0.19/0.50  fof(f16,plain,(
% 0.19/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.19/0.50    inference(ennf_transformation,[],[f15])).
% 0.19/0.50  fof(f15,negated_conjecture,(
% 0.19/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)))))))),
% 0.19/0.50    inference(negated_conjecture,[],[f14])).
% 0.19/0.50  fof(f14,conjecture,(
% 0.19/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)))))))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_tmap_1)).
% 0.19/0.50  fof(f280,plain,(
% 0.19/0.50    ~l1_pre_topc(sK0) | ~spl4_8),
% 0.19/0.50    inference(resolution,[],[f279,f57])).
% 0.19/0.50  fof(f57,plain,(
% 0.19/0.50    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f19])).
% 0.19/0.50  fof(f19,plain,(
% 0.19/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.19/0.50    inference(ennf_transformation,[],[f7])).
% 0.19/0.50  fof(f7,axiom,(
% 0.19/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.19/0.50  fof(f279,plain,(
% 0.19/0.50    ~l1_struct_0(sK0) | ~spl4_8),
% 0.19/0.50    inference(subsumption_resolution,[],[f278,f43])).
% 0.19/0.50  fof(f43,plain,(
% 0.19/0.50    ~v2_struct_0(sK0)),
% 0.19/0.50    inference(cnf_transformation,[],[f41])).
% 0.19/0.50  fof(f278,plain,(
% 0.19/0.50    ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl4_8),
% 0.19/0.50    inference(resolution,[],[f160,f60])).
% 0.19/0.50  fof(f60,plain,(
% 0.19/0.50    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f23])).
% 0.19/0.50  fof(f23,plain,(
% 0.19/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.19/0.50    inference(flattening,[],[f22])).
% 0.19/0.50  fof(f22,plain,(
% 0.19/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.19/0.50    inference(ennf_transformation,[],[f10])).
% 0.19/0.50  fof(f10,axiom,(
% 0.19/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.19/0.50  fof(f160,plain,(
% 0.19/0.50    v1_xboole_0(u1_struct_0(sK0)) | ~spl4_8),
% 0.19/0.50    inference(avatar_component_clause,[],[f158])).
% 0.19/0.50  fof(f158,plain,(
% 0.19/0.50    spl4_8 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.19/0.50  fof(f277,plain,(
% 0.19/0.50    spl4_8 | ~spl4_2 | ~spl4_9),
% 0.19/0.50    inference(avatar_split_clause,[],[f276,f162,f93,f158])).
% 0.19/0.50  fof(f93,plain,(
% 0.19/0.50    spl4_2 <=> ! [X1,X0] : (g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) | u1_struct_0(sK2) = X0)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.19/0.50  fof(f162,plain,(
% 0.19/0.50    spl4_9 <=> v1_partfun1(sK3,u1_struct_0(sK1))),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.19/0.50  fof(f276,plain,(
% 0.19/0.50    v1_xboole_0(u1_struct_0(sK0)) | (~spl4_2 | ~spl4_9)),
% 0.19/0.50    inference(subsumption_resolution,[],[f275,f51])).
% 0.19/0.50  fof(f51,plain,(
% 0.19/0.50    v1_funct_1(sK3)),
% 0.19/0.50    inference(cnf_transformation,[],[f41])).
% 0.19/0.50  % (29355)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.19/0.50  fof(f275,plain,(
% 0.19/0.50    ~v1_funct_1(sK3) | v1_xboole_0(u1_struct_0(sK0)) | (~spl4_2 | ~spl4_9)),
% 0.19/0.50    inference(subsumption_resolution,[],[f274,f52])).
% 0.19/0.50  fof(f52,plain,(
% 0.19/0.50    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.19/0.50    inference(cnf_transformation,[],[f41])).
% 0.19/0.50  fof(f274,plain,(
% 0.19/0.50    ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK3) | v1_xboole_0(u1_struct_0(sK0)) | (~spl4_2 | ~spl4_9)),
% 0.19/0.50    inference(subsumption_resolution,[],[f273,f53])).
% 0.19/0.50  fof(f53,plain,(
% 0.19/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.19/0.50    inference(cnf_transformation,[],[f41])).
% 0.19/0.50  fof(f273,plain,(
% 0.19/0.50    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK3) | v1_xboole_0(u1_struct_0(sK0)) | (~spl4_2 | ~spl4_9)),
% 0.19/0.50    inference(duplicate_literal_removal,[],[f272])).
% 0.19/0.50  fof(f272,plain,(
% 0.19/0.50    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK3) | v1_xboole_0(u1_struct_0(sK0)) | (~spl4_2 | ~spl4_9)),
% 0.19/0.50    inference(condensation,[],[f271])).
% 0.19/0.50  fof(f271,plain,(
% 0.19/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK3) | v1_xboole_0(u1_struct_0(sK0))) ) | (~spl4_2 | ~spl4_9)),
% 0.19/0.50    inference(duplicate_literal_removal,[],[f269])).
% 0.19/0.50  fof(f269,plain,(
% 0.19/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK3) | v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))) ) | (~spl4_2 | ~spl4_9)),
% 0.19/0.50    inference(resolution,[],[f268,f72])).
% 0.19/0.50  fof(f72,plain,(
% 0.19/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f36])).
% 0.19/0.50  fof(f36,plain,(
% 0.19/0.50    ! [X0,X1,X2,X3,X4,X5] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 0.19/0.50    inference(flattening,[],[f35])).
% 0.19/0.50  fof(f35,plain,(
% 0.19/0.50    ! [X0,X1,X2,X3,X4,X5] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 0.19/0.50    inference(ennf_transformation,[],[f12])).
% 0.19/0.50  fof(f12,axiom,(
% 0.19/0.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => r1_funct_2(X0,X1,X2,X3,X4,X4))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r1_funct_2)).
% 0.19/0.50  fof(f268,plain,(
% 0.19/0.50    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3) | (~spl4_2 | ~spl4_9)),
% 0.19/0.50    inference(subsumption_resolution,[],[f267,f77])).
% 0.19/0.50  fof(f77,plain,(
% 0.19/0.50    v4_relat_1(sK3,u1_struct_0(sK1))),
% 0.19/0.50    inference(resolution,[],[f69,f53])).
% 0.19/0.50  fof(f69,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f32])).
% 0.19/0.50  fof(f32,plain,(
% 0.19/0.50    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.50    inference(ennf_transformation,[],[f3])).
% 0.19/0.50  fof(f3,axiom,(
% 0.19/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.19/0.50  fof(f267,plain,(
% 0.19/0.50    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3) | ~v4_relat_1(sK3,u1_struct_0(sK1)) | (~spl4_2 | ~spl4_9)),
% 0.19/0.50    inference(subsumption_resolution,[],[f266,f164])).
% 0.19/0.50  fof(f164,plain,(
% 0.19/0.50    v1_partfun1(sK3,u1_struct_0(sK1)) | ~spl4_9),
% 0.19/0.50    inference(avatar_component_clause,[],[f162])).
% 0.19/0.50  fof(f266,plain,(
% 0.19/0.50    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3) | ~v1_partfun1(sK3,u1_struct_0(sK1)) | ~v4_relat_1(sK3,u1_struct_0(sK1)) | ~spl4_2),
% 0.19/0.50    inference(subsumption_resolution,[],[f265,f76])).
% 0.19/0.50  fof(f76,plain,(
% 0.19/0.50    v1_relat_1(sK3)),
% 0.19/0.50    inference(resolution,[],[f68,f53])).
% 0.19/0.50  fof(f68,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f31])).
% 0.19/0.50  fof(f31,plain,(
% 0.19/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.50    inference(ennf_transformation,[],[f2])).
% 0.19/0.50  fof(f2,axiom,(
% 0.19/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.19/0.50  fof(f265,plain,(
% 0.19/0.50    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3) | ~v1_relat_1(sK3) | ~v1_partfun1(sK3,u1_struct_0(sK1)) | ~v4_relat_1(sK3,u1_struct_0(sK1)) | ~spl4_2),
% 0.19/0.50    inference(superposition,[],[f263,f82])).
% 0.19/0.50  fof(f82,plain,(
% 0.19/0.50    ( ! [X2,X3] : (k7_relat_1(X2,X3) = X2 | ~v1_relat_1(X2) | ~v1_partfun1(X2,X3) | ~v4_relat_1(X2,X3)) )),
% 0.19/0.50    inference(duplicate_literal_removal,[],[f81])).
% 0.19/0.50  fof(f81,plain,(
% 0.19/0.50    ( ! [X2,X3] : (k7_relat_1(X2,X3) = X2 | ~v1_relat_1(X2) | ~v1_partfun1(X2,X3) | ~v4_relat_1(X2,X3) | ~v1_relat_1(X2)) )),
% 0.19/0.50    inference(superposition,[],[f56,f66])).
% 0.19/0.50  fof(f66,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f42])).
% 0.19/0.50  fof(f42,plain,(
% 0.19/0.50    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.19/0.50    inference(nnf_transformation,[],[f30])).
% 0.19/0.50  fof(f30,plain,(
% 0.19/0.50    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.19/0.50    inference(flattening,[],[f29])).
% 0.19/0.50  fof(f29,plain,(
% 0.19/0.50    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.19/0.50    inference(ennf_transformation,[],[f5])).
% 0.19/0.50  fof(f5,axiom,(
% 0.19/0.50    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 0.19/0.50  fof(f56,plain,(
% 0.19/0.50    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f18])).
% 0.19/0.50  fof(f18,plain,(
% 0.19/0.50    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.19/0.50    inference(ennf_transformation,[],[f1])).
% 0.19/0.50  fof(f1,axiom,(
% 0.19/0.50    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).
% 0.19/0.50  % (29375)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.19/0.50  fof(f263,plain,(
% 0.19/0.50    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k7_relat_1(sK3,u1_struct_0(sK1))) | ~spl4_2),
% 0.19/0.50    inference(forward_demodulation,[],[f262,f107])).
% 0.19/0.50  fof(f107,plain,(
% 0.19/0.50    u1_struct_0(sK1) = u1_struct_0(sK2) | ~spl4_2),
% 0.19/0.50    inference(equality_resolution,[],[f94])).
% 0.19/0.50  fof(f94,plain,(
% 0.19/0.50    ( ! [X0,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) | u1_struct_0(sK2) = X0) ) | ~spl4_2),
% 0.19/0.50    inference(avatar_component_clause,[],[f93])).
% 0.19/0.50  fof(f262,plain,(
% 0.19/0.50    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k7_relat_1(sK3,u1_struct_0(sK2))) | ~spl4_2),
% 0.19/0.50    inference(subsumption_resolution,[],[f261,f46])).
% 0.19/0.50  fof(f46,plain,(
% 0.19/0.50    ~v2_struct_0(sK1)),
% 0.19/0.50    inference(cnf_transformation,[],[f41])).
% 0.19/0.50  fof(f261,plain,(
% 0.19/0.50    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k7_relat_1(sK3,u1_struct_0(sK2))) | v2_struct_0(sK1) | ~spl4_2),
% 0.19/0.50    inference(subsumption_resolution,[],[f260,f47])).
% 0.19/0.50  fof(f47,plain,(
% 0.19/0.50    v2_pre_topc(sK1)),
% 0.19/0.50    inference(cnf_transformation,[],[f41])).
% 0.19/0.50  fof(f260,plain,(
% 0.19/0.50    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k7_relat_1(sK3,u1_struct_0(sK2))) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~spl4_2),
% 0.19/0.50    inference(subsumption_resolution,[],[f259,f48])).
% 0.19/0.50  fof(f48,plain,(
% 0.19/0.50    l1_pre_topc(sK1)),
% 0.19/0.50    inference(cnf_transformation,[],[f41])).
% 0.19/0.50  fof(f259,plain,(
% 0.19/0.50    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k7_relat_1(sK3,u1_struct_0(sK2))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~spl4_2),
% 0.19/0.50    inference(subsumption_resolution,[],[f258,f43])).
% 0.19/0.50  fof(f258,plain,(
% 0.19/0.50    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k7_relat_1(sK3,u1_struct_0(sK2))) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~spl4_2),
% 0.19/0.50    inference(subsumption_resolution,[],[f257,f44])).
% 0.19/0.50  fof(f44,plain,(
% 0.19/0.50    v2_pre_topc(sK0)),
% 0.19/0.50    inference(cnf_transformation,[],[f41])).
% 0.19/0.50  fof(f257,plain,(
% 0.19/0.50    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k7_relat_1(sK3,u1_struct_0(sK2))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~spl4_2),
% 0.19/0.50    inference(subsumption_resolution,[],[f256,f45])).
% 0.19/0.50  fof(f256,plain,(
% 0.19/0.50    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k7_relat_1(sK3,u1_struct_0(sK2))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~spl4_2),
% 0.19/0.50    inference(subsumption_resolution,[],[f255,f52])).
% 0.19/0.50  fof(f255,plain,(
% 0.19/0.50    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k7_relat_1(sK3,u1_struct_0(sK2))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~spl4_2),
% 0.19/0.50    inference(subsumption_resolution,[],[f254,f50])).
% 0.19/0.50  fof(f50,plain,(
% 0.19/0.50    m1_pre_topc(sK2,sK1)),
% 0.19/0.50    inference(cnf_transformation,[],[f41])).
% 0.19/0.50  fof(f254,plain,(
% 0.19/0.50    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k7_relat_1(sK3,u1_struct_0(sK2))) | ~m1_pre_topc(sK2,sK1) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~spl4_2),
% 0.19/0.50    inference(subsumption_resolution,[],[f253,f51])).
% 0.19/0.50  fof(f253,plain,(
% 0.19/0.50    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k7_relat_1(sK3,u1_struct_0(sK2))) | ~v1_funct_1(sK3) | ~m1_pre_topc(sK2,sK1) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~spl4_2),
% 0.19/0.50    inference(subsumption_resolution,[],[f252,f53])).
% 0.19/0.50  fof(f252,plain,(
% 0.19/0.50    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k7_relat_1(sK3,u1_struct_0(sK2))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(sK3) | ~m1_pre_topc(sK2,sK1) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~spl4_2),
% 0.19/0.50    inference(superposition,[],[f110,f221])).
% 0.19/0.50  fof(f221,plain,(
% 0.19/0.50    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k7_relat_1(X2,u1_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X2) | ~m1_pre_topc(X3,X0) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.50    inference(duplicate_literal_removal,[],[f220])).
% 0.19/0.50  fof(f220,plain,(
% 0.19/0.50    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k7_relat_1(X2,u1_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X2) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.50    inference(superposition,[],[f71,f61])).
% 0.19/0.50  fof(f61,plain,(
% 0.19/0.50    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f25])).
% 0.19/0.50  % (29370)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.19/0.50  fof(f25,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.50    inference(flattening,[],[f24])).
% 0.19/0.50  fof(f24,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.50    inference(ennf_transformation,[],[f13])).
% 0.19/0.50  fof(f13,axiom,(
% 0.19/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).
% 0.19/0.50  fof(f71,plain,(
% 0.19/0.50    ( ! [X2,X0,X3,X1] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f34])).
% 0.19/0.50  fof(f34,plain,(
% 0.19/0.50    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.19/0.50    inference(flattening,[],[f33])).
% 0.19/0.50  fof(f33,plain,(
% 0.19/0.50    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.19/0.50    inference(ennf_transformation,[],[f6])).
% 0.19/0.50  fof(f6,axiom,(
% 0.19/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.19/0.50  fof(f110,plain,(
% 0.19/0.50    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) | ~spl4_2),
% 0.19/0.50    inference(backward_demodulation,[],[f55,f107])).
% 0.19/0.50  fof(f55,plain,(
% 0.19/0.50    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))),
% 0.19/0.50    inference(cnf_transformation,[],[f41])).
% 0.19/0.50  fof(f165,plain,(
% 0.19/0.50    spl4_8 | spl4_9),
% 0.19/0.50    inference(avatar_split_clause,[],[f156,f162,f158])).
% 0.19/0.50  fof(f156,plain,(
% 0.19/0.50    v1_partfun1(sK3,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.19/0.50    inference(subsumption_resolution,[],[f155,f51])).
% 0.19/0.50  fof(f155,plain,(
% 0.19/0.50    ~v1_funct_1(sK3) | v1_partfun1(sK3,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.19/0.50    inference(subsumption_resolution,[],[f154,f52])).
% 0.19/0.50  fof(f154,plain,(
% 0.19/0.50    ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK3) | v1_partfun1(sK3,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.19/0.50    inference(resolution,[],[f63,f53])).
% 0.19/0.50  fof(f63,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_partfun1(X2,X0) | v1_xboole_0(X1)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f27])).
% 0.19/0.50  fof(f27,plain,(
% 0.19/0.50    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.19/0.50    inference(flattening,[],[f26])).
% 0.19/0.50  fof(f26,plain,(
% 0.19/0.50    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.19/0.50    inference(ennf_transformation,[],[f4])).
% 0.19/0.50  fof(f4,axiom,(
% 0.19/0.50    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.19/0.50  fof(f105,plain,(
% 0.19/0.50    spl4_1),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f104])).
% 0.19/0.50  fof(f104,plain,(
% 0.19/0.50    $false | spl4_1),
% 0.19/0.50    inference(subsumption_resolution,[],[f103,f75])).
% 0.19/0.50  fof(f75,plain,(
% 0.19/0.50    l1_pre_topc(sK2)),
% 0.19/0.50    inference(subsumption_resolution,[],[f74,f48])).
% 0.19/0.50  fof(f74,plain,(
% 0.19/0.50    l1_pre_topc(sK2) | ~l1_pre_topc(sK1)),
% 0.19/0.50    inference(resolution,[],[f59,f50])).
% 0.19/0.50  fof(f59,plain,(
% 0.19/0.50    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f21])).
% 0.19/0.50  fof(f21,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.19/0.50    inference(ennf_transformation,[],[f8])).
% 0.19/0.50  fof(f8,axiom,(
% 0.19/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.19/0.50  fof(f103,plain,(
% 0.19/0.50    ~l1_pre_topc(sK2) | spl4_1),
% 0.19/0.50    inference(resolution,[],[f91,f58])).
% 0.19/0.50  fof(f58,plain,(
% 0.19/0.50    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f20])).
% 0.19/0.50  fof(f20,plain,(
% 0.19/0.50    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.50    inference(ennf_transformation,[],[f9])).
% 0.19/0.50  fof(f9,axiom,(
% 0.19/0.50    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.19/0.50  fof(f91,plain,(
% 0.19/0.50    ~m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) | spl4_1),
% 0.19/0.50    inference(avatar_component_clause,[],[f89])).
% 0.19/0.50  fof(f89,plain,(
% 0.19/0.50    spl4_1 <=> m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.19/0.50  fof(f95,plain,(
% 0.19/0.50    ~spl4_1 | spl4_2),
% 0.19/0.50    inference(avatar_split_clause,[],[f85,f93,f89])).
% 0.19/0.50  fof(f85,plain,(
% 0.19/0.50    ( ! [X0,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) | u1_struct_0(sK2) = X0 | ~m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) )),
% 0.19/0.50    inference(superposition,[],[f64,f54])).
% 0.19/0.50  fof(f54,plain,(
% 0.19/0.50    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 0.19/0.50    inference(cnf_transformation,[],[f41])).
% 0.19/0.50  fof(f64,plain,(
% 0.19/0.50    ( ! [X2,X0,X3,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X0 = X2 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f28])).
% 0.19/0.50  fof(f28,plain,(
% 0.19/0.50    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.19/0.50    inference(ennf_transformation,[],[f11])).
% 0.19/0.50  fof(f11,axiom,(
% 0.19/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).
% 0.19/0.50  % SZS output end Proof for theBenchmark
% 0.19/0.50  % (29356)------------------------------
% 0.19/0.50  % (29356)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (29356)Termination reason: Refutation
% 0.19/0.50  
% 0.19/0.50  % (29356)Memory used [KB]: 6268
% 0.19/0.50  % (29356)Time elapsed: 0.071 s
% 0.19/0.50  % (29356)------------------------------
% 0.19/0.50  % (29356)------------------------------
% 0.19/0.50  % (29372)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.19/0.50  % (29348)Success in time 0.141 s
%------------------------------------------------------------------------------
