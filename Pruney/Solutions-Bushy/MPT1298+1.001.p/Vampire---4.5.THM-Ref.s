%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1298+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:40 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 544 expanded)
%              Number of leaves         :   25 ( 167 expanded)
%              Depth                    :   18
%              Number of atoms          :  585 (2809 expanded)
%              Number of equality atoms :   18 (  33 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1209,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f75,f235,f239,f244,f557,f559,f641,f647,f975,f982,f1012,f1208])).

fof(f1208,plain,
    ( spl5_2
    | ~ spl5_20
    | spl5_77 ),
    inference(avatar_contradiction_clause,[],[f1207])).

fof(f1207,plain,
    ( $false
    | spl5_2
    | ~ spl5_20
    | spl5_77 ),
    inference(subsumption_resolution,[],[f1112,f1026])).

fof(f1026,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_2 ),
    inference(resolution,[],[f994,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f994,plain,
    ( m1_subset_1(sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_2 ),
    inference(subsumption_resolution,[],[f993,f41])).

fof(f41,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
      | ~ v2_tops_2(sK1,sK0) )
    & ( v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
      | v2_tops_2(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_2(X1,X0) )
            & ( v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
              | v2_tops_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK0),X1),sK0)
            | ~ v2_tops_2(X1,sK0) )
          & ( v1_tops_2(k7_setfam_1(u1_struct_0(sK0),X1),sK0)
            | v2_tops_2(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ( ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK0),X1),sK0)
          | ~ v2_tops_2(X1,sK0) )
        & ( v1_tops_2(k7_setfam_1(u1_struct_0(sK0),X1),sK0)
          | v2_tops_2(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ( ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
        | ~ v2_tops_2(sK1,sK0) )
      & ( v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
        | v2_tops_2(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
            | ~ v2_tops_2(X1,X0) )
          & ( v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
            | v2_tops_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
            | ~ v2_tops_2(X1,X0) )
          & ( v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
            | v2_tops_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_2(X1,X0)
          <~> v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ( v2_tops_2(X1,X0)
            <=> v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tops_2)).

fof(f993,plain,
    ( m1_subset_1(sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f987,f125])).

fof(f125,plain,(
    m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f42,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(f42,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f26])).

fof(f987,plain,
    ( m1_subset_1(sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | spl5_2 ),
    inference(resolution,[],[f73,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ( ~ v3_pre_topc(sK2(X0,X1),X0)
                & r2_hidden(sK2(X0,X1),X1)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK2(X0,X1),X0)
        & r2_hidden(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v3_pre_topc(X2,X0)
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_2)).

fof(f73,plain,
    ( ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl5_2
  <=> v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f1112,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_2
    | ~ spl5_20
    | spl5_77 ),
    inference(subsumption_resolution,[],[f1104,f1011])).

fof(f1011,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1))),sK0)
    | spl5_77 ),
    inference(avatar_component_clause,[],[f1009])).

fof(f1009,plain,
    ( spl5_77
  <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_77])])).

fof(f1104,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1))),sK0)
    | spl5_2
    | ~ spl5_20 ),
    inference(resolution,[],[f1066,f243])).

fof(f243,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(X1,sK0) )
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f242])).

fof(f242,plain,
    ( spl5_20
  <=> ! [X1] :
        ( v4_pre_topc(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X1,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f1066,plain,
    ( r2_hidden(k3_subset_1(u1_struct_0(sK0),sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1))),sK1)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f1065,f42])).

fof(f1065,plain,
    ( r2_hidden(k3_subset_1(u1_struct_0(sK0),sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1))),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl5_2 ),
    inference(subsumption_resolution,[],[f1064,f125])).

fof(f1064,plain,
    ( r2_hidden(k3_subset_1(u1_struct_0(sK0),sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1))),sK1)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl5_2 ),
    inference(subsumption_resolution,[],[f1058,f994])).

fof(f1058,plain,
    ( r2_hidden(k3_subset_1(u1_struct_0(sK0),sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1))),sK1)
    | ~ m1_subset_1(sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl5_2 ),
    inference(resolution,[],[f996,f65])).

% (2842)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
fof(f65,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ r2_hidden(X4,k7_setfam_1(X0,X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | k7_setfam_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k3_subset_1(X0,sK3(X0,X1,X2)),X1)
                  | ~ r2_hidden(sK3(X0,X1,X2),X2) )
                & ( r2_hidden(k3_subset_1(X0,sK3(X0,X1,X2)),X1)
                  | r2_hidden(sK3(X0,X1,X2),X2) )
                & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(X0)) ) )
            & ( ! [X4] :
                  ( ( ( r2_hidden(X4,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X4),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X4),X1)
                      | ~ r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f34])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(k3_subset_1(X0,X3),X1)
            | r2_hidden(X3,X2) )
          & m1_subset_1(X3,k1_zfmisc_1(X0)) )
     => ( ( ~ r2_hidden(k3_subset_1(X0,sK3(X0,X1,X2)),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( r2_hidden(k3_subset_1(X0,sK3(X0,X1,X2)),X1)
          | r2_hidden(sK3(X0,X1,X2),X2) )
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ? [X3] :
                  ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(k3_subset_1(X0,X3),X1)
                    | r2_hidden(X3,X2) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
            & ( ! [X4] :
                  ( ( ( r2_hidden(X4,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X4),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X4),X1)
                      | ~ r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ? [X3] :
                  ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(k3_subset_1(X0,X3),X1)
                    | r2_hidden(X3,X2) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
            & ( ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X3),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X3),X1)
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ? [X3] :
                  ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(k3_subset_1(X0,X3),X1)
                    | r2_hidden(X3,X2) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
            & ( ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X3),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X3),X1)
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).

fof(f996,plain,
    ( r2_hidden(sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1)),k7_setfam_1(u1_struct_0(sK0),sK1))
    | spl5_2 ),
    inference(subsumption_resolution,[],[f995,f41])).

fof(f995,plain,
    ( r2_hidden(sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1)),k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ l1_pre_topc(sK0)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f988,f125])).

fof(f988,plain,
    ( r2_hidden(sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1)),k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | spl5_2 ),
    inference(resolution,[],[f73,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | r2_hidden(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1012,plain,
    ( ~ spl5_47
    | ~ spl5_77
    | spl5_2 ),
    inference(avatar_split_clause,[],[f1007,f71,f1009,f554])).

fof(f554,plain,
    ( spl5_47
  <=> m1_subset_1(sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).

fof(f1007,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1))),sK0)
    | ~ m1_subset_1(sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_2 ),
    inference(subsumption_resolution,[],[f1002,f41])).

fof(f1002,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1))),sK0)
    | ~ m1_subset_1(sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl5_2 ),
    inference(resolution,[],[f998,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tops_1)).

fof(f998,plain,
    ( ~ v3_pre_topc(sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1)),sK0)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f997,f41])).

fof(f997,plain,
    ( ~ v3_pre_topc(sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1)),sK0)
    | ~ l1_pre_topc(sK0)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f989,f125])).

fof(f989,plain,
    ( ~ v3_pre_topc(sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1)),sK0)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | spl5_2 ),
    inference(resolution,[],[f73,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ v3_pre_topc(sK2(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f982,plain,
    ( spl5_1
    | spl5_5 ),
    inference(avatar_split_clause,[],[f681,f101,f67])).

fof(f67,plain,
    ( spl5_1
  <=> v2_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f101,plain,
    ( spl5_5
  <=> r2_hidden(sK4(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f681,plain,
    ( r2_hidden(sK4(sK0,sK1),sK1)
    | v2_tops_2(sK1,sK0) ),
    inference(resolution,[],[f82,f42])).

fof(f82,plain,(
    ! [X8] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | r2_hidden(sK4(sK0,X8),X8)
      | v2_tops_2(X8,sK0) ) ),
    inference(resolution,[],[f41,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v2_tops_2(X1,X0)
      | r2_hidden(sK4(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ( ~ v4_pre_topc(sK4(X0,X1),X0)
                & r2_hidden(sK4(X0,X1),X1)
                & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v4_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v4_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK4(X0,X1),X0)
        & r2_hidden(sK4(X0,X1),X1)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v4_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_2)).

fof(f975,plain,
    ( ~ spl5_4
    | ~ spl5_5
    | ~ spl5_15
    | spl5_42 ),
    inference(avatar_contradiction_clause,[],[f974])).

fof(f974,plain,
    ( $false
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_15
    | spl5_42 ),
    inference(subsumption_resolution,[],[f973,f42])).

fof(f973,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_15
    | spl5_42 ),
    inference(forward_demodulation,[],[f972,f126])).

fof(f126,plain,(
    sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f42,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(f972,plain,
    ( ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_15
    | spl5_42 ),
    inference(subsumption_resolution,[],[f971,f103])).

fof(f103,plain,
    ( r2_hidden(sK4(sK0,sK1),sK1)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f101])).

fof(f971,plain,
    ( ~ r2_hidden(sK4(sK0,sK1),sK1)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_4
    | ~ spl5_15
    | spl5_42 ),
    inference(forward_demodulation,[],[f970,f126])).

fof(f970,plain,
    ( ~ r2_hidden(sK4(sK0,sK1),k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_4
    | ~ spl5_15
    | spl5_42 ),
    inference(subsumption_resolution,[],[f969,f125])).

fof(f969,plain,
    ( ~ r2_hidden(sK4(sK0,sK1),k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_4
    | ~ spl5_15
    | spl5_42 ),
    inference(subsumption_resolution,[],[f959,f97])).

fof(f97,plain,
    ( m1_subset_1(sK4(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl5_4
  <=> m1_subset_1(sK4(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f959,plain,
    ( ~ r2_hidden(sK4(sK0,sK1),k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)))
    | ~ m1_subset_1(sK4(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_4
    | ~ spl5_15
    | spl5_42 ),
    inference(resolution,[],[f954,f65])).

fof(f954,plain,
    ( ~ r2_hidden(k3_subset_1(u1_struct_0(sK0),sK4(sK0,sK1)),k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ spl5_4
    | ~ spl5_15
    | spl5_42 ),
    inference(subsumption_resolution,[],[f948,f525])).

fof(f525,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK4(sK0,sK1)),sK0)
    | spl5_42 ),
    inference(avatar_component_clause,[],[f523])).

fof(f523,plain,
    ( spl5_42
  <=> v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK4(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f948,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK4(sK0,sK1)),sK0)
    | ~ r2_hidden(k3_subset_1(u1_struct_0(sK0),sK4(sK0,sK1)),k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ spl5_4
    | ~ spl5_15 ),
    inference(resolution,[],[f192,f209])).

fof(f209,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK4(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_4 ),
    inference(resolution,[],[f97,f61])).

fof(f192,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(X0,sK0)
        | ~ r2_hidden(X0,k7_setfam_1(u1_struct_0(sK0),sK1)) )
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl5_15
  <=> ! [X0] :
        ( v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,k7_setfam_1(u1_struct_0(sK0),sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f647,plain,
    ( ~ spl5_42
    | spl5_43
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f646,f95,f527,f523])).

fof(f527,plain,
    ( spl5_43
  <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK4(sK0,sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f646,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK4(sK0,sK1))),sK0)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK4(sK0,sK1)),sK0)
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f602,f41])).

fof(f602,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK4(sK0,sK1))),sK0)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK4(sK0,sK1)),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_4 ),
    inference(resolution,[],[f209,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

% (2840)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f641,plain,
    ( ~ spl5_4
    | spl5_6
    | ~ spl5_43 ),
    inference(avatar_contradiction_clause,[],[f640])).

fof(f640,plain,
    ( $false
    | ~ spl5_4
    | spl5_6
    | ~ spl5_43 ),
    inference(subsumption_resolution,[],[f639,f97])).

fof(f639,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_6
    | ~ spl5_43 ),
    inference(subsumption_resolution,[],[f638,f109])).

fof(f109,plain,
    ( ~ v4_pre_topc(sK4(sK0,sK1),sK0)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl5_6
  <=> v4_pre_topc(sK4(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f638,plain,
    ( v4_pre_topc(sK4(sK0,sK1),sK0)
    | ~ m1_subset_1(sK4(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_43 ),
    inference(superposition,[],[f529,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f529,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK4(sK0,sK1))),sK0)
    | ~ spl5_43 ),
    inference(avatar_component_clause,[],[f527])).

fof(f559,plain,
    ( ~ spl5_2
    | spl5_15 ),
    inference(avatar_split_clause,[],[f558,f191,f71])).

fof(f558,plain,(
    ! [X2] :
      ( v3_pre_topc(X2,sK0)
      | ~ r2_hidden(X2,k7_setfam_1(u1_struct_0(sK0),sK1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) ) ),
    inference(subsumption_resolution,[],[f298,f41])).

fof(f298,plain,(
    ! [X2] :
      ( v3_pre_topc(X2,sK0)
      | ~ r2_hidden(X2,k7_setfam_1(u1_struct_0(sK0),sK1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f125,f45])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( v3_pre_topc(X3,X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f557,plain,
    ( spl5_47
    | spl5_2 ),
    inference(avatar_split_clause,[],[f552,f71,f554])).

fof(f552,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | m1_subset_1(sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f299,f41])).

fof(f299,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | m1_subset_1(sK2(sK0,k7_setfam_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f125,f46])).

fof(f244,plain,
    ( ~ spl5_1
    | spl5_20 ),
    inference(avatar_split_clause,[],[f240,f242,f67])).

fof(f240,plain,(
    ! [X1] :
      ( v4_pre_topc(X1,sK0)
      | ~ r2_hidden(X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tops_2(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f115,f41])).

fof(f115,plain,(
    ! [X1] :
      ( v4_pre_topc(X1,sK0)
      | ~ r2_hidden(X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tops_2(sK1,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f42,f56])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( v4_pre_topc(X3,X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f239,plain,
    ( spl5_4
    | spl5_1 ),
    inference(avatar_split_clause,[],[f238,f67,f95])).

fof(f238,plain,
    ( v2_tops_2(sK1,sK0)
    | m1_subset_1(sK4(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f116,f41])).

fof(f116,plain,
    ( v2_tops_2(sK1,sK0)
    | m1_subset_1(sK4(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f42,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v2_tops_2(X1,X0)
      | m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f235,plain,
    ( ~ spl5_6
    | spl5_1 ),
    inference(avatar_split_clause,[],[f234,f67,f107])).

fof(f234,plain,
    ( v2_tops_2(sK1,sK0)
    | ~ v4_pre_topc(sK4(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f118,f41])).

fof(f118,plain,
    ( v2_tops_2(sK1,sK0)
    | ~ v4_pre_topc(sK4(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f42,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v2_tops_2(X1,X0)
      | ~ v4_pre_topc(sK4(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f75,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f43,f71,f67])).

fof(f43,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f74,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f44,f71,f67])).

fof(f44,plain,
    ( ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

%------------------------------------------------------------------------------
