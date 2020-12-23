%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:19 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 263 expanded)
%              Number of leaves         :   15 (  76 expanded)
%              Depth                    :   15
%              Number of atoms          :  335 (1390 expanded)
%              Number of equality atoms :   14 (  30 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f110,plain,(
    $false ),
    inference(global_subsumption,[],[f99,f108])).

fof(f108,plain,(
    ~ v3_tex_2(sK6(sK2),sK2) ),
    inference(resolution,[],[f104,f42])).

fof(f42,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v3_tex_2(X1,sK2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ! [X1] :
        ( ~ v3_tex_2(X1,sK2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
    & l1_pre_topc(sK2)
    & v3_tdlat_3(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ! [X1] :
            ( ~ v3_tex_2(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ! [X1] :
          ( ~ v3_tex_2(X1,sK2)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2)
      & v3_tdlat_3(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ? [X1] :
            ( v3_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tex_2)).

fof(f104,plain,(
    m1_subset_1(sK6(sK2),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_subsumption,[],[f93,f102])).

fof(f102,plain,
    ( ~ v2_tex_2(k1_xboole_0,sK2)
    | m1_subset_1(sK6(sK2),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(resolution,[],[f101,f43])).

fof(f43,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f101,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v2_tex_2(X0,sK2)
      | m1_subset_1(sK6(sK2),k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(global_subsumption,[],[f41,f39,f38,f100])).

fof(f100,plain,(
    ! [X0] :
      ( ~ v2_tex_2(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_pre_topc(sK2)
      | m1_subset_1(sK6(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f57,f40])).

fof(f40,plain,(
    v3_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v3_tdlat_3(X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(sK6(X0),X0)
            & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f18,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X2] :
          ( v3_tex_2(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v3_tex_2(sK6(X0),X0)
        & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( v3_tex_2(X2,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( v3_tex_2(X2,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ~ ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ~ v3_tex_2(X2,X0) )
              & v2_tex_2(X1,X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ~ ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ~ ( v3_tex_2(X2,X0)
                      & r1_tarski(X1,X2) ) )
              & v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tex_2)).

fof(f38,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f39,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f41,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f93,plain,(
    v2_tex_2(k1_xboole_0,sK2) ),
    inference(resolution,[],[f89,f74])).

fof(f74,plain,(
    ! [X0] : sP0(X0,k1_xboole_0) ),
    inference(resolution,[],[f73,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK4(X0,X1))),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK5(X0,X1))))
          & sK4(X0,X1) != sK5(X0,X1)
          & r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X1)
          & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
          & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) )
      & ( ! [X4] :
            ( ! [X5] :
                ( r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X5)))
                | X4 = X5
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X1)
                | ~ m1_subset_1(X5,u1_struct_0(X0)) )
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f32,f34,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X3)))
              & X2 != X3
              & r2_hidden(X3,X1)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK4(X0,X1))),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X3)))
            & sK4(X0,X1) != X3
            & r2_hidden(X3,X1)
            & r2_hidden(sK4(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK4(X0,X1))),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X3)))
          & sK4(X0,X1) != X3
          & r2_hidden(X3,X1)
          & r2_hidden(sK4(X0,X1),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK4(X0,X1))),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK5(X0,X1))))
        & sK4(X0,X1) != sK5(X0,X1)
        & r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X1)
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ? [X3] :
                ( ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X3)))
                & X2 != X3
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ! [X4] :
            ( ! [X5] :
                ( r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X5)))
                | X4 = X5
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X1)
                | ~ m1_subset_1(X5,u1_struct_0(X0)) )
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ? [X3] :
                ( ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X3)))
                & X2 != X3
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ! [X2] :
            ( ! [X3] :
                ( r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X3)))
                | X2 = X3
                | ~ r2_hidden(X3,X1)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( ! [X3] :
              ( r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X3)))
              | X2 = X3
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f73,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f72,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ sP7(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(general_splitting,[],[f60,f61_D])).

fof(f61,plain,(
    ! [X2,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | sP7(X1) ) ),
    inference(cnf_transformation,[],[f61_D])).

fof(f61_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ v1_xboole_0(X2)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) )
    <=> ~ sP7(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f72,plain,(
    sP7(k1_xboole_0) ),
    inference(resolution,[],[f70,f43])).

fof(f70,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | sP7(X0) ) ),
    inference(resolution,[],[f69,f61])).

fof(f69,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f68,f43])).

fof(f68,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3(sK2)))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f66,f41])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK3(X1))) ) ),
    inference(resolution,[],[f46,f45])).

fof(f45,plain,(
    ! [X0] :
      ( v1_xboole_0(sK3(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_xboole_0(sK3(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v1_xboole_0(sK3(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_connsp_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f89,plain,
    ( ~ sP0(sK2,k1_xboole_0)
    | v2_tex_2(k1_xboole_0,sK2) ),
    inference(resolution,[],[f86,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ sP0(X1,X0)
      | v2_tex_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( v2_tex_2(X0,X1)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v2_tex_2(X0,X1) ) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ( ( v2_tex_2(X1,X0)
          | ~ sP0(X0,X1) )
        & ( sP0(X0,X1)
          | ~ v2_tex_2(X1,X0) ) )
      | ~ sP1(X1,X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ( v2_tex_2(X1,X0)
      <=> sP0(X0,X1) )
      | ~ sP1(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f86,plain,(
    sP1(k1_xboole_0,sK2) ),
    inference(resolution,[],[f85,f43])).

fof(f85,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(X0,sK2) ) ),
    inference(global_subsumption,[],[f41,f39,f38,f84])).

fof(f84,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_pre_topc(sK2)
      | sP1(X0,sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f56,f40])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v3_tdlat_3(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | sP1(X1,X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f16,f23,f22])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X3)))
                    | X2 = X3
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X3)))
                    | X2 = X3
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r2_hidden(X3,X1)
                        & r2_hidden(X2,X1) )
                     => ( r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X3)))
                        | X2 = X3 ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_tex_2)).

fof(f99,plain,(
    v3_tex_2(sK6(sK2),sK2) ),
    inference(global_subsumption,[],[f93,f97])).

fof(f97,plain,
    ( ~ v2_tex_2(k1_xboole_0,sK2)
    | v3_tex_2(sK6(sK2),sK2) ),
    inference(resolution,[],[f96,f43])).

fof(f96,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v2_tex_2(X0,sK2)
      | v3_tex_2(sK6(sK2),sK2) ) ),
    inference(global_subsumption,[],[f41,f39,f38,f95])).

fof(f95,plain,(
    ! [X0] :
      ( ~ v2_tex_2(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_pre_topc(sK2)
      | v3_tex_2(sK6(sK2),sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f58,f40])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v3_tdlat_3(X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v3_tex_2(sK6(X0),X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:50:17 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (10653)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.49  % (10653)Refutation not found, incomplete strategy% (10653)------------------------------
% 0.22/0.49  % (10653)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (10653)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (10653)Memory used [KB]: 6140
% 0.22/0.49  % (10653)Time elapsed: 0.080 s
% 0.22/0.49  % (10653)------------------------------
% 0.22/0.49  % (10653)------------------------------
% 0.22/0.49  % (10669)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.49  % (10660)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.49  % (10672)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.49  % (10660)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f110,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(global_subsumption,[],[f99,f108])).
% 0.22/0.49  fof(f108,plain,(
% 0.22/0.49    ~v3_tex_2(sK6(sK2),sK2)),
% 0.22/0.49    inference(resolution,[],[f104,f42])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | ~v3_tex_2(X1,sK2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X1] : (~v3_tex_2(X1,sK2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v3_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ? [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (! [X1] : (~v3_tex_2(X1,sK2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v3_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ? [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ? [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,negated_conjecture,(
% 0.22/0.49    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.49    inference(negated_conjecture,[],[f8])).
% 0.22/0.49  fof(f8,conjecture,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tex_2)).
% 0.22/0.49  fof(f104,plain,(
% 0.22/0.49    m1_subset_1(sK6(sK2),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.22/0.49    inference(global_subsumption,[],[f93,f102])).
% 0.22/0.49  fof(f102,plain,(
% 0.22/0.49    ~v2_tex_2(k1_xboole_0,sK2) | m1_subset_1(sK6(sK2),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.22/0.49    inference(resolution,[],[f101,f43])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~v2_tex_2(X0,sK2) | m1_subset_1(sK6(sK2),k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 0.22/0.50    inference(global_subsumption,[],[f41,f39,f38,f100])).
% 0.22/0.50  fof(f100,plain,(
% 0.22/0.50    ( ! [X0] : (~v2_tex_2(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2) | m1_subset_1(sK6(sK2),k1_zfmisc_1(u1_struct_0(sK2))) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.22/0.50    inference(resolution,[],[f57,f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    v3_tdlat_3(sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v3_tdlat_3(X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((v3_tex_2(sK6(X0),X0) & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f18,f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ! [X0] : (? [X2] : (v3_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (v3_tex_2(sK6(X0),X0) & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (? [X2] : (v3_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((? [X2] : (v3_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,plain,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~v3_tex_2(X2,X0)) & v2_tex_2(X1,X0))))),
% 0.22/0.50    inference(pure_predicate_removal,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(v3_tex_2(X2,X0) & r1_tarski(X1,X2))) & v2_tex_2(X1,X0))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tex_2)).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ~v2_struct_0(sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    v2_pre_topc(sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    l1_pre_topc(sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f93,plain,(
% 0.22/0.50    v2_tex_2(k1_xboole_0,sK2)),
% 0.22/0.50    inference(resolution,[],[f89,f74])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    ( ! [X0] : (sP0(X0,k1_xboole_0)) )),
% 0.22/0.50    inference(resolution,[],[f73,f52])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | sP0(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ! [X0,X1] : ((sP0(X0,X1) | ((~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK4(X0,X1))),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK5(X0,X1)))) & sK4(X0,X1) != sK5(X0,X1) & r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK4(X0,X1),X1) & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X5))) | X4 = X5 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~sP0(X0,X1)))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f32,f34,f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X2] : (? [X3] : (~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X3))) & X2 != X3 & r2_hidden(X3,X1) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK4(X0,X1))),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X3))) & sK4(X0,X1) != X3 & r2_hidden(X3,X1) & r2_hidden(sK4(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X3] : (~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK4(X0,X1))),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X3))) & sK4(X0,X1) != X3 & r2_hidden(X3,X1) & r2_hidden(sK4(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK4(X0,X1))),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK5(X0,X1)))) & sK4(X0,X1) != sK5(X0,X1) & r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK4(X0,X1),X1) & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (? [X3] : (~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X3))) & X2 != X3 & r2_hidden(X3,X1) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X5))) | X4 = X5 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~sP0(X0,X1)))),
% 0.22/0.50    inference(rectify,[],[f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (? [X3] : (~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X3))) & X2 != X3 & r2_hidden(X3,X1) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X3))) | X2 = X3 | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~sP0(X0,X1)))),
% 0.22/0.50    inference(nnf_transformation,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2] : (! [X3] : (r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X3))) | X2 = X3 | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))))),
% 0.22/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.50    inference(resolution,[],[f72,f62])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~sP7(X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.50    inference(general_splitting,[],[f60,f61_D])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    ( ! [X2,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | sP7(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f61_D])).
% 0.22/0.50  fof(f61_D,plain,(
% 0.22/0.50    ( ! [X1] : (( ! [X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2))) ) <=> ~sP7(X1)) )),
% 0.22/0.50    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    sP7(k1_xboole_0)),
% 0.22/0.50    inference(resolution,[],[f70,f43])).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | sP7(X0)) )),
% 0.22/0.50    inference(resolution,[],[f69,f61])).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    v1_xboole_0(k1_xboole_0)),
% 0.22/0.50    inference(resolution,[],[f68,f43])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK3(sK2))) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(resolution,[],[f66,f41])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~l1_pre_topc(X1) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK3(X1)))) )),
% 0.22/0.50    inference(resolution,[],[f46,f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ( ! [X0] : (v1_xboole_0(sK3(X0)) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0] : ((v1_xboole_0(sK3(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (v1_xboole_0(sK3(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_connsp_1)).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.22/0.50  fof(f89,plain,(
% 0.22/0.50    ~sP0(sK2,k1_xboole_0) | v2_tex_2(k1_xboole_0,sK2)),
% 0.22/0.50    inference(resolution,[],[f86,f48])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~sP1(X0,X1) | ~sP0(X1,X0) | v2_tex_2(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ! [X0,X1] : (((v2_tex_2(X0,X1) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v2_tex_2(X0,X1))) | ~sP1(X0,X1))),
% 0.22/0.50    inference(rectify,[],[f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X1,X0] : (((v2_tex_2(X1,X0) | ~sP0(X0,X1)) & (sP0(X0,X1) | ~v2_tex_2(X1,X0))) | ~sP1(X1,X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X1,X0] : ((v2_tex_2(X1,X0) <=> sP0(X0,X1)) | ~sP1(X1,X0))),
% 0.22/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.50  fof(f86,plain,(
% 0.22/0.50    sP1(k1_xboole_0,sK2)),
% 0.22/0.50    inference(resolution,[],[f85,f43])).
% 0.22/0.50  fof(f85,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(X0,sK2)) )),
% 0.22/0.50    inference(global_subsumption,[],[f41,f39,f38,f84])).
% 0.22/0.50  fof(f84,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2) | sP1(X0,sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.22/0.50    inference(resolution,[],[f56,f40])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v3_tdlat_3(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | sP1(X1,X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (sP1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(definition_folding,[],[f16,f23,f22])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (! [X3] : (r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X3))) | X2 = X3 | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (! [X3] : (((r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X3))) | X2 = X3) | (~r2_hidden(X3,X1) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r2_hidden(X3,X1) & r2_hidden(X2,X1)) => (r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X3))) | X2 = X3)))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_tex_2)).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    v3_tex_2(sK6(sK2),sK2)),
% 0.22/0.50    inference(global_subsumption,[],[f93,f97])).
% 0.22/0.50  fof(f97,plain,(
% 0.22/0.50    ~v2_tex_2(k1_xboole_0,sK2) | v3_tex_2(sK6(sK2),sK2)),
% 0.22/0.50    inference(resolution,[],[f96,f43])).
% 0.22/0.50  fof(f96,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~v2_tex_2(X0,sK2) | v3_tex_2(sK6(sK2),sK2)) )),
% 0.22/0.50    inference(global_subsumption,[],[f41,f39,f38,f95])).
% 0.22/0.50  fof(f95,plain,(
% 0.22/0.50    ( ! [X0] : (~v2_tex_2(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2) | v3_tex_2(sK6(sK2),sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.22/0.50    inference(resolution,[],[f58,f40])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v3_tdlat_3(X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v3_tex_2(sK6(X0),X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f37])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (10660)------------------------------
% 0.22/0.50  % (10660)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (10660)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (10660)Memory used [KB]: 6268
% 0.22/0.50  % (10660)Time elapsed: 0.068 s
% 0.22/0.50  % (10660)------------------------------
% 0.22/0.50  % (10660)------------------------------
% 0.22/0.50  % (10645)Success in time 0.138 s
%------------------------------------------------------------------------------
