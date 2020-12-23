%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:20 EST 2020

% Result     : Theorem 1.96s
% Output     : Refutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :  190 ( 499 expanded)
%              Number of leaves         :   31 ( 160 expanded)
%              Depth                    :   22
%              Number of atoms          :  963 (2465 expanded)
%              Number of equality atoms :   67 ( 284 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1113,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f98,f103,f108,f113,f119,f164,f941,f1043,f1072,f1080,f1096,f1099,f1104,f1112])).

fof(f1112,plain,
    ( ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | spl5_7
    | ~ spl5_12 ),
    inference(avatar_contradiction_clause,[],[f1111])).

fof(f1111,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | spl5_7
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f1110,f126])).

fof(f126,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl5_7 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl5_7
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f1110,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f1109,f97])).

fof(f97,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl5_2
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f1109,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_3
    | spl5_5
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f1108,f112])).

fof(f112,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl5_5
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f1108,plain,
    ( v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_3
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f1106,f102])).

fof(f102,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl5_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f1106,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_12 ),
    inference(resolution,[],[f247,f966])).

fof(f966,plain,(
    ! [X2,X3] :
      ( ~ v2_struct_0(k1_tex_2(X2,X3))
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | v1_xboole_0(u1_struct_0(X2)) ) ),
    inference(subsumption_resolution,[],[f958,f120])).

fof(f120,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(resolution,[],[f80,f87])).

fof(f87,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f46,f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f80,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f50,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
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

fof(f958,plain,(
    ! [X2,X3] :
      ( v1_xboole_0(k1_tarski(X3))
      | ~ v2_struct_0(k1_tex_2(X2,X3))
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | v1_xboole_0(u1_struct_0(X2)) ) ),
    inference(duplicate_literal_removal,[],[f957])).

fof(f957,plain,(
    ! [X2,X3] :
      ( v1_xboole_0(k1_tarski(X3))
      | ~ v2_struct_0(k1_tex_2(X2,X3))
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | v1_xboole_0(u1_struct_0(X2))
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | v1_xboole_0(u1_struct_0(X2)) ) ),
    inference(superposition,[],[f883,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f883,plain,(
    ! [X10,X11] :
      ( v1_xboole_0(k6_domain_1(u1_struct_0(X10),X11))
      | ~ v2_struct_0(k1_tex_2(X10,X11))
      | ~ l1_pre_topc(X10)
      | v2_struct_0(X10)
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | v1_xboole_0(u1_struct_0(X10)) ) ),
    inference(subsumption_resolution,[],[f882,f60])).

fof(f60,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f882,plain,(
    ! [X10,X11] :
      ( ~ v2_struct_0(k1_tex_2(X10,X11))
      | v1_xboole_0(k6_domain_1(u1_struct_0(X10),X11))
      | ~ l1_pre_topc(X10)
      | v2_struct_0(X10)
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | v1_xboole_0(u1_struct_0(X10))
      | ~ m1_subset_1(k6_domain_1(u1_struct_0(X10),X11),k1_zfmisc_1(u1_struct_0(X10))) ) ),
    inference(subsumption_resolution,[],[f860,f203])).

fof(f203,plain,(
    ! [X4,X5] :
      ( m1_pre_topc(sK2(X4,k6_domain_1(u1_struct_0(X4),X5)),X4)
      | v1_xboole_0(k6_domain_1(u1_struct_0(X4),X5))
      | ~ l1_pre_topc(X4)
      | v2_struct_0(X4)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | v1_xboole_0(u1_struct_0(X4)) ) ),
    inference(resolution,[],[f70,f60])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(sK2(X0,X1),X0)
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK2(X0,X1)) = X1
            & m1_pre_topc(sK2(X0,X1),X0)
            & v1_pre_topc(sK2(X0,X1))
            & ~ v2_struct_0(sK2(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & v1_pre_topc(X2)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK2(X0,X1)) = X1
        & m1_pre_topc(sK2(X0,X1),X0)
        & v1_pre_topc(sK2(X0,X1))
        & ~ v2_struct_0(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tsep_1)).

fof(f860,plain,(
    ! [X10,X11] :
      ( ~ v2_struct_0(k1_tex_2(X10,X11))
      | v1_xboole_0(k6_domain_1(u1_struct_0(X10),X11))
      | ~ l1_pre_topc(X10)
      | v2_struct_0(X10)
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | v1_xboole_0(u1_struct_0(X10))
      | ~ m1_pre_topc(sK2(X10,k6_domain_1(u1_struct_0(X10),X11)),X10)
      | ~ m1_subset_1(k6_domain_1(u1_struct_0(X10),X11),k1_zfmisc_1(u1_struct_0(X10))) ) ),
    inference(duplicate_literal_removal,[],[f791])).

fof(f791,plain,(
    ! [X10,X11] :
      ( ~ v2_struct_0(k1_tex_2(X10,X11))
      | v1_xboole_0(k6_domain_1(u1_struct_0(X10),X11))
      | ~ l1_pre_topc(X10)
      | v2_struct_0(X10)
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | v1_xboole_0(u1_struct_0(X10))
      | ~ m1_pre_topc(sK2(X10,k6_domain_1(u1_struct_0(X10),X11)),X10)
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | ~ l1_pre_topc(X10)
      | v2_struct_0(X10)
      | ~ m1_subset_1(k6_domain_1(u1_struct_0(X10),X11),k1_zfmisc_1(u1_struct_0(X10)))
      | v1_xboole_0(k6_domain_1(u1_struct_0(X10),X11))
      | ~ l1_pre_topc(X10)
      | v2_struct_0(X10) ) ),
    inference(superposition,[],[f173,f433])).

fof(f433,plain,(
    ! [X2,X0,X1] :
      ( k1_tex_2(X1,X2) = sK2(X0,k6_domain_1(u1_struct_0(X1),X2))
      | ~ m1_pre_topc(sK2(X0,k6_domain_1(u1_struct_0(X1),X2)),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(k6_domain_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(k6_domain_1(u1_struct_0(X1),X2))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f228])).

fof(f228,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_domain_1(u1_struct_0(X2),X3) != X1
      | sK2(X0,X1) = k1_tex_2(X2,X3)
      | ~ m1_pre_topc(sK2(X0,X1),X2)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f227,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_pre_topc(sK2(X0,X1))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f227,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_domain_1(u1_struct_0(X2),X3) != X1
      | sK2(X0,X1) = k1_tex_2(X2,X3)
      | ~ m1_pre_topc(sK2(X0,X1),X2)
      | ~ v1_pre_topc(sK2(X0,X1))
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f223,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_struct_0(sK2(X0,X1))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f223,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_domain_1(u1_struct_0(X2),X3) != X1
      | sK2(X0,X1) = k1_tex_2(X2,X3)
      | ~ m1_pre_topc(sK2(X0,X1),X2)
      | ~ v1_pre_topc(sK2(X0,X1))
      | v2_struct_0(sK2(X0,X1))
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f63,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK2(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(X2) != k6_domain_1(u1_struct_0(X0),X1)
      | k1_tex_2(X0,X1) = X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_tex_2(X0,X1) = X2
                  | u1_struct_0(X2) != k6_domain_1(u1_struct_0(X0),X1) )
                & ( u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)
                  | k1_tex_2(X0,X1) != X2 ) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tex_2)).

fof(f173,plain,(
    ! [X2,X3] :
      ( ~ v2_struct_0(sK2(X2,k6_domain_1(u1_struct_0(X2),X3)))
      | v1_xboole_0(k6_domain_1(u1_struct_0(X2),X3))
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | v1_xboole_0(u1_struct_0(X2)) ) ),
    inference(resolution,[],[f68,f60])).

fof(f247,plain,
    ( v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f245])).

fof(f245,plain,
    ( spl5_12
  <=> v2_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f1104,plain,
    ( spl5_17
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f1103,f1063,f110,f100,f95,f1056])).

fof(f1056,plain,
    ( spl5_17
  <=> v1_tdlat_3(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f1063,plain,
    ( spl5_18
  <=> v2_pre_topc(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f1103,plain,
    ( v1_tdlat_3(k1_tex_2(sK0,sK1))
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f1102,f112])).

fof(f1102,plain,
    ( v1_tdlat_3(k1_tex_2(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f1101,f102])).

fof(f1101,plain,
    ( v1_tdlat_3(k1_tex_2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f1100,f97])).

fof(f1100,plain,
    ( v1_tdlat_3(k1_tex_2(sK0,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_18 ),
    inference(resolution,[],[f1065,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(k1_tex_2(X0,X1))
      | v1_tdlat_3(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tdlat_3(k1_tex_2(X0,X1))
          | ~ v2_pre_topc(k1_tex_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tdlat_3(k1_tex_2(X0,X1))
          | ~ v2_pre_topc(k1_tex_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v2_pre_topc(k1_tex_2(X0,X1))
           => v1_tdlat_3(k1_tex_2(X0,X1)) ) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v2_pre_topc(k1_tex_2(X0,X1))
           => ( v2_tdlat_3(k1_tex_2(X0,X1))
              & v1_tdlat_3(k1_tex_2(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tex_2)).

fof(f1065,plain,
    ( v2_pre_topc(k1_tex_2(sK0,sK1))
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f1063])).

fof(f1099,plain,
    ( spl5_18
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f1098,f253,f105,f100,f1063])).

fof(f105,plain,
    ( spl5_4
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f253,plain,
    ( spl5_14
  <=> m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f1098,plain,
    ( v2_pre_topc(k1_tex_2(sK0,sK1))
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f1097,f107])).

fof(f107,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f105])).

fof(f1097,plain,
    ( v2_pre_topc(k1_tex_2(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | ~ spl5_3
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f1089,f102])).

fof(f1089,plain,
    ( v2_pre_topc(k1_tex_2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl5_14 ),
    inference(resolution,[],[f254,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f254,plain,
    ( m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f253])).

fof(f1096,plain,
    ( ~ spl5_17
    | spl5_12
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | spl5_7
    | spl5_10
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f1095,f253,f249,f161,f124,f110,f100,f95,f245,f1056])).

fof(f161,plain,
    ( spl5_10
  <=> v2_tex_2(k1_tarski(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f249,plain,
    ( spl5_13
  <=> v1_pre_topc(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f1095,plain,
    ( v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ v1_tdlat_3(k1_tex_2(sK0,sK1))
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | spl5_7
    | spl5_10
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f1094,f97])).

fof(f1094,plain,
    ( v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ v1_tdlat_3(k1_tex_2(sK0,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl5_3
    | spl5_5
    | spl5_7
    | spl5_10
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f1093,f112])).

fof(f1093,plain,
    ( v2_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ v1_tdlat_3(k1_tex_2(sK0,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl5_3
    | spl5_7
    | spl5_10
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f1092,f102])).

fof(f1092,plain,
    ( v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v1_tdlat_3(k1_tex_2(sK0,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl5_7
    | spl5_10
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f1091,f250])).

fof(f250,plain,
    ( v1_pre_topc(k1_tex_2(sK0,sK1))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f249])).

fof(f1091,plain,
    ( ~ v1_pre_topc(k1_tex_2(sK0,sK1))
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v1_tdlat_3(k1_tex_2(sK0,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl5_7
    | spl5_10
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f1090,f163])).

fof(f163,plain,
    ( ~ v2_tex_2(k1_tarski(sK1),sK0)
    | spl5_10 ),
    inference(avatar_component_clause,[],[f161])).

fof(f1090,plain,
    ( v2_tex_2(k1_tarski(sK1),sK0)
    | ~ v1_pre_topc(k1_tex_2(sK0,sK1))
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v1_tdlat_3(k1_tex_2(sK0,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl5_7
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f1088,f126])).

fof(f1088,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | v2_tex_2(k1_tarski(sK1),sK0)
    | ~ v1_pre_topc(k1_tex_2(sK0,sK1))
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v1_tdlat_3(k1_tex_2(sK0,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl5_14 ),
    inference(resolution,[],[f254,f677])).

fof(f677,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
      | v1_xboole_0(u1_struct_0(X0))
      | v2_tex_2(k1_tarski(X1),X0)
      | ~ v1_pre_topc(k1_tex_2(X0,X1))
      | v2_struct_0(k1_tex_2(X0,X1))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v1_tdlat_3(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f674])).

fof(f674,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k1_tarski(X1),X0)
      | v1_xboole_0(u1_struct_0(X0))
      | ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ v1_pre_topc(k1_tex_2(X0,X1))
      | v2_struct_0(k1_tex_2(X0,X1))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v1_tdlat_3(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v1_xboole_0(u1_struct_0(X0))
      | ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ v1_pre_topc(k1_tex_2(X0,X1))
      | v2_struct_0(k1_tex_2(X0,X1))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f400,f237])).

fof(f237,plain,(
    ! [X4,X3] :
      ( k1_tarski(X4) = u1_struct_0(k1_tex_2(X3,X4))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | v1_xboole_0(u1_struct_0(X3))
      | ~ m1_pre_topc(k1_tex_2(X3,X4),X3)
      | ~ v1_pre_topc(k1_tex_2(X3,X4))
      | v2_struct_0(k1_tex_2(X3,X4))
      | ~ l1_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(duplicate_literal_removal,[],[f234])).

fof(f234,plain,(
    ! [X4,X3] :
      ( k1_tarski(X4) = u1_struct_0(k1_tex_2(X3,X4))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | v1_xboole_0(u1_struct_0(X3))
      | ~ m1_pre_topc(k1_tex_2(X3,X4),X3)
      | ~ v1_pre_topc(k1_tex_2(X3,X4))
      | v2_struct_0(k1_tex_2(X3,X4))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l1_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(superposition,[],[f61,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1))
      | ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ v1_pre_topc(k1_tex_2(X0,X1))
      | v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)
      | k1_tex_2(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f400,plain,(
    ! [X2,X3] :
      ( v2_tex_2(u1_struct_0(k1_tex_2(X3,X2)),X3)
      | v1_xboole_0(u1_struct_0(X3))
      | ~ m1_pre_topc(k1_tex_2(X3,X2),X3)
      | ~ v1_pre_topc(k1_tex_2(X3,X2))
      | v2_struct_0(k1_tex_2(X3,X2))
      | ~ l1_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ v1_tdlat_3(k1_tex_2(X3,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X3)) ) ),
    inference(duplicate_literal_removal,[],[f385])).

fof(f385,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,u1_struct_0(X3))
      | v1_xboole_0(u1_struct_0(X3))
      | ~ m1_pre_topc(k1_tex_2(X3,X2),X3)
      | ~ v1_pre_topc(k1_tex_2(X3,X2))
      | v2_struct_0(k1_tex_2(X3,X2))
      | ~ l1_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ v1_tdlat_3(k1_tex_2(X3,X2))
      | v2_tex_2(u1_struct_0(k1_tex_2(X3,X2)),X3)
      | ~ m1_pre_topc(k1_tex_2(X3,X2),X3)
      | v2_struct_0(k1_tex_2(X3,X2))
      | ~ l1_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(resolution,[],[f236,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X1)
      | v2_tex_2(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v1_tdlat_3(X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_tex_2(X2,X0)
                  | ~ v1_tdlat_3(X1) )
                & ( v1_tdlat_3(X1)
                  | ~ v2_tex_2(X2,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v2_tex_2(X2,X0)
                <=> v1_tdlat_3(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).

fof(f236,plain,(
    ! [X6,X5] :
      ( m1_subset_1(u1_struct_0(k1_tex_2(X5,X6)),k1_zfmisc_1(u1_struct_0(X5)))
      | ~ m1_subset_1(X6,u1_struct_0(X5))
      | v1_xboole_0(u1_struct_0(X5))
      | ~ m1_pre_topc(k1_tex_2(X5,X6),X5)
      | ~ v1_pre_topc(k1_tex_2(X5,X6))
      | v2_struct_0(k1_tex_2(X5,X6))
      | ~ l1_pre_topc(X5)
      | v2_struct_0(X5) ) ),
    inference(duplicate_literal_removal,[],[f235])).

fof(f235,plain,(
    ! [X6,X5] :
      ( m1_subset_1(u1_struct_0(k1_tex_2(X5,X6)),k1_zfmisc_1(u1_struct_0(X5)))
      | ~ m1_subset_1(X6,u1_struct_0(X5))
      | v1_xboole_0(u1_struct_0(X5))
      | ~ m1_pre_topc(k1_tex_2(X5,X6),X5)
      | ~ v1_pre_topc(k1_tex_2(X5,X6))
      | v2_struct_0(k1_tex_2(X5,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X5))
      | ~ l1_pre_topc(X5)
      | v2_struct_0(X5) ) ),
    inference(superposition,[],[f60,f85])).

fof(f1080,plain,
    ( ~ spl5_2
    | spl5_7
    | ~ spl5_16 ),
    inference(avatar_contradiction_clause,[],[f1079])).

fof(f1079,plain,
    ( $false
    | ~ spl5_2
    | spl5_7
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f1078,f126])).

fof(f1078,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_2
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f1077,f97])).

fof(f1077,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f1076,f120])).

fof(f1076,plain,
    ( v1_xboole_0(k1_tarski(sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_16 ),
    inference(superposition,[],[f1033,f61])).

fof(f1033,plain,
    ( v1_xboole_0(k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f1031])).

fof(f1031,plain,
    ( spl5_16
  <=> v1_xboole_0(k6_domain_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

% (11194)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
fof(f1072,plain,
    ( spl5_16
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | spl5_7
    | spl5_14 ),
    inference(avatar_split_clause,[],[f1071,f253,f124,f110,f100,f95,f1031])).

fof(f1071,plain,
    ( v1_xboole_0(k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | spl5_7
    | spl5_14 ),
    inference(subsumption_resolution,[],[f1070,f126])).

fof(f1070,plain,
    ( v1_xboole_0(k6_domain_1(u1_struct_0(sK0),sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | spl5_14 ),
    inference(subsumption_resolution,[],[f1069,f97])).

fof(f1069,plain,
    ( v1_xboole_0(k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_3
    | spl5_5
    | spl5_14 ),
    inference(subsumption_resolution,[],[f1068,f112])).

fof(f1068,plain,
    ( v1_xboole_0(k6_domain_1(u1_struct_0(sK0),sK1))
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_3
    | spl5_14 ),
    inference(subsumption_resolution,[],[f1067,f102])).

fof(f1067,plain,
    ( v1_xboole_0(k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | spl5_14 ),
    inference(resolution,[],[f255,f879])).

fof(f879,plain,(
    ! [X6,X7] :
      ( m1_pre_topc(k1_tex_2(X6,X7),X6)
      | v1_xboole_0(k6_domain_1(u1_struct_0(X6),X7))
      | ~ l1_pre_topc(X6)
      | v2_struct_0(X6)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | v1_xboole_0(u1_struct_0(X6)) ) ),
    inference(subsumption_resolution,[],[f878,f60])).

fof(f878,plain,(
    ! [X6,X7] :
      ( m1_pre_topc(k1_tex_2(X6,X7),X6)
      | v1_xboole_0(k6_domain_1(u1_struct_0(X6),X7))
      | ~ l1_pre_topc(X6)
      | v2_struct_0(X6)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | v1_xboole_0(u1_struct_0(X6))
      | ~ m1_subset_1(k6_domain_1(u1_struct_0(X6),X7),k1_zfmisc_1(u1_struct_0(X6))) ) ),
    inference(subsumption_resolution,[],[f862,f203])).

fof(f862,plain,(
    ! [X6,X7] :
      ( m1_pre_topc(k1_tex_2(X6,X7),X6)
      | v1_xboole_0(k6_domain_1(u1_struct_0(X6),X7))
      | ~ l1_pre_topc(X6)
      | v2_struct_0(X6)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | v1_xboole_0(u1_struct_0(X6))
      | ~ m1_pre_topc(sK2(X6,k6_domain_1(u1_struct_0(X6),X7)),X6)
      | ~ m1_subset_1(k6_domain_1(u1_struct_0(X6),X7),k1_zfmisc_1(u1_struct_0(X6))) ) ),
    inference(duplicate_literal_removal,[],[f789])).

fof(f789,plain,(
    ! [X6,X7] :
      ( m1_pre_topc(k1_tex_2(X6,X7),X6)
      | v1_xboole_0(k6_domain_1(u1_struct_0(X6),X7))
      | ~ l1_pre_topc(X6)
      | v2_struct_0(X6)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | v1_xboole_0(u1_struct_0(X6))
      | ~ m1_pre_topc(sK2(X6,k6_domain_1(u1_struct_0(X6),X7)),X6)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ l1_pre_topc(X6)
      | v2_struct_0(X6)
      | ~ m1_subset_1(k6_domain_1(u1_struct_0(X6),X7),k1_zfmisc_1(u1_struct_0(X6)))
      | v1_xboole_0(k6_domain_1(u1_struct_0(X6),X7))
      | ~ l1_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(superposition,[],[f203,f433])).

fof(f255,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | spl5_14 ),
    inference(avatar_component_clause,[],[f253])).

fof(f1043,plain,
    ( spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(avatar_contradiction_clause,[],[f1042])).

fof(f1042,plain,
    ( $false
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f1041,f112])).

fof(f1041,plain,
    ( v2_struct_0(sK0)
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f1039,f118])).

fof(f118,plain,
    ( l1_struct_0(sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl5_6
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f1039,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_7 ),
    inference(resolution,[],[f125,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f125,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f124])).

fof(f941,plain,
    ( spl5_13
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | spl5_7 ),
    inference(avatar_split_clause,[],[f940,f124,f110,f100,f95,f249])).

fof(f940,plain,
    ( v1_pre_topc(k1_tex_2(sK0,sK1))
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | spl5_7 ),
    inference(subsumption_resolution,[],[f932,f126])).

fof(f932,plain,
    ( v1_pre_topc(k1_tex_2(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5 ),
    inference(subsumption_resolution,[],[f931,f112])).

fof(f931,plain,
    ( v2_struct_0(sK0)
    | v1_pre_topc(k1_tex_2(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f920,f102])).

fof(f920,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_pre_topc(k1_tex_2(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_2 ),
    inference(resolution,[],[f913,f97])).

fof(f913,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X2)
      | v1_pre_topc(k1_tex_2(X2,X3))
      | v1_xboole_0(u1_struct_0(X2)) ) ),
    inference(subsumption_resolution,[],[f906,f120])).

fof(f906,plain,(
    ! [X2,X3] :
      ( v1_xboole_0(k1_tarski(X3))
      | v1_pre_topc(k1_tex_2(X2,X3))
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | v1_xboole_0(u1_struct_0(X2)) ) ),
    inference(duplicate_literal_removal,[],[f905])).

fof(f905,plain,(
    ! [X2,X3] :
      ( v1_xboole_0(k1_tarski(X3))
      | v1_pre_topc(k1_tex_2(X2,X3))
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | v1_xboole_0(u1_struct_0(X2))
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | v1_xboole_0(u1_struct_0(X2)) ) ),
    inference(superposition,[],[f881,f61])).

fof(f881,plain,(
    ! [X8,X9] :
      ( v1_xboole_0(k6_domain_1(u1_struct_0(X8),X9))
      | v1_pre_topc(k1_tex_2(X8,X9))
      | ~ l1_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | v1_xboole_0(u1_struct_0(X8)) ) ),
    inference(subsumption_resolution,[],[f880,f60])).

fof(f880,plain,(
    ! [X8,X9] :
      ( v1_pre_topc(k1_tex_2(X8,X9))
      | v1_xboole_0(k6_domain_1(u1_struct_0(X8),X9))
      | ~ l1_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | v1_xboole_0(u1_struct_0(X8))
      | ~ m1_subset_1(k6_domain_1(u1_struct_0(X8),X9),k1_zfmisc_1(u1_struct_0(X8))) ) ),
    inference(subsumption_resolution,[],[f861,f203])).

fof(f861,plain,(
    ! [X8,X9] :
      ( v1_pre_topc(k1_tex_2(X8,X9))
      | v1_xboole_0(k6_domain_1(u1_struct_0(X8),X9))
      | ~ l1_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | v1_xboole_0(u1_struct_0(X8))
      | ~ m1_pre_topc(sK2(X8,k6_domain_1(u1_struct_0(X8),X9)),X8)
      | ~ m1_subset_1(k6_domain_1(u1_struct_0(X8),X9),k1_zfmisc_1(u1_struct_0(X8))) ) ),
    inference(duplicate_literal_removal,[],[f790])).

fof(f790,plain,(
    ! [X8,X9] :
      ( v1_pre_topc(k1_tex_2(X8,X9))
      | v1_xboole_0(k6_domain_1(u1_struct_0(X8),X9))
      | ~ l1_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | v1_xboole_0(u1_struct_0(X8))
      | ~ m1_pre_topc(sK2(X8,k6_domain_1(u1_struct_0(X8),X9)),X8)
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | ~ l1_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ m1_subset_1(k6_domain_1(u1_struct_0(X8),X9),k1_zfmisc_1(u1_struct_0(X8)))
      | v1_xboole_0(k6_domain_1(u1_struct_0(X8),X9))
      | ~ l1_pre_topc(X8)
      | v2_struct_0(X8) ) ),
    inference(superposition,[],[f182,f433])).

fof(f182,plain,(
    ! [X4,X5] :
      ( v1_pre_topc(sK2(X4,k6_domain_1(u1_struct_0(X4),X5)))
      | v1_xboole_0(k6_domain_1(u1_struct_0(X4),X5))
      | ~ l1_pre_topc(X4)
      | v2_struct_0(X4)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | v1_xboole_0(u1_struct_0(X4)) ) ),
    inference(resolution,[],[f69,f60])).

fof(f164,plain,
    ( ~ spl5_10
    | spl5_1
    | ~ spl5_2
    | spl5_7 ),
    inference(avatar_split_clause,[],[f159,f124,f95,f90,f161])).

fof(f90,plain,
    ( spl5_1
  <=> v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f159,plain,
    ( ~ v2_tex_2(k1_tarski(sK1),sK0)
    | spl5_1
    | ~ spl5_2
    | spl5_7 ),
    inference(subsumption_resolution,[],[f158,f126])).

fof(f158,plain,
    ( ~ v2_tex_2(k1_tarski(sK1),sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f155,f97])).

fof(f155,plain,
    ( ~ v2_tex_2(k1_tarski(sK1),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | spl5_1 ),
    inference(superposition,[],[f92,f61])).

fof(f92,plain,
    ( ~ v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f90])).

fof(f119,plain,
    ( spl5_6
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f114,f100,f116])).

fof(f114,plain,
    ( l1_struct_0(sK0)
    | ~ spl5_3 ),
    inference(resolution,[],[f74,f102])).

fof(f74,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f113,plain,(
    ~ spl5_5 ),
    inference(avatar_split_clause,[],[f53,f110])).

fof(f53,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ~ v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f38,f37])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v2_tex_2(k6_domain_1(u1_struct_0(sK0),X1),sK0)
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X1] :
        ( ~ v2_tex_2(k6_domain_1(u1_struct_0(sK0),X1),sK0)
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ~ v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0)
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
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
            ( m1_subset_1(X1,u1_struct_0(X0))
           => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

fof(f108,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f54,f105])).

fof(f54,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f103,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f55,f100])).

fof(f55,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f98,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f56,f95])).

fof(f56,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f93,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f57,f90])).

fof(f57,plain,(
    ~ v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:54:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (11164)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.52  % (11152)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.52  % (11149)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.52  % (11142)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.53  % (11162)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.53  % (11144)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.53  % (11146)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (11153)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.53  % (11143)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.53  % (11150)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.53  % (11140)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.53  % (11166)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (11168)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.54  % (11151)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.54  % (11150)Refutation not found, incomplete strategy% (11150)------------------------------
% 0.22/0.54  % (11150)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (11158)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.54  % (11145)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.54  % (11163)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.54  % (11160)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.54  % (11150)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (11150)Memory used [KB]: 10746
% 0.22/0.54  % (11150)Time elapsed: 0.109 s
% 0.22/0.54  % (11150)------------------------------
% 0.22/0.54  % (11150)------------------------------
% 0.22/0.54  % (11167)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.54  % (11154)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.54  % (11155)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.54  % (11161)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.55  % (11157)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.55  % (11152)Refutation not found, incomplete strategy% (11152)------------------------------
% 0.22/0.55  % (11152)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (11152)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (11152)Memory used [KB]: 10618
% 0.22/0.55  % (11152)Time elapsed: 0.003 s
% 0.22/0.55  % (11152)------------------------------
% 0.22/0.55  % (11152)------------------------------
% 0.22/0.55  % (11159)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.55  % (11168)Refutation not found, incomplete strategy% (11168)------------------------------
% 0.22/0.55  % (11168)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (11168)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (11168)Memory used [KB]: 10746
% 0.22/0.55  % (11168)Time elapsed: 0.118 s
% 0.22/0.55  % (11168)------------------------------
% 0.22/0.55  % (11168)------------------------------
% 0.22/0.55  % (11157)Refutation not found, incomplete strategy% (11157)------------------------------
% 0.22/0.55  % (11157)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (11141)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.55  % (11147)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.55  % (11156)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.55  % (11148)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.55  % (11166)Refutation not found, incomplete strategy% (11166)------------------------------
% 0.22/0.55  % (11166)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (11169)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.56  % (11169)Refutation not found, incomplete strategy% (11169)------------------------------
% 0.22/0.56  % (11169)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (11169)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (11169)Memory used [KB]: 1663
% 0.22/0.56  % (11169)Time elapsed: 0.005 s
% 0.22/0.56  % (11169)------------------------------
% 0.22/0.56  % (11169)------------------------------
% 1.47/0.56  % (11165)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.47/0.56  % (11165)Refutation not found, incomplete strategy% (11165)------------------------------
% 1.47/0.56  % (11165)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (11165)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.56  
% 1.47/0.56  % (11165)Memory used [KB]: 6268
% 1.47/0.56  % (11165)Time elapsed: 0.147 s
% 1.47/0.56  % (11165)------------------------------
% 1.47/0.56  % (11165)------------------------------
% 1.47/0.56  % (11141)Refutation not found, incomplete strategy% (11141)------------------------------
% 1.47/0.56  % (11141)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (11141)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.56  
% 1.47/0.56  % (11141)Memory used [KB]: 1663
% 1.47/0.56  % (11141)Time elapsed: 0.116 s
% 1.47/0.56  % (11141)------------------------------
% 1.47/0.56  % (11141)------------------------------
% 1.47/0.56  % (11167)Refutation not found, incomplete strategy% (11167)------------------------------
% 1.47/0.56  % (11167)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (11167)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.56  
% 1.47/0.56  % (11167)Memory used [KB]: 6268
% 1.47/0.56  % (11167)Time elapsed: 0.146 s
% 1.47/0.56  % (11167)------------------------------
% 1.47/0.56  % (11167)------------------------------
% 1.47/0.56  % (11157)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.56  
% 1.47/0.56  % (11157)Memory used [KB]: 1791
% 1.47/0.56  % (11157)Time elapsed: 0.135 s
% 1.47/0.56  % (11157)------------------------------
% 1.47/0.56  % (11157)------------------------------
% 1.47/0.57  % (11156)Refutation not found, incomplete strategy% (11156)------------------------------
% 1.47/0.57  % (11156)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.57  % (11156)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.57  
% 1.47/0.57  % (11156)Memory used [KB]: 10618
% 1.47/0.57  % (11156)Time elapsed: 0.152 s
% 1.47/0.57  % (11156)------------------------------
% 1.47/0.57  % (11156)------------------------------
% 1.64/0.58  % (11166)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.58  
% 1.64/0.58  % (11166)Memory used [KB]: 6780
% 1.64/0.58  % (11166)Time elapsed: 0.130 s
% 1.64/0.58  % (11166)------------------------------
% 1.64/0.58  % (11166)------------------------------
% 1.96/0.64  % (11161)Refutation found. Thanks to Tanya!
% 1.96/0.64  % SZS status Theorem for theBenchmark
% 2.09/0.66  % SZS output start Proof for theBenchmark
% 2.09/0.66  fof(f1113,plain,(
% 2.09/0.66    $false),
% 2.09/0.66    inference(avatar_sat_refutation,[],[f93,f98,f103,f108,f113,f119,f164,f941,f1043,f1072,f1080,f1096,f1099,f1104,f1112])).
% 2.09/0.66  fof(f1112,plain,(
% 2.09/0.66    ~spl5_2 | ~spl5_3 | spl5_5 | spl5_7 | ~spl5_12),
% 2.09/0.66    inference(avatar_contradiction_clause,[],[f1111])).
% 2.09/0.66  fof(f1111,plain,(
% 2.09/0.66    $false | (~spl5_2 | ~spl5_3 | spl5_5 | spl5_7 | ~spl5_12)),
% 2.09/0.66    inference(subsumption_resolution,[],[f1110,f126])).
% 2.09/0.66  fof(f126,plain,(
% 2.09/0.66    ~v1_xboole_0(u1_struct_0(sK0)) | spl5_7),
% 2.09/0.66    inference(avatar_component_clause,[],[f124])).
% 2.09/0.66  fof(f124,plain,(
% 2.09/0.66    spl5_7 <=> v1_xboole_0(u1_struct_0(sK0))),
% 2.09/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 2.09/0.66  fof(f1110,plain,(
% 2.09/0.66    v1_xboole_0(u1_struct_0(sK0)) | (~spl5_2 | ~spl5_3 | spl5_5 | ~spl5_12)),
% 2.09/0.66    inference(subsumption_resolution,[],[f1109,f97])).
% 2.09/0.66  fof(f97,plain,(
% 2.09/0.66    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl5_2),
% 2.09/0.66    inference(avatar_component_clause,[],[f95])).
% 2.09/0.66  fof(f95,plain,(
% 2.09/0.66    spl5_2 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 2.09/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.09/0.66  fof(f1109,plain,(
% 2.09/0.66    ~m1_subset_1(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | (~spl5_3 | spl5_5 | ~spl5_12)),
% 2.09/0.66    inference(subsumption_resolution,[],[f1108,f112])).
% 2.09/0.66  fof(f112,plain,(
% 2.09/0.66    ~v2_struct_0(sK0) | spl5_5),
% 2.09/0.66    inference(avatar_component_clause,[],[f110])).
% 2.09/0.66  fof(f110,plain,(
% 2.09/0.66    spl5_5 <=> v2_struct_0(sK0)),
% 2.09/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 2.09/0.66  fof(f1108,plain,(
% 2.09/0.66    v2_struct_0(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | (~spl5_3 | ~spl5_12)),
% 2.09/0.66    inference(subsumption_resolution,[],[f1106,f102])).
% 2.09/0.66  fof(f102,plain,(
% 2.09/0.66    l1_pre_topc(sK0) | ~spl5_3),
% 2.09/0.66    inference(avatar_component_clause,[],[f100])).
% 2.09/0.66  fof(f100,plain,(
% 2.09/0.66    spl5_3 <=> l1_pre_topc(sK0)),
% 2.09/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.09/0.66  fof(f1106,plain,(
% 2.09/0.66    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | ~spl5_12),
% 2.09/0.66    inference(resolution,[],[f247,f966])).
% 2.09/0.66  fof(f966,plain,(
% 2.09/0.66    ( ! [X2,X3] : (~v2_struct_0(k1_tex_2(X2,X3)) | ~l1_pre_topc(X2) | v2_struct_0(X2) | ~m1_subset_1(X3,u1_struct_0(X2)) | v1_xboole_0(u1_struct_0(X2))) )),
% 2.09/0.66    inference(subsumption_resolution,[],[f958,f120])).
% 2.09/0.66  fof(f120,plain,(
% 2.09/0.66    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 2.09/0.66    inference(resolution,[],[f80,f87])).
% 2.09/0.66  fof(f87,plain,(
% 2.09/0.66    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 2.09/0.66    inference(equality_resolution,[],[f86])).
% 2.09/0.66  fof(f86,plain,(
% 2.09/0.66    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 2.09/0.66    inference(equality_resolution,[],[f77])).
% 2.09/0.66  fof(f77,plain,(
% 2.09/0.66    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 2.09/0.66    inference(cnf_transformation,[],[f48])).
% 2.09/0.66  fof(f48,plain,(
% 2.09/0.66    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.09/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f46,f47])).
% 2.09/0.66  fof(f47,plain,(
% 2.09/0.66    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 2.09/0.66    introduced(choice_axiom,[])).
% 2.09/0.66  fof(f46,plain,(
% 2.09/0.66    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.09/0.66    inference(rectify,[],[f45])).
% 2.09/0.66  fof(f45,plain,(
% 2.09/0.66    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.09/0.66    inference(nnf_transformation,[],[f2])).
% 2.09/0.66  fof(f2,axiom,(
% 2.09/0.66    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.09/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 2.09/0.66  fof(f80,plain,(
% 2.09/0.66    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.09/0.66    inference(cnf_transformation,[],[f52])).
% 2.09/0.66  fof(f52,plain,(
% 2.09/0.66    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.09/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f50,f51])).
% 2.09/0.66  fof(f51,plain,(
% 2.09/0.66    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 2.09/0.66    introduced(choice_axiom,[])).
% 2.09/0.66  fof(f50,plain,(
% 2.09/0.66    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.09/0.66    inference(rectify,[],[f49])).
% 2.09/0.66  fof(f49,plain,(
% 2.09/0.66    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.09/0.66    inference(nnf_transformation,[],[f1])).
% 2.09/0.66  fof(f1,axiom,(
% 2.09/0.66    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.09/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 2.09/0.66  fof(f958,plain,(
% 2.09/0.66    ( ! [X2,X3] : (v1_xboole_0(k1_tarski(X3)) | ~v2_struct_0(k1_tex_2(X2,X3)) | ~l1_pre_topc(X2) | v2_struct_0(X2) | ~m1_subset_1(X3,u1_struct_0(X2)) | v1_xboole_0(u1_struct_0(X2))) )),
% 2.09/0.66    inference(duplicate_literal_removal,[],[f957])).
% 2.09/0.66  fof(f957,plain,(
% 2.09/0.66    ( ! [X2,X3] : (v1_xboole_0(k1_tarski(X3)) | ~v2_struct_0(k1_tex_2(X2,X3)) | ~l1_pre_topc(X2) | v2_struct_0(X2) | ~m1_subset_1(X3,u1_struct_0(X2)) | v1_xboole_0(u1_struct_0(X2)) | ~m1_subset_1(X3,u1_struct_0(X2)) | v1_xboole_0(u1_struct_0(X2))) )),
% 2.09/0.66    inference(superposition,[],[f883,f61])).
% 2.09/0.66  fof(f61,plain,(
% 2.09/0.66    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.09/0.66    inference(cnf_transformation,[],[f24])).
% 2.09/0.66  fof(f24,plain,(
% 2.09/0.66    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.09/0.66    inference(flattening,[],[f23])).
% 2.09/0.66  fof(f23,plain,(
% 2.09/0.66    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.09/0.66    inference(ennf_transformation,[],[f9])).
% 2.09/0.66  fof(f9,axiom,(
% 2.09/0.66    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 2.09/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 2.09/0.66  fof(f883,plain,(
% 2.09/0.66    ( ! [X10,X11] : (v1_xboole_0(k6_domain_1(u1_struct_0(X10),X11)) | ~v2_struct_0(k1_tex_2(X10,X11)) | ~l1_pre_topc(X10) | v2_struct_0(X10) | ~m1_subset_1(X11,u1_struct_0(X10)) | v1_xboole_0(u1_struct_0(X10))) )),
% 2.09/0.66    inference(subsumption_resolution,[],[f882,f60])).
% 2.09/0.66  fof(f60,plain,(
% 2.09/0.66    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.09/0.66    inference(cnf_transformation,[],[f22])).
% 2.09/0.66  fof(f22,plain,(
% 2.09/0.66    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.09/0.66    inference(flattening,[],[f21])).
% 2.09/0.66  fof(f21,plain,(
% 2.09/0.66    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.09/0.66    inference(ennf_transformation,[],[f8])).
% 2.09/0.66  fof(f8,axiom,(
% 2.09/0.66    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.09/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 2.09/0.66  fof(f882,plain,(
% 2.09/0.66    ( ! [X10,X11] : (~v2_struct_0(k1_tex_2(X10,X11)) | v1_xboole_0(k6_domain_1(u1_struct_0(X10),X11)) | ~l1_pre_topc(X10) | v2_struct_0(X10) | ~m1_subset_1(X11,u1_struct_0(X10)) | v1_xboole_0(u1_struct_0(X10)) | ~m1_subset_1(k6_domain_1(u1_struct_0(X10),X11),k1_zfmisc_1(u1_struct_0(X10)))) )),
% 2.09/0.66    inference(subsumption_resolution,[],[f860,f203])).
% 2.09/0.66  fof(f203,plain,(
% 2.09/0.66    ( ! [X4,X5] : (m1_pre_topc(sK2(X4,k6_domain_1(u1_struct_0(X4),X5)),X4) | v1_xboole_0(k6_domain_1(u1_struct_0(X4),X5)) | ~l1_pre_topc(X4) | v2_struct_0(X4) | ~m1_subset_1(X5,u1_struct_0(X4)) | v1_xboole_0(u1_struct_0(X4))) )),
% 2.09/0.66    inference(resolution,[],[f70,f60])).
% 2.09/0.66  fof(f70,plain,(
% 2.09/0.66    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_pre_topc(sK2(X0,X1),X0) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.09/0.66    inference(cnf_transformation,[],[f44])).
% 2.09/0.66  fof(f44,plain,(
% 2.09/0.66    ! [X0] : (! [X1] : ((u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & v1_pre_topc(sK2(X0,X1)) & ~v2_struct_0(sK2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.09/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f43])).
% 2.09/0.66  fof(f43,plain,(
% 2.09/0.66    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => (u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & v1_pre_topc(sK2(X0,X1)) & ~v2_struct_0(sK2(X0,X1))))),
% 2.09/0.66    introduced(choice_axiom,[])).
% 2.09/0.66  fof(f29,plain,(
% 2.09/0.66    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.09/0.66    inference(flattening,[],[f28])).
% 2.09/0.66  fof(f28,plain,(
% 2.09/0.66    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.09/0.66    inference(ennf_transformation,[],[f11])).
% 2.09/0.66  fof(f11,axiom,(
% 2.09/0.66    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 2.09/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tsep_1)).
% 2.09/0.66  fof(f860,plain,(
% 2.09/0.66    ( ! [X10,X11] : (~v2_struct_0(k1_tex_2(X10,X11)) | v1_xboole_0(k6_domain_1(u1_struct_0(X10),X11)) | ~l1_pre_topc(X10) | v2_struct_0(X10) | ~m1_subset_1(X11,u1_struct_0(X10)) | v1_xboole_0(u1_struct_0(X10)) | ~m1_pre_topc(sK2(X10,k6_domain_1(u1_struct_0(X10),X11)),X10) | ~m1_subset_1(k6_domain_1(u1_struct_0(X10),X11),k1_zfmisc_1(u1_struct_0(X10)))) )),
% 2.09/0.66    inference(duplicate_literal_removal,[],[f791])).
% 2.09/0.66  fof(f791,plain,(
% 2.09/0.66    ( ! [X10,X11] : (~v2_struct_0(k1_tex_2(X10,X11)) | v1_xboole_0(k6_domain_1(u1_struct_0(X10),X11)) | ~l1_pre_topc(X10) | v2_struct_0(X10) | ~m1_subset_1(X11,u1_struct_0(X10)) | v1_xboole_0(u1_struct_0(X10)) | ~m1_pre_topc(sK2(X10,k6_domain_1(u1_struct_0(X10),X11)),X10) | ~m1_subset_1(X11,u1_struct_0(X10)) | ~l1_pre_topc(X10) | v2_struct_0(X10) | ~m1_subset_1(k6_domain_1(u1_struct_0(X10),X11),k1_zfmisc_1(u1_struct_0(X10))) | v1_xboole_0(k6_domain_1(u1_struct_0(X10),X11)) | ~l1_pre_topc(X10) | v2_struct_0(X10)) )),
% 2.09/0.66    inference(superposition,[],[f173,f433])).
% 2.09/0.66  fof(f433,plain,(
% 2.09/0.66    ( ! [X2,X0,X1] : (k1_tex_2(X1,X2) = sK2(X0,k6_domain_1(u1_struct_0(X1),X2)) | ~m1_pre_topc(sK2(X0,k6_domain_1(u1_struct_0(X1),X2)),X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_pre_topc(X1) | v2_struct_0(X1) | ~m1_subset_1(k6_domain_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(k6_domain_1(u1_struct_0(X1),X2)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.09/0.66    inference(equality_resolution,[],[f228])).
% 2.09/0.66  fof(f228,plain,(
% 2.09/0.66    ( ! [X2,X0,X3,X1] : (k6_domain_1(u1_struct_0(X2),X3) != X1 | sK2(X0,X1) = k1_tex_2(X2,X3) | ~m1_pre_topc(sK2(X0,X1),X2) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_pre_topc(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.09/0.66    inference(subsumption_resolution,[],[f227,f69])).
% 2.09/0.66  fof(f69,plain,(
% 2.09/0.66    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_pre_topc(sK2(X0,X1)) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.09/0.66    inference(cnf_transformation,[],[f44])).
% 2.09/0.66  fof(f227,plain,(
% 2.09/0.66    ( ! [X2,X0,X3,X1] : (k6_domain_1(u1_struct_0(X2),X3) != X1 | sK2(X0,X1) = k1_tex_2(X2,X3) | ~m1_pre_topc(sK2(X0,X1),X2) | ~v1_pre_topc(sK2(X0,X1)) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_pre_topc(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.09/0.66    inference(subsumption_resolution,[],[f223,f68])).
% 2.09/0.66  fof(f68,plain,(
% 2.09/0.66    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_struct_0(sK2(X0,X1)) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.09/0.66    inference(cnf_transformation,[],[f44])).
% 2.09/0.66  fof(f223,plain,(
% 2.09/0.66    ( ! [X2,X0,X3,X1] : (k6_domain_1(u1_struct_0(X2),X3) != X1 | sK2(X0,X1) = k1_tex_2(X2,X3) | ~m1_pre_topc(sK2(X0,X1),X2) | ~v1_pre_topc(sK2(X0,X1)) | v2_struct_0(sK2(X0,X1)) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_pre_topc(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.09/0.66    inference(superposition,[],[f63,f71])).
% 2.09/0.66  fof(f71,plain,(
% 2.09/0.66    ( ! [X0,X1] : (u1_struct_0(sK2(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.09/0.66    inference(cnf_transformation,[],[f44])).
% 2.09/0.66  fof(f63,plain,(
% 2.09/0.66    ( ! [X2,X0,X1] : (u1_struct_0(X2) != k6_domain_1(u1_struct_0(X0),X1) | k1_tex_2(X0,X1) = X2 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.09/0.66    inference(cnf_transformation,[],[f41])).
% 2.09/0.66  fof(f41,plain,(
% 2.09/0.66    ! [X0] : (! [X1] : (! [X2] : (((k1_tex_2(X0,X1) = X2 | u1_struct_0(X2) != k6_domain_1(u1_struct_0(X0),X1)) & (u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) | k1_tex_2(X0,X1) != X2)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.09/0.66    inference(nnf_transformation,[],[f26])).
% 2.09/0.66  fof(f26,plain,(
% 2.09/0.66    ! [X0] : (! [X1] : (! [X2] : ((k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.09/0.66    inference(flattening,[],[f25])).
% 2.09/0.66  fof(f25,plain,(
% 2.09/0.66    ! [X0] : (! [X1] : (! [X2] : ((k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.09/0.66    inference(ennf_transformation,[],[f10])).
% 2.09/0.66  fof(f10,axiom,(
% 2.09/0.66    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => (k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)))))),
% 2.09/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tex_2)).
% 2.09/0.66  fof(f173,plain,(
% 2.09/0.66    ( ! [X2,X3] : (~v2_struct_0(sK2(X2,k6_domain_1(u1_struct_0(X2),X3))) | v1_xboole_0(k6_domain_1(u1_struct_0(X2),X3)) | ~l1_pre_topc(X2) | v2_struct_0(X2) | ~m1_subset_1(X3,u1_struct_0(X2)) | v1_xboole_0(u1_struct_0(X2))) )),
% 2.09/0.66    inference(resolution,[],[f68,f60])).
% 2.09/0.66  fof(f247,plain,(
% 2.09/0.66    v2_struct_0(k1_tex_2(sK0,sK1)) | ~spl5_12),
% 2.09/0.66    inference(avatar_component_clause,[],[f245])).
% 2.09/0.66  fof(f245,plain,(
% 2.09/0.66    spl5_12 <=> v2_struct_0(k1_tex_2(sK0,sK1))),
% 2.09/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 2.09/0.66  fof(f1104,plain,(
% 2.09/0.66    spl5_17 | ~spl5_2 | ~spl5_3 | spl5_5 | ~spl5_18),
% 2.09/0.66    inference(avatar_split_clause,[],[f1103,f1063,f110,f100,f95,f1056])).
% 2.09/0.66  fof(f1056,plain,(
% 2.09/0.66    spl5_17 <=> v1_tdlat_3(k1_tex_2(sK0,sK1))),
% 2.09/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 2.09/0.66  fof(f1063,plain,(
% 2.09/0.66    spl5_18 <=> v2_pre_topc(k1_tex_2(sK0,sK1))),
% 2.09/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 2.09/0.66  fof(f1103,plain,(
% 2.09/0.66    v1_tdlat_3(k1_tex_2(sK0,sK1)) | (~spl5_2 | ~spl5_3 | spl5_5 | ~spl5_18)),
% 2.09/0.66    inference(subsumption_resolution,[],[f1102,f112])).
% 2.09/0.66  fof(f1102,plain,(
% 2.09/0.66    v1_tdlat_3(k1_tex_2(sK0,sK1)) | v2_struct_0(sK0) | (~spl5_2 | ~spl5_3 | ~spl5_18)),
% 2.09/0.66    inference(subsumption_resolution,[],[f1101,f102])).
% 2.09/0.66  fof(f1101,plain,(
% 2.09/0.66    v1_tdlat_3(k1_tex_2(sK0,sK1)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_2 | ~spl5_18)),
% 2.09/0.66    inference(subsumption_resolution,[],[f1100,f97])).
% 2.09/0.66  fof(f1100,plain,(
% 2.09/0.66    v1_tdlat_3(k1_tex_2(sK0,sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_18),
% 2.09/0.66    inference(resolution,[],[f1065,f75])).
% 2.09/0.66  fof(f75,plain,(
% 2.09/0.66    ( ! [X0,X1] : (~v2_pre_topc(k1_tex_2(X0,X1)) | v1_tdlat_3(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.09/0.66    inference(cnf_transformation,[],[f36])).
% 2.09/0.66  fof(f36,plain,(
% 2.09/0.66    ! [X0] : (! [X1] : (v1_tdlat_3(k1_tex_2(X0,X1)) | ~v2_pre_topc(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.09/0.66    inference(flattening,[],[f35])).
% 2.09/0.66  fof(f35,plain,(
% 2.09/0.66    ! [X0] : (! [X1] : ((v1_tdlat_3(k1_tex_2(X0,X1)) | ~v2_pre_topc(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.09/0.66    inference(ennf_transformation,[],[f16])).
% 2.09/0.66  fof(f16,plain,(
% 2.09/0.66    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v2_pre_topc(k1_tex_2(X0,X1)) => v1_tdlat_3(k1_tex_2(X0,X1)))))),
% 2.09/0.66    inference(pure_predicate_removal,[],[f12])).
% 2.09/0.66  fof(f12,axiom,(
% 2.09/0.66    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v2_pre_topc(k1_tex_2(X0,X1)) => (v2_tdlat_3(k1_tex_2(X0,X1)) & v1_tdlat_3(k1_tex_2(X0,X1))))))),
% 2.09/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tex_2)).
% 2.09/0.66  fof(f1065,plain,(
% 2.09/0.66    v2_pre_topc(k1_tex_2(sK0,sK1)) | ~spl5_18),
% 2.09/0.66    inference(avatar_component_clause,[],[f1063])).
% 2.09/0.66  fof(f1099,plain,(
% 2.09/0.66    spl5_18 | ~spl5_3 | ~spl5_4 | ~spl5_14),
% 2.09/0.66    inference(avatar_split_clause,[],[f1098,f253,f105,f100,f1063])).
% 2.09/0.66  fof(f105,plain,(
% 2.09/0.66    spl5_4 <=> v2_pre_topc(sK0)),
% 2.09/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 2.09/0.66  fof(f253,plain,(
% 2.09/0.66    spl5_14 <=> m1_pre_topc(k1_tex_2(sK0,sK1),sK0)),
% 2.09/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 2.09/0.66  fof(f1098,plain,(
% 2.09/0.66    v2_pre_topc(k1_tex_2(sK0,sK1)) | (~spl5_3 | ~spl5_4 | ~spl5_14)),
% 2.09/0.66    inference(subsumption_resolution,[],[f1097,f107])).
% 2.09/0.66  fof(f107,plain,(
% 2.09/0.66    v2_pre_topc(sK0) | ~spl5_4),
% 2.09/0.66    inference(avatar_component_clause,[],[f105])).
% 2.09/0.66  fof(f1097,plain,(
% 2.09/0.66    v2_pre_topc(k1_tex_2(sK0,sK1)) | ~v2_pre_topc(sK0) | (~spl5_3 | ~spl5_14)),
% 2.09/0.66    inference(subsumption_resolution,[],[f1089,f102])).
% 2.09/0.66  fof(f1089,plain,(
% 2.09/0.66    v2_pre_topc(k1_tex_2(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl5_14),
% 2.09/0.66    inference(resolution,[],[f254,f73])).
% 2.09/0.66  fof(f73,plain,(
% 2.09/0.66    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.09/0.66    inference(cnf_transformation,[],[f33])).
% 2.09/0.66  fof(f33,plain,(
% 2.09/0.66    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.09/0.66    inference(flattening,[],[f32])).
% 2.09/0.66  fof(f32,plain,(
% 2.09/0.66    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.09/0.66    inference(ennf_transformation,[],[f5])).
% 2.09/0.66  fof(f5,axiom,(
% 2.09/0.66    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.09/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 2.09/0.66  fof(f254,plain,(
% 2.09/0.66    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~spl5_14),
% 2.09/0.66    inference(avatar_component_clause,[],[f253])).
% 2.09/0.66  fof(f1096,plain,(
% 2.09/0.66    ~spl5_17 | spl5_12 | ~spl5_2 | ~spl5_3 | spl5_5 | spl5_7 | spl5_10 | ~spl5_13 | ~spl5_14),
% 2.09/0.66    inference(avatar_split_clause,[],[f1095,f253,f249,f161,f124,f110,f100,f95,f245,f1056])).
% 2.09/0.66  fof(f161,plain,(
% 2.09/0.66    spl5_10 <=> v2_tex_2(k1_tarski(sK1),sK0)),
% 2.09/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 2.09/0.66  fof(f249,plain,(
% 2.09/0.66    spl5_13 <=> v1_pre_topc(k1_tex_2(sK0,sK1))),
% 2.09/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 2.09/0.66  fof(f1095,plain,(
% 2.09/0.66    v2_struct_0(k1_tex_2(sK0,sK1)) | ~v1_tdlat_3(k1_tex_2(sK0,sK1)) | (~spl5_2 | ~spl5_3 | spl5_5 | spl5_7 | spl5_10 | ~spl5_13 | ~spl5_14)),
% 2.09/0.66    inference(subsumption_resolution,[],[f1094,f97])).
% 2.09/0.66  fof(f1094,plain,(
% 2.09/0.66    v2_struct_0(k1_tex_2(sK0,sK1)) | ~v1_tdlat_3(k1_tex_2(sK0,sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (~spl5_3 | spl5_5 | spl5_7 | spl5_10 | ~spl5_13 | ~spl5_14)),
% 2.09/0.66    inference(subsumption_resolution,[],[f1093,f112])).
% 2.09/0.66  fof(f1093,plain,(
% 2.09/0.66    v2_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(sK0) | ~v1_tdlat_3(k1_tex_2(sK0,sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (~spl5_3 | spl5_7 | spl5_10 | ~spl5_13 | ~spl5_14)),
% 2.09/0.66    inference(subsumption_resolution,[],[f1092,f102])).
% 2.09/0.66  fof(f1092,plain,(
% 2.09/0.66    v2_struct_0(k1_tex_2(sK0,sK1)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v1_tdlat_3(k1_tex_2(sK0,sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (spl5_7 | spl5_10 | ~spl5_13 | ~spl5_14)),
% 2.09/0.66    inference(subsumption_resolution,[],[f1091,f250])).
% 2.09/0.66  fof(f250,plain,(
% 2.09/0.66    v1_pre_topc(k1_tex_2(sK0,sK1)) | ~spl5_13),
% 2.09/0.66    inference(avatar_component_clause,[],[f249])).
% 2.09/0.66  fof(f1091,plain,(
% 2.09/0.66    ~v1_pre_topc(k1_tex_2(sK0,sK1)) | v2_struct_0(k1_tex_2(sK0,sK1)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v1_tdlat_3(k1_tex_2(sK0,sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (spl5_7 | spl5_10 | ~spl5_14)),
% 2.09/0.66    inference(subsumption_resolution,[],[f1090,f163])).
% 2.09/0.66  fof(f163,plain,(
% 2.09/0.66    ~v2_tex_2(k1_tarski(sK1),sK0) | spl5_10),
% 2.09/0.66    inference(avatar_component_clause,[],[f161])).
% 2.09/0.66  fof(f1090,plain,(
% 2.09/0.66    v2_tex_2(k1_tarski(sK1),sK0) | ~v1_pre_topc(k1_tex_2(sK0,sK1)) | v2_struct_0(k1_tex_2(sK0,sK1)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v1_tdlat_3(k1_tex_2(sK0,sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (spl5_7 | ~spl5_14)),
% 2.09/0.66    inference(subsumption_resolution,[],[f1088,f126])).
% 2.09/0.66  fof(f1088,plain,(
% 2.09/0.66    v1_xboole_0(u1_struct_0(sK0)) | v2_tex_2(k1_tarski(sK1),sK0) | ~v1_pre_topc(k1_tex_2(sK0,sK1)) | v2_struct_0(k1_tex_2(sK0,sK1)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v1_tdlat_3(k1_tex_2(sK0,sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl5_14),
% 2.09/0.66    inference(resolution,[],[f254,f677])).
% 2.09/0.66  fof(f677,plain,(
% 2.09/0.66    ( ! [X0,X1] : (~m1_pre_topc(k1_tex_2(X0,X1),X0) | v1_xboole_0(u1_struct_0(X0)) | v2_tex_2(k1_tarski(X1),X0) | ~v1_pre_topc(k1_tex_2(X0,X1)) | v2_struct_0(k1_tex_2(X0,X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v1_tdlat_3(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) )),
% 2.09/0.66    inference(duplicate_literal_removal,[],[f674])).
% 2.09/0.66  fof(f674,plain,(
% 2.09/0.66    ( ! [X0,X1] : (v2_tex_2(k1_tarski(X1),X0) | v1_xboole_0(u1_struct_0(X0)) | ~m1_pre_topc(k1_tex_2(X0,X1),X0) | ~v1_pre_topc(k1_tex_2(X0,X1)) | v2_struct_0(k1_tex_2(X0,X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v1_tdlat_3(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | v1_xboole_0(u1_struct_0(X0)) | ~m1_pre_topc(k1_tex_2(X0,X1),X0) | ~v1_pre_topc(k1_tex_2(X0,X1)) | v2_struct_0(k1_tex_2(X0,X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.09/0.66    inference(superposition,[],[f400,f237])).
% 2.09/0.66  fof(f237,plain,(
% 2.09/0.66    ( ! [X4,X3] : (k1_tarski(X4) = u1_struct_0(k1_tex_2(X3,X4)) | ~m1_subset_1(X4,u1_struct_0(X3)) | v1_xboole_0(u1_struct_0(X3)) | ~m1_pre_topc(k1_tex_2(X3,X4),X3) | ~v1_pre_topc(k1_tex_2(X3,X4)) | v2_struct_0(k1_tex_2(X3,X4)) | ~l1_pre_topc(X3) | v2_struct_0(X3)) )),
% 2.09/0.66    inference(duplicate_literal_removal,[],[f234])).
% 2.09/0.66  fof(f234,plain,(
% 2.09/0.66    ( ! [X4,X3] : (k1_tarski(X4) = u1_struct_0(k1_tex_2(X3,X4)) | ~m1_subset_1(X4,u1_struct_0(X3)) | v1_xboole_0(u1_struct_0(X3)) | ~m1_pre_topc(k1_tex_2(X3,X4),X3) | ~v1_pre_topc(k1_tex_2(X3,X4)) | v2_struct_0(k1_tex_2(X3,X4)) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~l1_pre_topc(X3) | v2_struct_0(X3)) )),
% 2.09/0.66    inference(superposition,[],[f61,f85])).
% 2.09/0.66  fof(f85,plain,(
% 2.09/0.66    ( ! [X0,X1] : (k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) | ~m1_pre_topc(k1_tex_2(X0,X1),X0) | ~v1_pre_topc(k1_tex_2(X0,X1)) | v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.09/0.66    inference(equality_resolution,[],[f62])).
% 2.09/0.66  fof(f62,plain,(
% 2.09/0.66    ( ! [X2,X0,X1] : (u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) | k1_tex_2(X0,X1) != X2 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.09/0.66    inference(cnf_transformation,[],[f41])).
% 2.09/0.66  fof(f400,plain,(
% 2.09/0.66    ( ! [X2,X3] : (v2_tex_2(u1_struct_0(k1_tex_2(X3,X2)),X3) | v1_xboole_0(u1_struct_0(X3)) | ~m1_pre_topc(k1_tex_2(X3,X2),X3) | ~v1_pre_topc(k1_tex_2(X3,X2)) | v2_struct_0(k1_tex_2(X3,X2)) | ~l1_pre_topc(X3) | v2_struct_0(X3) | ~v1_tdlat_3(k1_tex_2(X3,X2)) | ~m1_subset_1(X2,u1_struct_0(X3))) )),
% 2.09/0.66    inference(duplicate_literal_removal,[],[f385])).
% 2.09/0.66  fof(f385,plain,(
% 2.09/0.66    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(X3)) | v1_xboole_0(u1_struct_0(X3)) | ~m1_pre_topc(k1_tex_2(X3,X2),X3) | ~v1_pre_topc(k1_tex_2(X3,X2)) | v2_struct_0(k1_tex_2(X3,X2)) | ~l1_pre_topc(X3) | v2_struct_0(X3) | ~v1_tdlat_3(k1_tex_2(X3,X2)) | v2_tex_2(u1_struct_0(k1_tex_2(X3,X2)),X3) | ~m1_pre_topc(k1_tex_2(X3,X2),X3) | v2_struct_0(k1_tex_2(X3,X2)) | ~l1_pre_topc(X3) | v2_struct_0(X3)) )),
% 2.09/0.66    inference(resolution,[],[f236,f83])).
% 2.09/0.66  fof(f83,plain,(
% 2.09/0.66    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X1) | v2_tex_2(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.09/0.66    inference(equality_resolution,[],[f59])).
% 2.09/0.66  fof(f59,plain,(
% 2.09/0.66    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v1_tdlat_3(X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.09/0.66    inference(cnf_transformation,[],[f40])).
% 2.09/0.66  fof(f40,plain,(
% 2.09/0.66    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) | ~v1_tdlat_3(X1)) & (v1_tdlat_3(X1) | ~v2_tex_2(X2,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.09/0.66    inference(nnf_transformation,[],[f20])).
% 2.09/0.66  fof(f20,plain,(
% 2.09/0.66    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.09/0.66    inference(flattening,[],[f19])).
% 2.09/0.66  fof(f19,plain,(
% 2.09/0.66    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.09/0.66    inference(ennf_transformation,[],[f13])).
% 2.09/0.66  fof(f13,axiom,(
% 2.09/0.66    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 2.09/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).
% 2.09/0.66  fof(f236,plain,(
% 2.09/0.66    ( ! [X6,X5] : (m1_subset_1(u1_struct_0(k1_tex_2(X5,X6)),k1_zfmisc_1(u1_struct_0(X5))) | ~m1_subset_1(X6,u1_struct_0(X5)) | v1_xboole_0(u1_struct_0(X5)) | ~m1_pre_topc(k1_tex_2(X5,X6),X5) | ~v1_pre_topc(k1_tex_2(X5,X6)) | v2_struct_0(k1_tex_2(X5,X6)) | ~l1_pre_topc(X5) | v2_struct_0(X5)) )),
% 2.09/0.66    inference(duplicate_literal_removal,[],[f235])).
% 2.09/0.66  fof(f235,plain,(
% 2.09/0.66    ( ! [X6,X5] : (m1_subset_1(u1_struct_0(k1_tex_2(X5,X6)),k1_zfmisc_1(u1_struct_0(X5))) | ~m1_subset_1(X6,u1_struct_0(X5)) | v1_xboole_0(u1_struct_0(X5)) | ~m1_pre_topc(k1_tex_2(X5,X6),X5) | ~v1_pre_topc(k1_tex_2(X5,X6)) | v2_struct_0(k1_tex_2(X5,X6)) | ~m1_subset_1(X6,u1_struct_0(X5)) | ~l1_pre_topc(X5) | v2_struct_0(X5)) )),
% 2.09/0.66    inference(superposition,[],[f60,f85])).
% 2.09/0.66  fof(f1080,plain,(
% 2.09/0.66    ~spl5_2 | spl5_7 | ~spl5_16),
% 2.09/0.66    inference(avatar_contradiction_clause,[],[f1079])).
% 2.09/0.66  fof(f1079,plain,(
% 2.09/0.66    $false | (~spl5_2 | spl5_7 | ~spl5_16)),
% 2.09/0.66    inference(subsumption_resolution,[],[f1078,f126])).
% 2.09/0.66  fof(f1078,plain,(
% 2.09/0.66    v1_xboole_0(u1_struct_0(sK0)) | (~spl5_2 | ~spl5_16)),
% 2.09/0.66    inference(subsumption_resolution,[],[f1077,f97])).
% 2.09/0.66  fof(f1077,plain,(
% 2.09/0.66    ~m1_subset_1(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | ~spl5_16),
% 2.09/0.66    inference(subsumption_resolution,[],[f1076,f120])).
% 2.09/0.66  fof(f1076,plain,(
% 2.09/0.66    v1_xboole_0(k1_tarski(sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | ~spl5_16),
% 2.09/0.66    inference(superposition,[],[f1033,f61])).
% 2.09/0.66  fof(f1033,plain,(
% 2.09/0.66    v1_xboole_0(k6_domain_1(u1_struct_0(sK0),sK1)) | ~spl5_16),
% 2.09/0.66    inference(avatar_component_clause,[],[f1031])).
% 2.09/0.66  fof(f1031,plain,(
% 2.09/0.66    spl5_16 <=> v1_xboole_0(k6_domain_1(u1_struct_0(sK0),sK1))),
% 2.09/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 2.09/0.66  % (11194)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.09/0.66  fof(f1072,plain,(
% 2.09/0.66    spl5_16 | ~spl5_2 | ~spl5_3 | spl5_5 | spl5_7 | spl5_14),
% 2.09/0.66    inference(avatar_split_clause,[],[f1071,f253,f124,f110,f100,f95,f1031])).
% 2.09/0.66  fof(f1071,plain,(
% 2.09/0.66    v1_xboole_0(k6_domain_1(u1_struct_0(sK0),sK1)) | (~spl5_2 | ~spl5_3 | spl5_5 | spl5_7 | spl5_14)),
% 2.09/0.66    inference(subsumption_resolution,[],[f1070,f126])).
% 2.09/0.66  fof(f1070,plain,(
% 2.09/0.66    v1_xboole_0(k6_domain_1(u1_struct_0(sK0),sK1)) | v1_xboole_0(u1_struct_0(sK0)) | (~spl5_2 | ~spl5_3 | spl5_5 | spl5_14)),
% 2.09/0.66    inference(subsumption_resolution,[],[f1069,f97])).
% 2.09/0.66  fof(f1069,plain,(
% 2.09/0.66    v1_xboole_0(k6_domain_1(u1_struct_0(sK0),sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | (~spl5_3 | spl5_5 | spl5_14)),
% 2.09/0.66    inference(subsumption_resolution,[],[f1068,f112])).
% 2.09/0.66  fof(f1068,plain,(
% 2.09/0.66    v1_xboole_0(k6_domain_1(u1_struct_0(sK0),sK1)) | v2_struct_0(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | (~spl5_3 | spl5_14)),
% 2.09/0.66    inference(subsumption_resolution,[],[f1067,f102])).
% 2.09/0.66  fof(f1067,plain,(
% 2.09/0.66    v1_xboole_0(k6_domain_1(u1_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | spl5_14),
% 2.09/0.66    inference(resolution,[],[f255,f879])).
% 2.09/0.66  fof(f879,plain,(
% 2.09/0.66    ( ! [X6,X7] : (m1_pre_topc(k1_tex_2(X6,X7),X6) | v1_xboole_0(k6_domain_1(u1_struct_0(X6),X7)) | ~l1_pre_topc(X6) | v2_struct_0(X6) | ~m1_subset_1(X7,u1_struct_0(X6)) | v1_xboole_0(u1_struct_0(X6))) )),
% 2.09/0.66    inference(subsumption_resolution,[],[f878,f60])).
% 2.09/0.66  fof(f878,plain,(
% 2.09/0.66    ( ! [X6,X7] : (m1_pre_topc(k1_tex_2(X6,X7),X6) | v1_xboole_0(k6_domain_1(u1_struct_0(X6),X7)) | ~l1_pre_topc(X6) | v2_struct_0(X6) | ~m1_subset_1(X7,u1_struct_0(X6)) | v1_xboole_0(u1_struct_0(X6)) | ~m1_subset_1(k6_domain_1(u1_struct_0(X6),X7),k1_zfmisc_1(u1_struct_0(X6)))) )),
% 2.09/0.66    inference(subsumption_resolution,[],[f862,f203])).
% 2.09/0.66  fof(f862,plain,(
% 2.09/0.66    ( ! [X6,X7] : (m1_pre_topc(k1_tex_2(X6,X7),X6) | v1_xboole_0(k6_domain_1(u1_struct_0(X6),X7)) | ~l1_pre_topc(X6) | v2_struct_0(X6) | ~m1_subset_1(X7,u1_struct_0(X6)) | v1_xboole_0(u1_struct_0(X6)) | ~m1_pre_topc(sK2(X6,k6_domain_1(u1_struct_0(X6),X7)),X6) | ~m1_subset_1(k6_domain_1(u1_struct_0(X6),X7),k1_zfmisc_1(u1_struct_0(X6)))) )),
% 2.09/0.66    inference(duplicate_literal_removal,[],[f789])).
% 2.09/0.66  fof(f789,plain,(
% 2.09/0.66    ( ! [X6,X7] : (m1_pre_topc(k1_tex_2(X6,X7),X6) | v1_xboole_0(k6_domain_1(u1_struct_0(X6),X7)) | ~l1_pre_topc(X6) | v2_struct_0(X6) | ~m1_subset_1(X7,u1_struct_0(X6)) | v1_xboole_0(u1_struct_0(X6)) | ~m1_pre_topc(sK2(X6,k6_domain_1(u1_struct_0(X6),X7)),X6) | ~m1_subset_1(X7,u1_struct_0(X6)) | ~l1_pre_topc(X6) | v2_struct_0(X6) | ~m1_subset_1(k6_domain_1(u1_struct_0(X6),X7),k1_zfmisc_1(u1_struct_0(X6))) | v1_xboole_0(k6_domain_1(u1_struct_0(X6),X7)) | ~l1_pre_topc(X6) | v2_struct_0(X6)) )),
% 2.09/0.66    inference(superposition,[],[f203,f433])).
% 2.09/0.66  fof(f255,plain,(
% 2.09/0.66    ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | spl5_14),
% 2.09/0.66    inference(avatar_component_clause,[],[f253])).
% 2.09/0.66  fof(f1043,plain,(
% 2.09/0.66    spl5_5 | ~spl5_6 | ~spl5_7),
% 2.09/0.66    inference(avatar_contradiction_clause,[],[f1042])).
% 2.09/0.66  fof(f1042,plain,(
% 2.09/0.66    $false | (spl5_5 | ~spl5_6 | ~spl5_7)),
% 2.09/0.66    inference(subsumption_resolution,[],[f1041,f112])).
% 2.09/0.66  fof(f1041,plain,(
% 2.09/0.66    v2_struct_0(sK0) | (~spl5_6 | ~spl5_7)),
% 2.09/0.66    inference(subsumption_resolution,[],[f1039,f118])).
% 2.09/0.66  fof(f118,plain,(
% 2.09/0.66    l1_struct_0(sK0) | ~spl5_6),
% 2.09/0.66    inference(avatar_component_clause,[],[f116])).
% 2.09/0.66  fof(f116,plain,(
% 2.09/0.66    spl5_6 <=> l1_struct_0(sK0)),
% 2.09/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 2.09/0.66  fof(f1039,plain,(
% 2.09/0.66    ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl5_7),
% 2.09/0.66    inference(resolution,[],[f125,f72])).
% 2.09/0.66  fof(f72,plain,(
% 2.09/0.66    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.09/0.66    inference(cnf_transformation,[],[f31])).
% 2.09/0.66  fof(f31,plain,(
% 2.09/0.66    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.09/0.66    inference(flattening,[],[f30])).
% 2.09/0.66  fof(f30,plain,(
% 2.09/0.66    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.09/0.66    inference(ennf_transformation,[],[f7])).
% 2.09/0.66  fof(f7,axiom,(
% 2.09/0.66    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.09/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 2.09/0.66  fof(f125,plain,(
% 2.09/0.66    v1_xboole_0(u1_struct_0(sK0)) | ~spl5_7),
% 2.09/0.66    inference(avatar_component_clause,[],[f124])).
% 2.09/0.66  fof(f941,plain,(
% 2.09/0.66    spl5_13 | ~spl5_2 | ~spl5_3 | spl5_5 | spl5_7),
% 2.09/0.66    inference(avatar_split_clause,[],[f940,f124,f110,f100,f95,f249])).
% 2.09/0.66  fof(f940,plain,(
% 2.09/0.66    v1_pre_topc(k1_tex_2(sK0,sK1)) | (~spl5_2 | ~spl5_3 | spl5_5 | spl5_7)),
% 2.09/0.66    inference(subsumption_resolution,[],[f932,f126])).
% 2.09/0.66  fof(f932,plain,(
% 2.09/0.66    v1_pre_topc(k1_tex_2(sK0,sK1)) | v1_xboole_0(u1_struct_0(sK0)) | (~spl5_2 | ~spl5_3 | spl5_5)),
% 2.09/0.66    inference(subsumption_resolution,[],[f931,f112])).
% 2.09/0.66  fof(f931,plain,(
% 2.09/0.66    v2_struct_0(sK0) | v1_pre_topc(k1_tex_2(sK0,sK1)) | v1_xboole_0(u1_struct_0(sK0)) | (~spl5_2 | ~spl5_3)),
% 2.09/0.66    inference(subsumption_resolution,[],[f920,f102])).
% 2.09/0.66  fof(f920,plain,(
% 2.09/0.66    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_pre_topc(k1_tex_2(sK0,sK1)) | v1_xboole_0(u1_struct_0(sK0)) | ~spl5_2),
% 2.09/0.66    inference(resolution,[],[f913,f97])).
% 2.09/0.66  fof(f913,plain,(
% 2.09/0.66    ( ! [X2,X3] : (~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_pre_topc(X2) | v2_struct_0(X2) | v1_pre_topc(k1_tex_2(X2,X3)) | v1_xboole_0(u1_struct_0(X2))) )),
% 2.09/0.66    inference(subsumption_resolution,[],[f906,f120])).
% 2.09/0.66  fof(f906,plain,(
% 2.09/0.66    ( ! [X2,X3] : (v1_xboole_0(k1_tarski(X3)) | v1_pre_topc(k1_tex_2(X2,X3)) | ~l1_pre_topc(X2) | v2_struct_0(X2) | ~m1_subset_1(X3,u1_struct_0(X2)) | v1_xboole_0(u1_struct_0(X2))) )),
% 2.09/0.66    inference(duplicate_literal_removal,[],[f905])).
% 2.09/0.66  fof(f905,plain,(
% 2.09/0.66    ( ! [X2,X3] : (v1_xboole_0(k1_tarski(X3)) | v1_pre_topc(k1_tex_2(X2,X3)) | ~l1_pre_topc(X2) | v2_struct_0(X2) | ~m1_subset_1(X3,u1_struct_0(X2)) | v1_xboole_0(u1_struct_0(X2)) | ~m1_subset_1(X3,u1_struct_0(X2)) | v1_xboole_0(u1_struct_0(X2))) )),
% 2.09/0.66    inference(superposition,[],[f881,f61])).
% 2.09/0.66  fof(f881,plain,(
% 2.09/0.66    ( ! [X8,X9] : (v1_xboole_0(k6_domain_1(u1_struct_0(X8),X9)) | v1_pre_topc(k1_tex_2(X8,X9)) | ~l1_pre_topc(X8) | v2_struct_0(X8) | ~m1_subset_1(X9,u1_struct_0(X8)) | v1_xboole_0(u1_struct_0(X8))) )),
% 2.09/0.66    inference(subsumption_resolution,[],[f880,f60])).
% 2.09/0.66  fof(f880,plain,(
% 2.09/0.66    ( ! [X8,X9] : (v1_pre_topc(k1_tex_2(X8,X9)) | v1_xboole_0(k6_domain_1(u1_struct_0(X8),X9)) | ~l1_pre_topc(X8) | v2_struct_0(X8) | ~m1_subset_1(X9,u1_struct_0(X8)) | v1_xboole_0(u1_struct_0(X8)) | ~m1_subset_1(k6_domain_1(u1_struct_0(X8),X9),k1_zfmisc_1(u1_struct_0(X8)))) )),
% 2.09/0.66    inference(subsumption_resolution,[],[f861,f203])).
% 2.09/0.66  fof(f861,plain,(
% 2.09/0.66    ( ! [X8,X9] : (v1_pre_topc(k1_tex_2(X8,X9)) | v1_xboole_0(k6_domain_1(u1_struct_0(X8),X9)) | ~l1_pre_topc(X8) | v2_struct_0(X8) | ~m1_subset_1(X9,u1_struct_0(X8)) | v1_xboole_0(u1_struct_0(X8)) | ~m1_pre_topc(sK2(X8,k6_domain_1(u1_struct_0(X8),X9)),X8) | ~m1_subset_1(k6_domain_1(u1_struct_0(X8),X9),k1_zfmisc_1(u1_struct_0(X8)))) )),
% 2.09/0.66    inference(duplicate_literal_removal,[],[f790])).
% 2.09/0.66  fof(f790,plain,(
% 2.09/0.66    ( ! [X8,X9] : (v1_pre_topc(k1_tex_2(X8,X9)) | v1_xboole_0(k6_domain_1(u1_struct_0(X8),X9)) | ~l1_pre_topc(X8) | v2_struct_0(X8) | ~m1_subset_1(X9,u1_struct_0(X8)) | v1_xboole_0(u1_struct_0(X8)) | ~m1_pre_topc(sK2(X8,k6_domain_1(u1_struct_0(X8),X9)),X8) | ~m1_subset_1(X9,u1_struct_0(X8)) | ~l1_pre_topc(X8) | v2_struct_0(X8) | ~m1_subset_1(k6_domain_1(u1_struct_0(X8),X9),k1_zfmisc_1(u1_struct_0(X8))) | v1_xboole_0(k6_domain_1(u1_struct_0(X8),X9)) | ~l1_pre_topc(X8) | v2_struct_0(X8)) )),
% 2.09/0.66    inference(superposition,[],[f182,f433])).
% 2.09/0.66  fof(f182,plain,(
% 2.09/0.66    ( ! [X4,X5] : (v1_pre_topc(sK2(X4,k6_domain_1(u1_struct_0(X4),X5))) | v1_xboole_0(k6_domain_1(u1_struct_0(X4),X5)) | ~l1_pre_topc(X4) | v2_struct_0(X4) | ~m1_subset_1(X5,u1_struct_0(X4)) | v1_xboole_0(u1_struct_0(X4))) )),
% 2.09/0.66    inference(resolution,[],[f69,f60])).
% 2.09/0.66  fof(f164,plain,(
% 2.09/0.66    ~spl5_10 | spl5_1 | ~spl5_2 | spl5_7),
% 2.09/0.66    inference(avatar_split_clause,[],[f159,f124,f95,f90,f161])).
% 2.09/0.66  fof(f90,plain,(
% 2.09/0.66    spl5_1 <=> v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0)),
% 2.09/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.09/0.66  fof(f159,plain,(
% 2.09/0.66    ~v2_tex_2(k1_tarski(sK1),sK0) | (spl5_1 | ~spl5_2 | spl5_7)),
% 2.09/0.66    inference(subsumption_resolution,[],[f158,f126])).
% 2.09/0.66  fof(f158,plain,(
% 2.09/0.66    ~v2_tex_2(k1_tarski(sK1),sK0) | v1_xboole_0(u1_struct_0(sK0)) | (spl5_1 | ~spl5_2)),
% 2.09/0.66    inference(subsumption_resolution,[],[f155,f97])).
% 2.09/0.66  fof(f155,plain,(
% 2.09/0.66    ~v2_tex_2(k1_tarski(sK1),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | spl5_1),
% 2.09/0.66    inference(superposition,[],[f92,f61])).
% 2.09/0.66  fof(f92,plain,(
% 2.09/0.66    ~v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0) | spl5_1),
% 2.09/0.66    inference(avatar_component_clause,[],[f90])).
% 2.09/0.66  fof(f119,plain,(
% 2.09/0.66    spl5_6 | ~spl5_3),
% 2.09/0.66    inference(avatar_split_clause,[],[f114,f100,f116])).
% 2.09/0.66  fof(f114,plain,(
% 2.09/0.66    l1_struct_0(sK0) | ~spl5_3),
% 2.09/0.66    inference(resolution,[],[f74,f102])).
% 2.09/0.66  fof(f74,plain,(
% 2.09/0.66    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 2.09/0.66    inference(cnf_transformation,[],[f34])).
% 2.09/0.66  fof(f34,plain,(
% 2.09/0.66    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.09/0.66    inference(ennf_transformation,[],[f6])).
% 2.09/0.66  fof(f6,axiom,(
% 2.09/0.66    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.09/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 2.09/0.66  fof(f113,plain,(
% 2.09/0.66    ~spl5_5),
% 2.09/0.66    inference(avatar_split_clause,[],[f53,f110])).
% 2.09/0.66  fof(f53,plain,(
% 2.09/0.66    ~v2_struct_0(sK0)),
% 2.09/0.66    inference(cnf_transformation,[],[f39])).
% 2.09/0.66  fof(f39,plain,(
% 2.09/0.66    (~v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.09/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f38,f37])).
% 2.09/0.66  fof(f37,plain,(
% 2.09/0.66    ? [X0] : (? [X1] : (~v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v2_tex_2(k6_domain_1(u1_struct_0(sK0),X1),sK0) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.09/0.66    introduced(choice_axiom,[])).
% 2.09/0.66  fof(f38,plain,(
% 2.09/0.66    ? [X1] : (~v2_tex_2(k6_domain_1(u1_struct_0(sK0),X1),sK0) & m1_subset_1(X1,u1_struct_0(sK0))) => (~v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 2.09/0.66    introduced(choice_axiom,[])).
% 2.09/0.66  fof(f18,plain,(
% 2.09/0.66    ? [X0] : (? [X1] : (~v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.09/0.66    inference(flattening,[],[f17])).
% 2.09/0.66  fof(f17,plain,(
% 2.09/0.66    ? [X0] : (? [X1] : (~v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.09/0.66    inference(ennf_transformation,[],[f15])).
% 2.09/0.66  fof(f15,negated_conjecture,(
% 2.09/0.66    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 2.09/0.66    inference(negated_conjecture,[],[f14])).
% 2.09/0.66  fof(f14,conjecture,(
% 2.09/0.66    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 2.09/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).
% 2.09/0.66  fof(f108,plain,(
% 2.09/0.66    spl5_4),
% 2.09/0.66    inference(avatar_split_clause,[],[f54,f105])).
% 2.09/0.66  fof(f54,plain,(
% 2.09/0.66    v2_pre_topc(sK0)),
% 2.09/0.66    inference(cnf_transformation,[],[f39])).
% 2.09/0.66  fof(f103,plain,(
% 2.09/0.66    spl5_3),
% 2.09/0.66    inference(avatar_split_clause,[],[f55,f100])).
% 2.09/0.66  fof(f55,plain,(
% 2.09/0.66    l1_pre_topc(sK0)),
% 2.09/0.66    inference(cnf_transformation,[],[f39])).
% 2.09/0.66  fof(f98,plain,(
% 2.09/0.66    spl5_2),
% 2.09/0.66    inference(avatar_split_clause,[],[f56,f95])).
% 2.09/0.66  fof(f56,plain,(
% 2.09/0.66    m1_subset_1(sK1,u1_struct_0(sK0))),
% 2.09/0.66    inference(cnf_transformation,[],[f39])).
% 2.09/0.66  fof(f93,plain,(
% 2.09/0.66    ~spl5_1),
% 2.09/0.66    inference(avatar_split_clause,[],[f57,f90])).
% 2.09/0.66  fof(f57,plain,(
% 2.09/0.66    ~v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0)),
% 2.09/0.66    inference(cnf_transformation,[],[f39])).
% 2.09/0.66  % SZS output end Proof for theBenchmark
% 2.09/0.66  % (11161)------------------------------
% 2.09/0.66  % (11161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.09/0.66  % (11161)Termination reason: Refutation
% 2.09/0.66  
% 2.09/0.66  % (11161)Memory used [KB]: 7036
% 2.09/0.66  % (11161)Time elapsed: 0.235 s
% 2.09/0.66  % (11161)------------------------------
% 2.09/0.66  % (11161)------------------------------
% 2.09/0.67  % (11139)Success in time 0.287 s
%------------------------------------------------------------------------------
