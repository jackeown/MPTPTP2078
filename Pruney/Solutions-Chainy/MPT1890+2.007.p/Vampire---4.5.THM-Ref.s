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
% DateTime   : Thu Dec  3 13:22:12 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 401 expanded)
%              Number of leaves         :   20 ( 133 expanded)
%              Depth                    :   15
%              Number of atoms          :  392 (2842 expanded)
%              Number of equality atoms :   21 ( 301 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f309,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f229,f233,f262,f286,f296,f307])).

fof(f307,plain,(
    ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f306])).

fof(f306,plain,
    ( $false
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f300,f155])).

fof(f155,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(resolution,[],[f154,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(resolution,[],[f48,f51])).

fof(f51,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
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

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK3(X0,X1))
            | ~ v4_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r2_hidden(sK3(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) )
      | ~ sP0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2)
              | ~ v4_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK3(X0,X1))
            | ~ v4_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r2_hidden(sK3(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2)
              | ~ v4_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2)
              | ~ v4_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f154,plain,(
    sP0(sK1,sK2) ),
    inference(subsumption_resolution,[],[f153,f40])).

fof(f40,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ v2_tex_2(sK2,sK1)
    & ! [X2] :
        ( k6_domain_1(u1_struct_0(sK1),X2) = k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X2)))
        | ~ r2_hidden(X2,sK2)
        | ~ m1_subset_1(X2,u1_struct_0(sK1)) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1)
    & v3_tdlat_3(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f12,f26,f25])).

fof(f25,plain,
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
          ( ~ v2_tex_2(X1,sK1)
          & ! [X2] :
              ( k6_domain_1(u1_struct_0(sK1),X2) = k9_subset_1(u1_struct_0(sK1),X1,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X2)))
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(sK1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1)
      & v3_tdlat_3(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X1] :
        ( ~ v2_tex_2(X1,sK1)
        & ! [X2] :
            ( k6_domain_1(u1_struct_0(sK1),X2) = k9_subset_1(u1_struct_0(sK1),X1,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X2)))
            | ~ r2_hidden(X2,X1)
            | ~ m1_subset_1(X2,u1_struct_0(sK1)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( ~ v2_tex_2(sK2,sK1)
      & ! [X2] :
          ( k6_domain_1(u1_struct_0(sK1),X2) = k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X2)))
          | ~ r2_hidden(X2,sK2)
          | ~ m1_subset_1(X2,u1_struct_0(sK1)) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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

fof(f153,plain,
    ( sP0(sK1,sK2)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f152,f41])).

fof(f41,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f152,plain,
    ( sP0(sK1,sK2)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f151,f42])).

fof(f42,plain,(
    v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f151,plain,
    ( sP0(sK1,sK2)
    | ~ v3_tdlat_3(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f150,f43])).

fof(f43,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f150,plain,
    ( sP0(sK1,sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v3_tdlat_3(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f148,f46])).

fof(f46,plain,(
    ~ v2_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f148,plain,
    ( sP0(sK1,sK2)
    | v2_tex_2(sK2,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v3_tdlat_3(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f50,f44])).

fof(f44,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP0(X0,X1)
      | v2_tex_2(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | sP0(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f14,f23])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ? [X2] :
              ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ? [X2] :
              ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = k6_domain_1(u1_struct_0(X0),X2)
                            & v4_pre_topc(X3,X0) ) )
                    & r2_hidden(X2,X1) ) )
           => v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_tex_2)).

fof(f300,plain,
    ( v1_xboole_0(sK2)
    | ~ spl6_2 ),
    inference(resolution,[],[f85,f52])).

fof(f52,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f85,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl6_2
  <=> ! [X0] : ~ r2_hidden(X0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f296,plain,
    ( spl6_1
    | ~ spl6_13
    | spl6_16 ),
    inference(avatar_split_clause,[],[f293,f226,f214,f80])).

fof(f80,plain,
    ( spl6_1
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f214,plain,
    ( spl6_13
  <=> m1_subset_1(sK3(sK1,sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f226,plain,
    ( spl6_16
  <=> v4_pre_topc(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3(sK1,sK2))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f293,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl6_13
    | spl6_16 ),
    inference(subsumption_resolution,[],[f290,f215])).

fof(f215,plain,
    ( m1_subset_1(sK3(sK1,sK2),u1_struct_0(sK1))
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f214])).

fof(f290,plain,
    ( ~ m1_subset_1(sK3(sK1,sK2),u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | spl6_16 ),
    inference(resolution,[],[f289,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
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

fof(f289,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK3(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl6_16 ),
    inference(subsumption_resolution,[],[f288,f41])).

fof(f288,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK3(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | spl6_16 ),
    inference(subsumption_resolution,[],[f287,f43])).

fof(f287,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK3(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | spl6_16 ),
    inference(resolution,[],[f228,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
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

fof(f228,plain,
    ( ~ v4_pre_topc(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3(sK1,sK2))),sK1)
    | spl6_16 ),
    inference(avatar_component_clause,[],[f226])).

fof(f286,plain,
    ( spl6_1
    | ~ spl6_13
    | spl6_15 ),
    inference(avatar_contradiction_clause,[],[f285])).

fof(f285,plain,
    ( $false
    | spl6_1
    | ~ spl6_13
    | spl6_15 ),
    inference(subsumption_resolution,[],[f284,f82])).

fof(f82,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f284,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl6_13
    | spl6_15 ),
    inference(subsumption_resolution,[],[f281,f215])).

fof(f281,plain,
    ( ~ m1_subset_1(sK3(sK1,sK2),u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | spl6_15 ),
    inference(resolution,[],[f280,f54])).

fof(f280,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK3(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl6_15 ),
    inference(subsumption_resolution,[],[f277,f43])).

fof(f277,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK3(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | spl6_15 ),
    inference(resolution,[],[f224,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
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

fof(f224,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3(sK1,sK2))),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl6_15 ),
    inference(avatar_component_clause,[],[f222])).

fof(f222,plain,
    ( spl6_15
  <=> m1_subset_1(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3(sK1,sK2))),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f262,plain,(
    spl6_14 ),
    inference(avatar_contradiction_clause,[],[f261])).

fof(f261,plain,
    ( $false
    | spl6_14 ),
    inference(subsumption_resolution,[],[f260,f154])).

fof(f260,plain,
    ( ~ sP0(sK1,sK2)
    | spl6_14 ),
    inference(resolution,[],[f220,f48])).

fof(f220,plain,
    ( ~ r2_hidden(sK3(sK1,sK2),sK2)
    | spl6_14 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl6_14
  <=> r2_hidden(sK3(sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f233,plain,(
    spl6_13 ),
    inference(avatar_contradiction_clause,[],[f232])).

fof(f232,plain,
    ( $false
    | spl6_13 ),
    inference(subsumption_resolution,[],[f230,f154])).

fof(f230,plain,
    ( ~ sP0(sK1,sK2)
    | spl6_13 ),
    inference(resolution,[],[f216,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f216,plain,
    ( ~ m1_subset_1(sK3(sK1,sK2),u1_struct_0(sK1))
    | spl6_13 ),
    inference(avatar_component_clause,[],[f214])).

fof(f229,plain,
    ( ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f212,f226,f222,f218,f214])).

fof(f212,plain,
    ( ~ v4_pre_topc(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3(sK1,sK2))),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3(sK1,sK2))),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK3(sK1,sK2),sK2)
    | ~ m1_subset_1(sK3(sK1,sK2),u1_struct_0(sK1)) ),
    inference(equality_resolution,[],[f199])).

fof(f199,plain,(
    ! [X0] :
      ( k6_domain_1(u1_struct_0(sK1),X0) != k6_domain_1(u1_struct_0(sK1),sK3(sK1,sK2))
      | ~ v4_pre_topc(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0)),sK1)
      | ~ m1_subset_1(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0)),k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r2_hidden(X0,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f198,f154])).

fof(f198,plain,(
    ! [X0] :
      ( k6_domain_1(u1_struct_0(sK1),X0) != k6_domain_1(u1_struct_0(sK1),sK3(sK1,sK2))
      | ~ v4_pre_topc(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0)),sK1)
      | ~ m1_subset_1(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0)),k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ sP0(sK1,sK2)
      | ~ r2_hidden(X0,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    inference(superposition,[],[f49,f45])).

fof(f45,plain,(
    ! [X2] :
      ( k6_domain_1(u1_struct_0(sK1),X2) = k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X2)))
      | ~ r2_hidden(X2,sK2)
      | ~ m1_subset_1(X2,u1_struct_0(sK1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK3(X0,X1))
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f86,plain,
    ( ~ spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f77,f84,f80])).

fof(f77,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | ~ v1_xboole_0(u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f73,f51])).

fof(f73,plain,(
    ! [X0] :
      ( r2_hidden(X0,u1_struct_0(sK1))
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f57,f63])).

fof(f63,plain,(
    r1_tarski(sK2,u1_struct_0(sK1)) ),
    inference(resolution,[],[f60,f44])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f36,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:57:33 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.53  % (8965)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (8980)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.53  % (8981)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % (8972)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (8964)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.54  % (8968)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.54  % (8973)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  % (8954)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.55  % (8978)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.55  % (8959)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.56  % (8975)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.56  % (8983)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.56  % (8955)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.56  % (8981)Refutation found. Thanks to Tanya!
% 0.20/0.56  % SZS status Theorem for theBenchmark
% 0.20/0.56  % SZS output start Proof for theBenchmark
% 0.20/0.56  fof(f309,plain,(
% 0.20/0.56    $false),
% 0.20/0.56    inference(avatar_sat_refutation,[],[f86,f229,f233,f262,f286,f296,f307])).
% 0.20/0.56  fof(f307,plain,(
% 0.20/0.56    ~spl6_2),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f306])).
% 0.20/0.56  fof(f306,plain,(
% 0.20/0.56    $false | ~spl6_2),
% 0.20/0.56    inference(subsumption_resolution,[],[f300,f155])).
% 0.20/0.56  fof(f155,plain,(
% 0.20/0.56    ~v1_xboole_0(sK2)),
% 0.20/0.56    inference(resolution,[],[f154,f67])).
% 0.20/0.56  fof(f67,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~sP0(X0,X1) | ~v1_xboole_0(X1)) )),
% 0.20/0.56    inference(resolution,[],[f48,f51])).
% 0.20/0.56  fof(f51,plain,(
% 0.20/0.56    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f34])).
% 0.20/0.56  fof(f34,plain,(
% 0.20/0.56    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).
% 0.20/0.56  fof(f33,plain,(
% 0.20/0.56    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f32,plain,(
% 0.20/0.56    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.56    inference(rectify,[],[f31])).
% 0.20/0.56  fof(f31,plain,(
% 0.20/0.56    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.56    inference(nnf_transformation,[],[f1])).
% 0.20/0.56  fof(f1,axiom,(
% 0.20/0.56    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.56  fof(f48,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | ~sP0(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f30])).
% 0.20/0.56  fof(f30,plain,(
% 0.20/0.56    ! [X0,X1] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK3(X0,X1)) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))) | ~sP0(X0,X1))),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f29])).
% 0.20/0.56  fof(f29,plain,(
% 0.20/0.56    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK3(X0,X1)) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f28,plain,(
% 0.20/0.56    ! [X0,X1] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~sP0(X0,X1))),
% 0.20/0.56    inference(nnf_transformation,[],[f23])).
% 0.20/0.56  fof(f23,plain,(
% 0.20/0.56    ! [X0,X1] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~sP0(X0,X1))),
% 0.20/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.56  fof(f154,plain,(
% 0.20/0.56    sP0(sK1,sK2)),
% 0.20/0.56    inference(subsumption_resolution,[],[f153,f40])).
% 0.20/0.56  fof(f40,plain,(
% 0.20/0.56    ~v2_struct_0(sK1)),
% 0.20/0.56    inference(cnf_transformation,[],[f27])).
% 0.20/0.56  fof(f27,plain,(
% 0.20/0.56    (~v2_tex_2(sK2,sK1) & ! [X2] : (k6_domain_1(u1_struct_0(sK1),X2) = k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X2))) | ~r2_hidden(X2,sK2) | ~m1_subset_1(X2,u1_struct_0(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v3_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f12,f26,f25])).
% 0.20/0.56  fof(f25,plain,(
% 0.20/0.56    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & ! [X2] : (k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v2_tex_2(X1,sK1) & ! [X2] : (k6_domain_1(u1_struct_0(sK1),X2) = k9_subset_1(u1_struct_0(sK1),X1,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X2))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(sK1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v3_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f26,plain,(
% 0.20/0.56    ? [X1] : (~v2_tex_2(X1,sK1) & ! [X2] : (k6_domain_1(u1_struct_0(sK1),X2) = k9_subset_1(u1_struct_0(sK1),X1,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X2))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(sK1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) => (~v2_tex_2(sK2,sK1) & ! [X2] : (k6_domain_1(u1_struct_0(sK1),X2) = k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X2))) | ~r2_hidden(X2,sK2) | ~m1_subset_1(X2,u1_struct_0(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f12,plain,(
% 0.20/0.56    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & ! [X2] : (k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.56    inference(flattening,[],[f11])).
% 0.20/0.56  fof(f11,plain,(
% 0.20/0.56    ? [X0] : (? [X1] : ((~v2_tex_2(X1,X0) & ! [X2] : ((k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f10])).
% 0.20/0.56  fof(f10,negated_conjecture,(
% 0.20/0.56    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))) => v2_tex_2(X1,X0))))),
% 0.20/0.56    inference(negated_conjecture,[],[f9])).
% 0.20/0.56  fof(f9,conjecture,(
% 0.20/0.56    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))) => v2_tex_2(X1,X0))))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_tex_2)).
% 0.20/0.56  fof(f153,plain,(
% 0.20/0.56    sP0(sK1,sK2) | v2_struct_0(sK1)),
% 0.20/0.56    inference(subsumption_resolution,[],[f152,f41])).
% 0.20/0.56  fof(f41,plain,(
% 0.20/0.56    v2_pre_topc(sK1)),
% 0.20/0.56    inference(cnf_transformation,[],[f27])).
% 0.20/0.56  fof(f152,plain,(
% 0.20/0.56    sP0(sK1,sK2) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 0.20/0.56    inference(subsumption_resolution,[],[f151,f42])).
% 0.20/0.56  fof(f42,plain,(
% 0.20/0.56    v3_tdlat_3(sK1)),
% 0.20/0.56    inference(cnf_transformation,[],[f27])).
% 0.20/0.56  fof(f151,plain,(
% 0.20/0.56    sP0(sK1,sK2) | ~v3_tdlat_3(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 0.20/0.56    inference(subsumption_resolution,[],[f150,f43])).
% 0.20/0.56  fof(f43,plain,(
% 0.20/0.56    l1_pre_topc(sK1)),
% 0.20/0.56    inference(cnf_transformation,[],[f27])).
% 0.20/0.56  fof(f150,plain,(
% 0.20/0.56    sP0(sK1,sK2) | ~l1_pre_topc(sK1) | ~v3_tdlat_3(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 0.20/0.56    inference(subsumption_resolution,[],[f148,f46])).
% 0.20/0.56  fof(f46,plain,(
% 0.20/0.56    ~v2_tex_2(sK2,sK1)),
% 0.20/0.56    inference(cnf_transformation,[],[f27])).
% 0.20/0.56  fof(f148,plain,(
% 0.20/0.56    sP0(sK1,sK2) | v2_tex_2(sK2,sK1) | ~l1_pre_topc(sK1) | ~v3_tdlat_3(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 0.20/0.56    inference(resolution,[],[f50,f44])).
% 0.20/0.56  fof(f44,plain,(
% 0.20/0.56    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.20/0.56    inference(cnf_transformation,[],[f27])).
% 0.20/0.56  fof(f50,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP0(X0,X1) | v2_tex_2(X1,X0) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f24])).
% 0.20/0.56  fof(f24,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | sP0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.56    inference(definition_folding,[],[f14,f23])).
% 0.20/0.56  fof(f14,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.56    inference(flattening,[],[f13])).
% 0.20/0.56  fof(f13,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) | ? [X2] : ((! [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2) | ~v4_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f8])).
% 0.20/0.56  fof(f8,axiom,(
% 0.20/0.56    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k6_domain_1(u1_struct_0(X0),X2) & v4_pre_topc(X3,X0))) & r2_hidden(X2,X1))) => v2_tex_2(X1,X0))))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_tex_2)).
% 0.20/0.56  fof(f300,plain,(
% 0.20/0.56    v1_xboole_0(sK2) | ~spl6_2),
% 0.20/0.56    inference(resolution,[],[f85,f52])).
% 0.20/0.56  fof(f52,plain,(
% 0.20/0.56    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f34])).
% 0.20/0.56  fof(f85,plain,(
% 0.20/0.56    ( ! [X0] : (~r2_hidden(X0,sK2)) ) | ~spl6_2),
% 0.20/0.56    inference(avatar_component_clause,[],[f84])).
% 0.20/0.56  fof(f84,plain,(
% 0.20/0.56    spl6_2 <=> ! [X0] : ~r2_hidden(X0,sK2)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.56  fof(f296,plain,(
% 0.20/0.56    spl6_1 | ~spl6_13 | spl6_16),
% 0.20/0.56    inference(avatar_split_clause,[],[f293,f226,f214,f80])).
% 0.20/0.56  fof(f80,plain,(
% 0.20/0.56    spl6_1 <=> v1_xboole_0(u1_struct_0(sK1))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.56  fof(f214,plain,(
% 0.20/0.56    spl6_13 <=> m1_subset_1(sK3(sK1,sK2),u1_struct_0(sK1))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.20/0.56  fof(f226,plain,(
% 0.20/0.56    spl6_16 <=> v4_pre_topc(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3(sK1,sK2))),sK1)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.20/0.56  fof(f293,plain,(
% 0.20/0.56    v1_xboole_0(u1_struct_0(sK1)) | (~spl6_13 | spl6_16)),
% 0.20/0.56    inference(subsumption_resolution,[],[f290,f215])).
% 0.20/0.56  fof(f215,plain,(
% 0.20/0.56    m1_subset_1(sK3(sK1,sK2),u1_struct_0(sK1)) | ~spl6_13),
% 0.20/0.56    inference(avatar_component_clause,[],[f214])).
% 0.20/0.56  fof(f290,plain,(
% 0.20/0.56    ~m1_subset_1(sK3(sK1,sK2),u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK1)) | spl6_16),
% 0.20/0.56    inference(resolution,[],[f289,f54])).
% 0.20/0.56  fof(f54,plain,(
% 0.20/0.56    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f17])).
% 0.20/0.56  fof(f17,plain,(
% 0.20/0.56    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.56    inference(flattening,[],[f16])).
% 0.20/0.56  fof(f16,plain,(
% 0.20/0.56    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f6])).
% 0.20/0.56  fof(f6,axiom,(
% 0.20/0.56    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.20/0.56  fof(f289,plain,(
% 0.20/0.56    ~m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK3(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) | spl6_16),
% 0.20/0.56    inference(subsumption_resolution,[],[f288,f41])).
% 0.20/0.56  fof(f288,plain,(
% 0.20/0.56    ~m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK3(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) | ~v2_pre_topc(sK1) | spl6_16),
% 0.20/0.56    inference(subsumption_resolution,[],[f287,f43])).
% 0.20/0.56  fof(f287,plain,(
% 0.20/0.56    ~m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK3(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | spl6_16),
% 0.20/0.56    inference(resolution,[],[f228,f55])).
% 0.20/0.56  fof(f55,plain,(
% 0.20/0.56    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f19])).
% 0.20/0.56  fof(f19,plain,(
% 0.20/0.56    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.56    inference(flattening,[],[f18])).
% 0.20/0.56  fof(f18,plain,(
% 0.20/0.56    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f7])).
% 0.20/0.56  fof(f7,axiom,(
% 0.20/0.56    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).
% 0.20/0.56  fof(f228,plain,(
% 0.20/0.56    ~v4_pre_topc(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3(sK1,sK2))),sK1) | spl6_16),
% 0.20/0.56    inference(avatar_component_clause,[],[f226])).
% 0.20/0.56  fof(f286,plain,(
% 0.20/0.56    spl6_1 | ~spl6_13 | spl6_15),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f285])).
% 0.20/0.56  fof(f285,plain,(
% 0.20/0.56    $false | (spl6_1 | ~spl6_13 | spl6_15)),
% 0.20/0.56    inference(subsumption_resolution,[],[f284,f82])).
% 0.20/0.56  fof(f82,plain,(
% 0.20/0.56    ~v1_xboole_0(u1_struct_0(sK1)) | spl6_1),
% 0.20/0.56    inference(avatar_component_clause,[],[f80])).
% 0.20/0.56  fof(f284,plain,(
% 0.20/0.56    v1_xboole_0(u1_struct_0(sK1)) | (~spl6_13 | spl6_15)),
% 0.20/0.56    inference(subsumption_resolution,[],[f281,f215])).
% 0.20/0.56  fof(f281,plain,(
% 0.20/0.56    ~m1_subset_1(sK3(sK1,sK2),u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK1)) | spl6_15),
% 0.20/0.56    inference(resolution,[],[f280,f54])).
% 0.20/0.56  fof(f280,plain,(
% 0.20/0.56    ~m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK3(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) | spl6_15),
% 0.20/0.56    inference(subsumption_resolution,[],[f277,f43])).
% 0.20/0.56  fof(f277,plain,(
% 0.20/0.56    ~m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK3(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | spl6_15),
% 0.20/0.56    inference(resolution,[],[f224,f56])).
% 0.20/0.56  fof(f56,plain,(
% 0.20/0.56    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f21])).
% 0.20/0.56  fof(f21,plain,(
% 0.20/0.56    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.56    inference(flattening,[],[f20])).
% 0.20/0.56  fof(f20,plain,(
% 0.20/0.56    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f5])).
% 0.20/0.56  fof(f5,axiom,(
% 0.20/0.56    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.20/0.56  fof(f224,plain,(
% 0.20/0.56    ~m1_subset_1(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3(sK1,sK2))),k1_zfmisc_1(u1_struct_0(sK1))) | spl6_15),
% 0.20/0.56    inference(avatar_component_clause,[],[f222])).
% 0.20/0.56  fof(f222,plain,(
% 0.20/0.56    spl6_15 <=> m1_subset_1(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3(sK1,sK2))),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.20/0.56  fof(f262,plain,(
% 0.20/0.56    spl6_14),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f261])).
% 0.20/0.56  fof(f261,plain,(
% 0.20/0.56    $false | spl6_14),
% 0.20/0.56    inference(subsumption_resolution,[],[f260,f154])).
% 0.20/0.56  fof(f260,plain,(
% 0.20/0.56    ~sP0(sK1,sK2) | spl6_14),
% 0.20/0.56    inference(resolution,[],[f220,f48])).
% 0.20/0.56  fof(f220,plain,(
% 0.20/0.56    ~r2_hidden(sK3(sK1,sK2),sK2) | spl6_14),
% 0.20/0.56    inference(avatar_component_clause,[],[f218])).
% 0.20/0.56  fof(f218,plain,(
% 0.20/0.56    spl6_14 <=> r2_hidden(sK3(sK1,sK2),sK2)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.20/0.56  fof(f233,plain,(
% 0.20/0.56    spl6_13),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f232])).
% 0.20/0.56  fof(f232,plain,(
% 0.20/0.56    $false | spl6_13),
% 0.20/0.56    inference(subsumption_resolution,[],[f230,f154])).
% 0.20/0.56  fof(f230,plain,(
% 0.20/0.56    ~sP0(sK1,sK2) | spl6_13),
% 0.20/0.56    inference(resolution,[],[f216,f47])).
% 0.20/0.56  fof(f47,plain,(
% 0.20/0.56    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) | ~sP0(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f30])).
% 0.20/0.56  fof(f216,plain,(
% 0.20/0.56    ~m1_subset_1(sK3(sK1,sK2),u1_struct_0(sK1)) | spl6_13),
% 0.20/0.56    inference(avatar_component_clause,[],[f214])).
% 0.20/0.56  fof(f229,plain,(
% 0.20/0.56    ~spl6_13 | ~spl6_14 | ~spl6_15 | ~spl6_16),
% 0.20/0.56    inference(avatar_split_clause,[],[f212,f226,f222,f218,f214])).
% 0.20/0.56  fof(f212,plain,(
% 0.20/0.56    ~v4_pre_topc(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3(sK1,sK2))),sK1) | ~m1_subset_1(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK3(sK1,sK2))),k1_zfmisc_1(u1_struct_0(sK1))) | ~r2_hidden(sK3(sK1,sK2),sK2) | ~m1_subset_1(sK3(sK1,sK2),u1_struct_0(sK1))),
% 0.20/0.56    inference(equality_resolution,[],[f199])).
% 0.20/0.56  fof(f199,plain,(
% 0.20/0.56    ( ! [X0] : (k6_domain_1(u1_struct_0(sK1),X0) != k6_domain_1(u1_struct_0(sK1),sK3(sK1,sK2)) | ~v4_pre_topc(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0)),sK1) | ~m1_subset_1(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0)),k1_zfmisc_1(u1_struct_0(sK1))) | ~r2_hidden(X0,sK2) | ~m1_subset_1(X0,u1_struct_0(sK1))) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f198,f154])).
% 0.20/0.56  fof(f198,plain,(
% 0.20/0.56    ( ! [X0] : (k6_domain_1(u1_struct_0(sK1),X0) != k6_domain_1(u1_struct_0(sK1),sK3(sK1,sK2)) | ~v4_pre_topc(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0)),sK1) | ~m1_subset_1(k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0)),k1_zfmisc_1(u1_struct_0(sK1))) | ~sP0(sK1,sK2) | ~r2_hidden(X0,sK2) | ~m1_subset_1(X0,u1_struct_0(sK1))) )),
% 0.20/0.56    inference(superposition,[],[f49,f45])).
% 0.20/0.56  fof(f45,plain,(
% 0.20/0.56    ( ! [X2] : (k6_domain_1(u1_struct_0(sK1),X2) = k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X2))) | ~r2_hidden(X2,sK2) | ~m1_subset_1(X2,u1_struct_0(sK1))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f27])).
% 0.20/0.56  fof(f49,plain,(
% 0.20/0.56    ( ! [X0,X3,X1] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK3(X0,X1)) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~sP0(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f30])).
% 0.20/0.56  fof(f86,plain,(
% 0.20/0.56    ~spl6_1 | spl6_2),
% 0.20/0.56    inference(avatar_split_clause,[],[f77,f84,f80])).
% 0.20/0.56  fof(f77,plain,(
% 0.20/0.56    ( ! [X0] : (~r2_hidden(X0,sK2) | ~v1_xboole_0(u1_struct_0(sK1))) )),
% 0.20/0.56    inference(resolution,[],[f73,f51])).
% 0.20/0.56  fof(f73,plain,(
% 0.20/0.56    ( ! [X0] : (r2_hidden(X0,u1_struct_0(sK1)) | ~r2_hidden(X0,sK2)) )),
% 0.20/0.56    inference(resolution,[],[f57,f63])).
% 0.20/0.56  fof(f63,plain,(
% 0.20/0.56    r1_tarski(sK2,u1_struct_0(sK1))),
% 0.20/0.56    inference(resolution,[],[f60,f44])).
% 0.20/0.56  fof(f60,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f39])).
% 0.20/0.56  fof(f39,plain,(
% 0.20/0.56    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.56    inference(nnf_transformation,[],[f4])).
% 0.20/0.56  fof(f4,axiom,(
% 0.20/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.56  fof(f57,plain,(
% 0.20/0.56    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f38])).
% 0.20/0.56  fof(f38,plain,(
% 0.20/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f36,f37])).
% 0.20/0.56  fof(f37,plain,(
% 0.20/0.56    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f36,plain,(
% 0.20/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.56    inference(rectify,[],[f35])).
% 0.20/0.56  fof(f35,plain,(
% 0.20/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.56    inference(nnf_transformation,[],[f22])).
% 0.20/0.56  fof(f22,plain,(
% 0.20/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f2])).
% 0.20/0.56  fof(f2,axiom,(
% 0.20/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.56  % SZS output end Proof for theBenchmark
% 0.20/0.56  % (8981)------------------------------
% 0.20/0.56  % (8981)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (8981)Termination reason: Refutation
% 0.20/0.56  
% 0.20/0.56  % (8981)Memory used [KB]: 6396
% 0.20/0.56  % (8981)Time elapsed: 0.129 s
% 0.20/0.56  % (8981)------------------------------
% 0.20/0.56  % (8981)------------------------------
% 0.20/0.56  % (8975)Refutation not found, incomplete strategy% (8975)------------------------------
% 0.20/0.56  % (8975)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (8975)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (8975)Memory used [KB]: 1791
% 0.20/0.56  % (8975)Time elapsed: 0.113 s
% 0.20/0.56  % (8975)------------------------------
% 0.20/0.56  % (8975)------------------------------
% 0.20/0.56  % (8982)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.56  % (8953)Success in time 0.203 s
%------------------------------------------------------------------------------
