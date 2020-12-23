%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:12 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 553 expanded)
%              Number of leaves         :   14 ( 192 expanded)
%              Depth                    :   12
%              Number of atoms          :  291 (4437 expanded)
%              Number of equality atoms :   24 ( 528 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f528,plain,(
    $false ),
    inference(subsumption_resolution,[],[f430,f527])).

fof(f527,plain,(
    ~ m1_subset_1(k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5(sK3,sK4))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unit_resulting_resolution,[],[f67,f89,f433,f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK5(X0,X1))
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK5(X0,X1))
            | ~ v3_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r2_hidden(sK5(X0,X1),X1)
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) )
      | ~ sP0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK5(X0,X1))
            | ~ v3_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r2_hidden(sK5(X0,X1),X1)
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f433,plain,(
    v3_pre_topc(k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5(sK3,sK4))),sK3) ),
    inference(superposition,[],[f157,f89])).

fof(f157,plain,(
    ! [X0] : v3_pre_topc(k2_pre_topc(sK3,k9_subset_1(u1_struct_0(sK3),sK4,X0)),sK3) ),
    inference(superposition,[],[f136,f69])).

fof(f69,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK3),X0,sK4) = k9_subset_1(u1_struct_0(sK3),sK4,X0) ),
    inference(unit_resulting_resolution,[],[f41,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f41,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ~ v2_tex_2(sK4,sK3)
    & ! [X2] :
        ( k6_domain_1(u1_struct_0(sK3),X2) = k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X2)))
        | ~ r2_hidden(X2,sK4)
        | ~ m1_subset_1(X2,u1_struct_0(sK3)) )
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & l1_pre_topc(sK3)
    & v3_tdlat_3(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f10,f27,f26])).

fof(f26,plain,
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
          ( ~ v2_tex_2(X1,sK3)
          & ! [X2] :
              ( k6_domain_1(u1_struct_0(sK3),X2) = k9_subset_1(u1_struct_0(sK3),X1,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X2)))
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(sK3)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) )
      & l1_pre_topc(sK3)
      & v3_tdlat_3(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ~ v2_tex_2(X1,sK3)
        & ! [X2] :
            ( k6_domain_1(u1_struct_0(sK3),X2) = k9_subset_1(u1_struct_0(sK3),X1,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X2)))
            | ~ r2_hidden(X2,X1)
            | ~ m1_subset_1(X2,u1_struct_0(sK3)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) )
   => ( ~ v2_tex_2(sK4,sK3)
      & ! [X2] :
          ( k6_domain_1(u1_struct_0(sK3),X2) = k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X2)))
          | ~ r2_hidden(X2,sK4)
          | ~ m1_subset_1(X2,u1_struct_0(sK3)) )
      & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
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
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
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

fof(f136,plain,(
    ! [X0] : v3_pre_topc(k2_pre_topc(sK3,k9_subset_1(u1_struct_0(sK3),X0,sK4)),sK3) ),
    inference(unit_resulting_resolution,[],[f61,f91,f92,f53])).

fof(f53,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | v3_pre_topc(X2,X0)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( sP1(X0)
        | ( ~ v3_pre_topc(sK6(X0),X0)
          & v4_pre_topc(sK6(X0),X0)
          & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( v3_pre_topc(X2,X0)
            | ~ v4_pre_topc(X2,X0)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f34,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK6(X0),X0)
        & v4_pre_topc(sK6(X0),X0)
        & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ( sP1(X0)
        | ? [X1] :
            ( ~ v3_pre_topc(X1,X0)
            & v4_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( v3_pre_topc(X2,X0)
            | ~ v4_pre_topc(X2,X0)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP1(X0) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( sP1(X0)
        | ? [X1] :
            ( ~ v3_pre_topc(X1,X0)
            & v4_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP1(X0) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( sP1(X0)
    <=> ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f92,plain,(
    ! [X0] : m1_subset_1(k2_pre_topc(sK3,k9_subset_1(u1_struct_0(sK3),X0,sK4)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unit_resulting_resolution,[],[f40,f68,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f68,plain,(
    ! [X0] : m1_subset_1(k9_subset_1(u1_struct_0(sK3),X0,sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unit_resulting_resolution,[],[f41,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f40,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f91,plain,(
    ! [X0] : v4_pre_topc(k2_pre_topc(sK3,k9_subset_1(u1_struct_0(sK3),X0,sK4)),sK3) ),
    inference(unit_resulting_resolution,[],[f38,f40,f68,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f38,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f61,plain,(
    sP1(sK3) ),
    inference(unit_resulting_resolution,[],[f39,f60,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ sP2(X0)
      | ~ v3_tdlat_3(X0)
      | sP1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ~ sP1(X0) )
        & ( sP1(X0)
          | ~ v3_tdlat_3(X0) ) )
      | ~ sP2(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> sP1(X0) )
      | ~ sP2(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f60,plain,(
    sP2(sK3) ),
    inference(unit_resulting_resolution,[],[f38,f40,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | sP2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_folding,[],[f18,f24,f23])).

fof(f18,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).

fof(f39,plain,(
    v3_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f89,plain,(
    k6_domain_1(u1_struct_0(sK3),sK5(sK3,sK4)) = k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5(sK3,sK4)))) ),
    inference(unit_resulting_resolution,[],[f75,f74,f42])).

fof(f42,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ r2_hidden(X2,sK4)
      | k6_domain_1(u1_struct_0(sK3),X2) = k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X2))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f74,plain,(
    m1_subset_1(sK5(sK3,sK4),u1_struct_0(sK3)) ),
    inference(unit_resulting_resolution,[],[f67,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f75,plain,(
    r2_hidden(sK5(sK3,sK4),sK4) ),
    inference(unit_resulting_resolution,[],[f67,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f67,plain,(
    sP0(sK3,sK4) ),
    inference(unit_resulting_resolution,[],[f37,f38,f40,f43,f41,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP0(X0,X1)
      | v2_tex_2(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | sP0(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f12,f21])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f43,plain,(
    ~ v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f37,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f430,plain,(
    m1_subset_1(k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5(sK3,sK4))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(superposition,[],[f119,f89])).

fof(f119,plain,(
    ! [X0] : m1_subset_1(k2_pre_topc(sK3,k9_subset_1(u1_struct_0(sK3),sK4,X0)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unit_resulting_resolution,[],[f40,f100,f50])).

fof(f100,plain,(
    ! [X2] : m1_subset_1(k9_subset_1(u1_struct_0(sK3),sK4,X2),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(superposition,[],[f68,f69])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:07:30 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.50  % (25045)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.23/0.50  % (25037)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.23/0.50  % (25042)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.23/0.50  % (25050)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.23/0.54  % (25045)Refutation found. Thanks to Tanya!
% 0.23/0.54  % SZS status Theorem for theBenchmark
% 0.23/0.54  % SZS output start Proof for theBenchmark
% 0.23/0.54  fof(f528,plain,(
% 0.23/0.54    $false),
% 0.23/0.54    inference(subsumption_resolution,[],[f430,f527])).
% 0.23/0.54  fof(f527,plain,(
% 0.23/0.54    ~m1_subset_1(k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5(sK3,sK4))),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.23/0.54    inference(unit_resulting_resolution,[],[f67,f89,f433,f46])).
% 0.23/0.54  fof(f46,plain,(
% 0.23/0.54    ( ! [X0,X3,X1] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK5(X0,X1)) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~sP0(X0,X1)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f31])).
% 0.23/0.54  fof(f31,plain,(
% 0.23/0.54    ! [X0,X1] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK5(X0,X1)) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK5(X0,X1),X1) & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))) | ~sP0(X0,X1))),
% 0.23/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f30])).
% 0.23/0.54  fof(f30,plain,(
% 0.23/0.54    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK5(X0,X1)) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK5(X0,X1),X1) & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))))),
% 0.23/0.54    introduced(choice_axiom,[])).
% 0.23/0.54  fof(f29,plain,(
% 0.23/0.54    ! [X0,X1] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~sP0(X0,X1))),
% 0.23/0.54    inference(nnf_transformation,[],[f21])).
% 0.23/0.54  fof(f21,plain,(
% 0.23/0.54    ! [X0,X1] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~sP0(X0,X1))),
% 0.23/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.23/0.54  fof(f433,plain,(
% 0.23/0.54    v3_pre_topc(k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5(sK3,sK4))),sK3)),
% 0.23/0.54    inference(superposition,[],[f157,f89])).
% 0.23/0.54  fof(f157,plain,(
% 0.23/0.54    ( ! [X0] : (v3_pre_topc(k2_pre_topc(sK3,k9_subset_1(u1_struct_0(sK3),sK4,X0)),sK3)) )),
% 0.23/0.54    inference(superposition,[],[f136,f69])).
% 0.23/0.54  fof(f69,plain,(
% 0.23/0.54    ( ! [X0] : (k9_subset_1(u1_struct_0(sK3),X0,sK4) = k9_subset_1(u1_struct_0(sK3),sK4,X0)) )),
% 0.23/0.54    inference(unit_resulting_resolution,[],[f41,f48])).
% 0.23/0.54  fof(f48,plain,(
% 0.23/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f13])).
% 0.23/0.54  fof(f13,plain,(
% 0.23/0.54    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.23/0.54    inference(ennf_transformation,[],[f1])).
% 0.23/0.54  fof(f1,axiom,(
% 0.23/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 0.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).
% 0.23/0.54  fof(f41,plain,(
% 0.23/0.54    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.23/0.54    inference(cnf_transformation,[],[f28])).
% 0.23/0.54  fof(f28,plain,(
% 0.23/0.54    (~v2_tex_2(sK4,sK3) & ! [X2] : (k6_domain_1(u1_struct_0(sK3),X2) = k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X2))) | ~r2_hidden(X2,sK4) | ~m1_subset_1(X2,u1_struct_0(sK3))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK3) & v3_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 0.23/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f10,f27,f26])).
% 0.23/0.54  fof(f26,plain,(
% 0.23/0.54    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & ! [X2] : (k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v2_tex_2(X1,sK3) & ! [X2] : (k6_domain_1(u1_struct_0(sK3),X2) = k9_subset_1(u1_struct_0(sK3),X1,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X2))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(sK3))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK3) & v3_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 0.23/0.54    introduced(choice_axiom,[])).
% 0.23/0.54  fof(f27,plain,(
% 0.23/0.54    ? [X1] : (~v2_tex_2(X1,sK3) & ! [X2] : (k6_domain_1(u1_struct_0(sK3),X2) = k9_subset_1(u1_struct_0(sK3),X1,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X2))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(sK3))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))) => (~v2_tex_2(sK4,sK3) & ! [X2] : (k6_domain_1(u1_struct_0(sK3),X2) = k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X2))) | ~r2_hidden(X2,sK4) | ~m1_subset_1(X2,u1_struct_0(sK3))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))))),
% 0.23/0.54    introduced(choice_axiom,[])).
% 0.23/0.54  fof(f10,plain,(
% 0.23/0.54    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & ! [X2] : (k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.23/0.54    inference(flattening,[],[f9])).
% 0.23/0.54  fof(f9,plain,(
% 0.23/0.54    ? [X0] : (? [X1] : ((~v2_tex_2(X1,X0) & ! [X2] : ((k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.23/0.54    inference(ennf_transformation,[],[f8])).
% 0.23/0.54  fof(f8,negated_conjecture,(
% 0.23/0.54    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))) => v2_tex_2(X1,X0))))),
% 0.23/0.54    inference(negated_conjecture,[],[f7])).
% 0.23/0.54  fof(f7,conjecture,(
% 0.23/0.54    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))) => v2_tex_2(X1,X0))))),
% 0.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_tex_2)).
% 0.23/0.54  fof(f136,plain,(
% 0.23/0.54    ( ! [X0] : (v3_pre_topc(k2_pre_topc(sK3,k9_subset_1(u1_struct_0(sK3),X0,sK4)),sK3)) )),
% 0.23/0.54    inference(unit_resulting_resolution,[],[f61,f91,f92,f53])).
% 0.23/0.54  fof(f53,plain,(
% 0.23/0.54    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | v3_pre_topc(X2,X0) | ~sP1(X0)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f36])).
% 0.23/0.54  fof(f36,plain,(
% 0.23/0.54    ! [X0] : ((sP1(X0) | (~v3_pre_topc(sK6(X0),X0) & v4_pre_topc(sK6(X0),X0) & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP1(X0)))),
% 0.23/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f34,f35])).
% 0.23/0.54  fof(f35,plain,(
% 0.23/0.54    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK6(X0),X0) & v4_pre_topc(sK6(X0),X0) & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.23/0.54    introduced(choice_axiom,[])).
% 0.23/0.54  fof(f34,plain,(
% 0.23/0.54    ! [X0] : ((sP1(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP1(X0)))),
% 0.23/0.54    inference(rectify,[],[f33])).
% 0.23/0.54  fof(f33,plain,(
% 0.23/0.54    ! [X0] : ((sP1(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP1(X0)))),
% 0.23/0.54    inference(nnf_transformation,[],[f23])).
% 0.23/0.54  fof(f23,plain,(
% 0.23/0.54    ! [X0] : (sP1(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.23/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.23/0.54  fof(f92,plain,(
% 0.23/0.54    ( ! [X0] : (m1_subset_1(k2_pre_topc(sK3,k9_subset_1(u1_struct_0(sK3),X0,sK4)),k1_zfmisc_1(u1_struct_0(sK3)))) )),
% 0.23/0.54    inference(unit_resulting_resolution,[],[f40,f68,f50])).
% 0.23/0.54  fof(f50,plain,(
% 0.23/0.54    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f16])).
% 0.23/0.54  fof(f16,plain,(
% 0.23/0.54    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.23/0.54    inference(flattening,[],[f15])).
% 0.23/0.54  fof(f15,plain,(
% 0.23/0.54    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.23/0.54    inference(ennf_transformation,[],[f3])).
% 0.23/0.54  fof(f3,axiom,(
% 0.23/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.23/0.54  fof(f68,plain,(
% 0.23/0.54    ( ! [X0] : (m1_subset_1(k9_subset_1(u1_struct_0(sK3),X0,sK4),k1_zfmisc_1(u1_struct_0(sK3)))) )),
% 0.23/0.54    inference(unit_resulting_resolution,[],[f41,f49])).
% 0.23/0.54  fof(f49,plain,(
% 0.23/0.54    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.23/0.54    inference(cnf_transformation,[],[f14])).
% 0.23/0.54  fof(f14,plain,(
% 0.23/0.54    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.23/0.54    inference(ennf_transformation,[],[f2])).
% 0.23/0.54  fof(f2,axiom,(
% 0.23/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 0.23/0.54  fof(f40,plain,(
% 0.23/0.54    l1_pre_topc(sK3)),
% 0.23/0.54    inference(cnf_transformation,[],[f28])).
% 0.23/0.54  fof(f91,plain,(
% 0.23/0.54    ( ! [X0] : (v4_pre_topc(k2_pre_topc(sK3,k9_subset_1(u1_struct_0(sK3),X0,sK4)),sK3)) )),
% 0.23/0.54    inference(unit_resulting_resolution,[],[f38,f40,f68,f58])).
% 0.23/0.54  fof(f58,plain,(
% 0.23/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f20])).
% 0.23/0.54  fof(f20,plain,(
% 0.23/0.54    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.23/0.54    inference(flattening,[],[f19])).
% 0.23/0.54  fof(f19,plain,(
% 0.23/0.54    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.23/0.54    inference(ennf_transformation,[],[f4])).
% 0.23/0.54  fof(f4,axiom,(
% 0.23/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 0.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).
% 0.23/0.54  fof(f38,plain,(
% 0.23/0.54    v2_pre_topc(sK3)),
% 0.23/0.54    inference(cnf_transformation,[],[f28])).
% 0.23/0.54  fof(f61,plain,(
% 0.23/0.54    sP1(sK3)),
% 0.23/0.54    inference(unit_resulting_resolution,[],[f39,f60,f51])).
% 0.23/0.54  fof(f51,plain,(
% 0.23/0.54    ( ! [X0] : (~sP2(X0) | ~v3_tdlat_3(X0) | sP1(X0)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f32])).
% 0.23/0.54  fof(f32,plain,(
% 0.23/0.54    ! [X0] : (((v3_tdlat_3(X0) | ~sP1(X0)) & (sP1(X0) | ~v3_tdlat_3(X0))) | ~sP2(X0))),
% 0.23/0.54    inference(nnf_transformation,[],[f24])).
% 0.23/0.54  fof(f24,plain,(
% 0.23/0.54    ! [X0] : ((v3_tdlat_3(X0) <=> sP1(X0)) | ~sP2(X0))),
% 0.23/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.23/0.54  fof(f60,plain,(
% 0.23/0.54    sP2(sK3)),
% 0.23/0.54    inference(unit_resulting_resolution,[],[f38,f40,f57])).
% 0.23/0.54  fof(f57,plain,(
% 0.23/0.54    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | sP2(X0)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f25])).
% 0.23/0.54  fof(f25,plain,(
% 0.23/0.54    ! [X0] : (sP2(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.23/0.54    inference(definition_folding,[],[f18,f24,f23])).
% 0.23/0.54  fof(f18,plain,(
% 0.23/0.54    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.23/0.54    inference(flattening,[],[f17])).
% 0.23/0.54  fof(f17,plain,(
% 0.23/0.54    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.23/0.54    inference(ennf_transformation,[],[f5])).
% 0.23/0.54  fof(f5,axiom,(
% 0.23/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_pre_topc(X1,X0)))))),
% 0.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).
% 0.23/0.54  fof(f39,plain,(
% 0.23/0.54    v3_tdlat_3(sK3)),
% 0.23/0.54    inference(cnf_transformation,[],[f28])).
% 0.23/0.54  fof(f89,plain,(
% 0.23/0.54    k6_domain_1(u1_struct_0(sK3),sK5(sK3,sK4)) = k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5(sK3,sK4))))),
% 0.23/0.54    inference(unit_resulting_resolution,[],[f75,f74,f42])).
% 0.23/0.54  fof(f42,plain,(
% 0.23/0.54    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK3)) | ~r2_hidden(X2,sK4) | k6_domain_1(u1_struct_0(sK3),X2) = k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X2)))) )),
% 0.23/0.54    inference(cnf_transformation,[],[f28])).
% 0.23/0.54  fof(f74,plain,(
% 0.23/0.54    m1_subset_1(sK5(sK3,sK4),u1_struct_0(sK3))),
% 0.23/0.54    inference(unit_resulting_resolution,[],[f67,f44])).
% 0.23/0.54  fof(f44,plain,(
% 0.23/0.54    ( ! [X0,X1] : (m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) | ~sP0(X0,X1)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f31])).
% 0.23/0.54  fof(f75,plain,(
% 0.23/0.54    r2_hidden(sK5(sK3,sK4),sK4)),
% 0.23/0.54    inference(unit_resulting_resolution,[],[f67,f45])).
% 0.23/0.54  fof(f45,plain,(
% 0.23/0.54    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X1) | ~sP0(X0,X1)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f31])).
% 0.23/0.54  fof(f67,plain,(
% 0.23/0.54    sP0(sK3,sK4)),
% 0.23/0.54    inference(unit_resulting_resolution,[],[f37,f38,f40,f43,f41,f47])).
% 0.23/0.54  fof(f47,plain,(
% 0.23/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP0(X0,X1) | v2_tex_2(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f22])).
% 0.23/0.54  fof(f22,plain,(
% 0.23/0.54    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | sP0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.23/0.54    inference(definition_folding,[],[f12,f21])).
% 0.23/0.54  fof(f12,plain,(
% 0.23/0.54    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.23/0.54    inference(flattening,[],[f11])).
% 0.23/0.54  fof(f11,plain,(
% 0.23/0.54    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) | ? [X2] : ((! [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2) | ~v3_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.23/0.54    inference(ennf_transformation,[],[f6])).
% 0.23/0.54  fof(f6,axiom,(
% 0.23/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k6_domain_1(u1_struct_0(X0),X2) & v3_pre_topc(X3,X0))) & r2_hidden(X2,X1))) => v2_tex_2(X1,X0))))),
% 0.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_tex_2)).
% 0.23/0.54  fof(f43,plain,(
% 0.23/0.54    ~v2_tex_2(sK4,sK3)),
% 0.23/0.54    inference(cnf_transformation,[],[f28])).
% 0.23/0.54  fof(f37,plain,(
% 0.23/0.54    ~v2_struct_0(sK3)),
% 0.23/0.54    inference(cnf_transformation,[],[f28])).
% 0.23/0.54  fof(f430,plain,(
% 0.23/0.54    m1_subset_1(k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5(sK3,sK4))),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.23/0.54    inference(superposition,[],[f119,f89])).
% 0.23/0.54  fof(f119,plain,(
% 0.23/0.54    ( ! [X0] : (m1_subset_1(k2_pre_topc(sK3,k9_subset_1(u1_struct_0(sK3),sK4,X0)),k1_zfmisc_1(u1_struct_0(sK3)))) )),
% 0.23/0.54    inference(unit_resulting_resolution,[],[f40,f100,f50])).
% 0.23/0.54  fof(f100,plain,(
% 0.23/0.54    ( ! [X2] : (m1_subset_1(k9_subset_1(u1_struct_0(sK3),sK4,X2),k1_zfmisc_1(u1_struct_0(sK3)))) )),
% 0.23/0.54    inference(superposition,[],[f68,f69])).
% 0.23/0.54  % SZS output end Proof for theBenchmark
% 0.23/0.54  % (25045)------------------------------
% 0.23/0.54  % (25045)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (25045)Termination reason: Refutation
% 0.23/0.54  
% 0.23/0.54  % (25045)Memory used [KB]: 2046
% 0.23/0.54  % (25045)Time elapsed: 0.093 s
% 0.23/0.54  % (25045)------------------------------
% 0.23/0.54  % (25045)------------------------------
% 0.23/0.54  % (25028)Success in time 0.17 s
%------------------------------------------------------------------------------
