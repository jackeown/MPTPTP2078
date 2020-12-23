%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:23 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 163 expanded)
%              Number of leaves         :   14 (  45 expanded)
%              Depth                    :   19
%              Number of atoms          :  342 ( 916 expanded)
%              Number of equality atoms :   14 (  15 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f158,plain,(
    $false ),
    inference(resolution,[],[f154,f54])).

fof(f54,plain,(
    ! [X0] : v1_xboole_0(sK6(X0)) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( v1_xboole_0(sK6(X0))
      & m1_subset_1(sK6(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f1,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_xboole_0(sK6(X0))
        & m1_subset_1(sK6(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).

fof(f154,plain,(
    ! [X0] : ~ v1_xboole_0(X0) ),
    inference(subsumption_resolution,[],[f153,f40])).

fof(f40,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f153,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f148,f57])).

fof(f57,plain,(
    ! [X2,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | sP7(X1) ) ),
    inference(cnf_transformation,[],[f57_D])).

fof(f57_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ v1_xboole_0(X2)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) )
    <=> ~ sP7(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).

fof(f148,plain,(
    ~ sP7(k1_xboole_0) ),
    inference(resolution,[],[f126,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP7(X1) ) ),
    inference(general_splitting,[],[f56,f57_D])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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

fof(f126,plain,(
    r2_hidden(sK3(sK2,k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[],[f122,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK3(X0,X1))),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK4(X0,X1))))
          & sK3(X0,X1) != sK4(X0,X1)
          & r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X1)
          & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
          & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) )
      & ( ! [X4] :
            ( ! [X5] :
                ( r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X5)))
                | X4 = X5
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X1)
                | ~ m1_subset_1(X5,u1_struct_0(X0)) )
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f27,f29,f28])).

fof(f28,plain,(
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
            ( ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK3(X0,X1))),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X3)))
            & sK3(X0,X1) != X3
            & r2_hidden(X3,X1)
            & r2_hidden(sK3(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK3(X0,X1))),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X3)))
          & sK3(X0,X1) != X3
          & r2_hidden(X3,X1)
          & r2_hidden(sK3(X0,X1),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK3(X0,X1))),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK4(X0,X1))))
        & sK3(X0,X1) != sK4(X0,X1)
        & r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X1)
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
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

fof(f122,plain,(
    ~ sP0(sK2,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f121,f98])).

fof(f98,plain,(
    sP1(k1_xboole_0,sK2) ),
    inference(resolution,[],[f88,f40])).

fof(f88,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(X2,sK2) ) ),
    inference(subsumption_resolution,[],[f87,f35])).

fof(f35,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ! [X1] :
        ( ~ v3_tex_2(X1,sK2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
    & l1_pre_topc(sK2)
    & v3_tdlat_3(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f22])).

fof(f22,plain,
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

fof(f11,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
       => ? [X1] :
            ( v3_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tex_2)).

fof(f87,plain,(
    ! [X2] :
      ( sP1(X2,sK2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f86,f36])).

fof(f36,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f86,plain,(
    ! [X2] :
      ( sP1(X2,sK2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f79,f37])).

fof(f37,plain,(
    v3_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f79,plain,(
    ! [X2] :
      ( sP1(X2,sK2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v3_tdlat_3(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f38,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( sP1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f13,f20,f19])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ( v2_tex_2(X1,X0)
      <=> sP0(X0,X1) )
      | ~ sP1(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f38,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f121,plain,
    ( ~ sP0(sK2,k1_xboole_0)
    | ~ sP1(k1_xboole_0,sK2) ),
    inference(resolution,[],[f118,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X0,X1)
      | ~ sP0(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( v2_tex_2(X0,X1)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v2_tex_2(X0,X1) ) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ( ( v2_tex_2(X1,X0)
          | ~ sP0(X0,X1) )
        & ( sP0(X0,X1)
          | ~ v2_tex_2(X1,X0) ) )
      | ~ sP1(X1,X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f118,plain,(
    ~ v2_tex_2(k1_xboole_0,sK2) ),
    inference(resolution,[],[f116,f40])).

fof(f116,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v2_tex_2(X2,sK2) ) ),
    inference(subsumption_resolution,[],[f96,f85])).

fof(f85,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v2_tex_2(X1,sK2)
      | v3_tex_2(sK5(sK2),sK2) ) ),
    inference(subsumption_resolution,[],[f84,f35])).

fof(f84,plain,(
    ! [X1] :
      ( v3_tex_2(sK5(sK2),sK2)
      | ~ v2_tex_2(X1,sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f83,f36])).

fof(f83,plain,(
    ! [X1] :
      ( v3_tex_2(sK5(sK2),sK2)
      | ~ v2_tex_2(X1,sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f78,f37])).

fof(f78,plain,(
    ! [X1] :
      ( v3_tex_2(sK5(sK2),sK2)
      | ~ v2_tex_2(X1,sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v3_tdlat_3(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f38,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v3_tex_2(sK5(X0),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(sK5(X0),X0)
            & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f15,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X2] :
          ( v3_tex_2(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v3_tex_2(sK5(X0),X0)
        & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
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
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
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

fof(f96,plain,(
    ! [X2] :
      ( ~ v3_tex_2(sK5(sK2),sK2)
      | ~ v2_tex_2(X2,sK2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(subsumption_resolution,[],[f95,f35])).

fof(f95,plain,(
    ! [X2] :
      ( ~ v3_tex_2(sK5(sK2),sK2)
      | ~ v2_tex_2(X2,sK2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f94,f36])).

fof(f94,plain,(
    ! [X2] :
      ( ~ v3_tex_2(sK5(sK2),sK2)
      | ~ v2_tex_2(X2,sK2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f93,f37])).

fof(f93,plain,(
    ! [X2] :
      ( ~ v3_tex_2(sK5(sK2),sK2)
      | ~ v2_tex_2(X2,sK2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v3_tdlat_3(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f91,f38])).

fof(f91,plain,(
    ! [X2] :
      ( ~ v3_tex_2(sK5(sK2),sK2)
      | ~ v2_tex_2(X2,sK2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_pre_topc(sK2)
      | ~ v3_tdlat_3(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f39,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f39,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v3_tex_2(X1,sK2) ) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.33  % Computer   : n021.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 11:13:49 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.21/0.45  % (20810)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.47  % (20819)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.47  % (20819)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (20805)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f158,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(resolution,[],[f154,f54])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ( ! [X0] : (v1_xboole_0(sK6(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(sK6(X0)) & m1_subset_1(sK6(X0),k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f1,f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (v1_xboole_0(sK6(X0)) & m1_subset_1(sK6(X0),k1_zfmisc_1(X0))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).
% 0.21/0.48  fof(f154,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_xboole_0(X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f153,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.48  fof(f153,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_xboole_0(X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(resolution,[],[f148,f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X2,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | sP7(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f57_D])).
% 0.21/0.48  fof(f57_D,plain,(
% 0.21/0.48    ( ! [X1] : (( ! [X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2))) ) <=> ~sP7(X1)) )),
% 0.21/0.48    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).
% 0.21/0.48  fof(f148,plain,(
% 0.21/0.48    ~sP7(k1_xboole_0)),
% 0.21/0.48    inference(resolution,[],[f126,f58])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~sP7(X1)) )),
% 0.21/0.48    inference(general_splitting,[],[f56,f57_D])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    r2_hidden(sK3(sK2,k1_xboole_0),k1_xboole_0)),
% 0.21/0.48    inference(resolution,[],[f122,f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X0,X1] : (sP0(X0,X1) | r2_hidden(sK3(X0,X1),X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0,X1] : ((sP0(X0,X1) | ((~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK3(X0,X1))),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK4(X0,X1)))) & sK3(X0,X1) != sK4(X0,X1) & r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK3(X0,X1),X1) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X5))) | X4 = X5 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~sP0(X0,X1)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f27,f29,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X1,X0] : (? [X2] : (? [X3] : (~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X3))) & X2 != X3 & r2_hidden(X3,X1) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK3(X0,X1))),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X3))) & sK3(X0,X1) != X3 & r2_hidden(X3,X1) & r2_hidden(sK3(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X1,X0] : (? [X3] : (~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK3(X0,X1))),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X3))) & sK3(X0,X1) != X3 & r2_hidden(X3,X1) & r2_hidden(sK3(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK3(X0,X1))),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK4(X0,X1)))) & sK3(X0,X1) != sK4(X0,X1) & r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK3(X0,X1),X1) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (? [X3] : (~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X3))) & X2 != X3 & r2_hidden(X3,X1) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X5))) | X4 = X5 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~sP0(X0,X1)))),
% 0.21/0.48    inference(rectify,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (? [X3] : (~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X3))) & X2 != X3 & r2_hidden(X3,X1) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X3))) | X2 = X3 | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~sP0(X0,X1)))),
% 0.21/0.48    inference(nnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2] : (! [X3] : (r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X3))) | X2 = X3 | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))))),
% 0.21/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.48  fof(f122,plain,(
% 0.21/0.48    ~sP0(sK2,k1_xboole_0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f121,f98])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    sP1(k1_xboole_0,sK2)),
% 0.21/0.48    inference(resolution,[],[f88,f40])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(X2,sK2)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f87,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ~v2_struct_0(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X1] : (~v3_tex_2(X1,sK2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v3_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ? [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (! [X1] : (~v3_tex_2(X1,sK2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v3_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ? [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ? [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.48    inference(negated_conjecture,[],[f7])).
% 0.21/0.48  fof(f7,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tex_2)).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    ( ! [X2] : (sP1(X2,sK2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) | v2_struct_0(sK2)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f86,f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    v2_pre_topc(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    ( ! [X2] : (sP1(X2,sK2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f79,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    v3_tdlat_3(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    ( ! [X2] : (sP1(X2,sK2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) | ~v3_tdlat_3(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.21/0.48    inference(resolution,[],[f38,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X0,X1] : (sP1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (sP1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(definition_folding,[],[f13,f20,f19])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X1,X0] : ((v2_tex_2(X1,X0) <=> sP0(X0,X1)) | ~sP1(X1,X0))),
% 0.21/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (! [X3] : (r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X3))) | X2 = X3 | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (! [X3] : (((r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X3))) | X2 = X3) | (~r2_hidden(X3,X1) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r2_hidden(X3,X1) & r2_hidden(X2,X1)) => (r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X3))) | X2 = X3)))))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_tex_2)).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    l1_pre_topc(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f121,plain,(
% 0.21/0.48    ~sP0(sK2,k1_xboole_0) | ~sP1(k1_xboole_0,sK2)),
% 0.21/0.48    inference(resolution,[],[f118,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v2_tex_2(X0,X1) | ~sP0(X1,X0) | ~sP1(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0,X1] : (((v2_tex_2(X0,X1) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v2_tex_2(X0,X1))) | ~sP1(X0,X1))),
% 0.21/0.48    inference(rectify,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X1,X0] : (((v2_tex_2(X1,X0) | ~sP0(X0,X1)) & (sP0(X0,X1) | ~v2_tex_2(X1,X0))) | ~sP1(X1,X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f20])).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    ~v2_tex_2(k1_xboole_0,sK2)),
% 0.21/0.48    inference(resolution,[],[f116,f40])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) | ~v2_tex_2(X2,sK2)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f96,f85])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | ~v2_tex_2(X1,sK2) | v3_tex_2(sK5(sK2),sK2)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f84,f35])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    ( ! [X1] : (v3_tex_2(sK5(sK2),sK2) | ~v2_tex_2(X1,sK2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | v2_struct_0(sK2)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f83,f36])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    ( ! [X1] : (v3_tex_2(sK5(sK2),sK2) | ~v2_tex_2(X1,sK2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f78,f37])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    ( ! [X1] : (v3_tex_2(sK5(sK2),sK2) | ~v2_tex_2(X1,sK2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | ~v3_tdlat_3(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.21/0.48    inference(resolution,[],[f38,f52])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v3_tex_2(sK5(X0),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v3_tex_2(sK5(X0),X0) & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f15,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ! [X0] : (? [X2] : (v3_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (v3_tex_2(sK5(X0),X0) & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (? [X2] : (v3_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((? [X2] : (v3_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~v3_tex_2(X2,X0)) & v2_tex_2(X1,X0))))),
% 0.21/0.48    inference(pure_predicate_removal,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(v3_tex_2(X2,X0) & r1_tarski(X1,X2))) & v2_tex_2(X1,X0))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tex_2)).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    ( ! [X2] : (~v3_tex_2(sK5(sK2),sK2) | ~v2_tex_2(X2,sK2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f95,f35])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    ( ! [X2] : (~v3_tex_2(sK5(sK2),sK2) | ~v2_tex_2(X2,sK2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) | v2_struct_0(sK2)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f94,f36])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    ( ! [X2] : (~v3_tex_2(sK5(sK2),sK2) | ~v2_tex_2(X2,sK2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f93,f37])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    ( ! [X2] : (~v3_tex_2(sK5(sK2),sK2) | ~v2_tex_2(X2,sK2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) | ~v3_tdlat_3(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f91,f38])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    ( ! [X2] : (~v3_tex_2(sK5(sK2),sK2) | ~v2_tex_2(X2,sK2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2) | ~v3_tdlat_3(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.21/0.48    inference(resolution,[],[f39,f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f32])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | ~v3_tex_2(X1,sK2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (20819)------------------------------
% 0.21/0.48  % (20819)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (20819)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (20819)Memory used [KB]: 1663
% 0.21/0.48  % (20819)Time elapsed: 0.065 s
% 0.21/0.48  % (20819)------------------------------
% 0.21/0.48  % (20819)------------------------------
% 0.21/0.49  % (20792)Success in time 0.136 s
%------------------------------------------------------------------------------
