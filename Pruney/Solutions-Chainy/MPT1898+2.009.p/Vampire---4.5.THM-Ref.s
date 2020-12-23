%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 374 expanded)
%              Number of leaves         :   14 ( 103 expanded)
%              Depth                    :   24
%              Number of atoms          :  361 (2081 expanded)
%              Number of equality atoms :   25 (  56 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f296,plain,(
    $false ),
    inference(subsumption_resolution,[],[f293,f42])).

fof(f42,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f293,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(trivial_inequality_removal,[],[f285])).

fof(f285,plain,
    ( sK4(sK3,k1_xboole_0) != sK4(sK3,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(superposition,[],[f101,f219])).

fof(f219,plain,(
    sK4(sK3,k1_xboole_0) = sK5(sK3,k1_xboole_0) ),
    inference(resolution,[],[f213,f127])).

fof(f127,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,sK4(sK3,k1_xboole_0))
      | sK4(sK3,k1_xboole_0) = X1 ) ),
    inference(resolution,[],[f124,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f124,plain,(
    ! [X11] : r1_tarski(sK4(sK3,k1_xboole_0),X11) ),
    inference(resolution,[],[f117,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f117,plain,(
    ! [X5] : m1_subset_1(sK4(sK3,k1_xboole_0),X5) ),
    inference(subsumption_resolution,[],[f115,f42])).

fof(f115,plain,(
    ! [X5] :
      ( m1_subset_1(sK4(sK3,k1_xboole_0),X5)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(resolution,[],[f103,f42])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | m1_subset_1(sK4(sK3,X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(resolution,[],[f99,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f99,plain,(
    ! [X3] :
      ( r2_hidden(sK4(sK3,X3),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(resolution,[],[f95,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f27,f29,f28])).

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
            ( ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK4(X0,X1))),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X3)))
            & sK4(X0,X1) != X3
            & r2_hidden(X3,X1)
            & r2_hidden(sK4(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

% (11303)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
fof(f29,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
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

fof(f95,plain,(
    ! [X0] :
      ( ~ sP0(sK3,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(subsumption_resolution,[],[f94,f84])).

fof(f84,plain,(
    ! [X1] :
      ( sP1(X1,sK3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(subsumption_resolution,[],[f83,f37])).

fof(f37,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ! [X1] :
        ( ~ v3_tex_2(X1,sK3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) )
    & l1_pre_topc(sK3)
    & v3_tdlat_3(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f22])).

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
          ( ~ v3_tex_2(X1,sK3)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) )
      & l1_pre_topc(sK3)
      & v3_tdlat_3(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
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

fof(f83,plain,(
    ! [X1] :
      ( sP1(X1,sK3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f82,f38])).

fof(f38,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f82,plain,(
    ! [X1] :
      ( sP1(X1,sK3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f78,f39])).

fof(f39,plain,(
    v3_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f78,plain,(
    ! [X1] :
      ( sP1(X1,sK3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ v3_tdlat_3(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f40,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( sP1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f12,f18,f17])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ( v2_tex_2(X1,X0)
      <=> sP0(X0,X1) )
      | ~ sP1(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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

fof(f40,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f23])).

% (11298)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
fof(f94,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ sP0(sK3,X0)
      | ~ sP1(X0,sK3) ) ),
    inference(resolution,[],[f91,f44])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f91,plain,(
    ! [X0] :
      ( ~ v2_tex_2(X0,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(subsumption_resolution,[],[f90,f37])).

fof(f90,plain,(
    ! [X0] :
      ( ~ v2_tex_2(X0,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f89,f38])).

fof(f89,plain,(
    ! [X0] :
      ( ~ v2_tex_2(X0,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f88,f39])).

fof(f88,plain,(
    ! [X0] :
      ( ~ v2_tex_2(X0,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ v3_tdlat_3(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f87,f40])).

fof(f87,plain,(
    ! [X0] :
      ( ~ v2_tex_2(X0,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ l1_pre_topc(sK3)
      | ~ v3_tdlat_3(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f86,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP2(X0,X1)
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f14,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( v3_tex_2(X2,X0)
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ sP2(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( v3_tex_2(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( v3_tex_2(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tex_2(X1,X0)
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
         => ~ ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ~ ( v3_tex_2(X2,X0)
                      & r1_tarski(X1,X2) ) )
              & v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tex_2)).

fof(f86,plain,(
    ! [X0] : ~ sP2(sK3,X0) ),
    inference(subsumption_resolution,[],[f85,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v3_tex_2(sK6(X0,X1),X0)
        & r1_tarski(X1,sK6(X0,X1))
        & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ sP2(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f31,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v3_tex_2(X2,X0)
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v3_tex_2(sK6(X0,X1),X0)
        & r1_tarski(X1,sK6(X0,X1))
        & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( v3_tex_2(X2,X0)
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ sP2(X0,X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f85,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK6(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ sP2(sK3,X0) ) ),
    inference(resolution,[],[f41,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v3_tex_2(sK6(X0,X1),X0)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f41,plain,(
    ! [X1] :
      ( ~ v3_tex_2(X1,sK3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f213,plain,(
    ! [X12] : r1_tarski(sK5(sK3,k1_xboole_0),X12) ),
    inference(resolution,[],[f203,f60])).

fof(f203,plain,(
    ! [X7] : m1_subset_1(sK5(sK3,k1_xboole_0),X7) ),
    inference(subsumption_resolution,[],[f199,f42])).

fof(f199,plain,(
    ! [X7] :
      ( m1_subset_1(sK5(sK3,k1_xboole_0),X7)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(resolution,[],[f106,f42])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | m1_subset_1(sK5(sK3,X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(resolution,[],[f100,f62])).

fof(f100,plain,(
    ! [X4] :
      ( r2_hidden(sK5(sK3,X4),X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(resolution,[],[f95,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f101,plain,(
    ! [X5] :
      ( sK4(sK3,X5) != sK5(sK3,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(resolution,[],[f95,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | sK4(X0,X1) != sK5(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:03:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (11296)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.49  % (11304)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.50  % (11296)Refutation not found, incomplete strategy% (11296)------------------------------
% 0.21/0.50  % (11296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (11296)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (11296)Memory used [KB]: 10490
% 0.21/0.50  % (11296)Time elapsed: 0.003 s
% 0.21/0.50  % (11296)------------------------------
% 0.21/0.50  % (11296)------------------------------
% 0.21/0.50  % (11297)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (11306)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.51  % (11301)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (11297)Refutation not found, incomplete strategy% (11297)------------------------------
% 0.21/0.51  % (11297)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (11297)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (11297)Memory used [KB]: 10618
% 0.21/0.51  % (11297)Time elapsed: 0.088 s
% 0.21/0.51  % (11297)------------------------------
% 0.21/0.51  % (11297)------------------------------
% 0.21/0.51  % (11299)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (11302)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (11302)Refutation not found, incomplete strategy% (11302)------------------------------
% 0.21/0.51  % (11302)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (11302)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (11302)Memory used [KB]: 10490
% 0.21/0.51  % (11302)Time elapsed: 0.001 s
% 0.21/0.51  % (11302)------------------------------
% 0.21/0.51  % (11302)------------------------------
% 0.21/0.51  % (11310)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (11318)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (11301)Refutation not found, incomplete strategy% (11301)------------------------------
% 0.21/0.51  % (11301)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (11304)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f296,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f293,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.51  fof(f293,plain,(
% 0.21/0.51    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f285])).
% 0.21/0.51  fof(f285,plain,(
% 0.21/0.51    sK4(sK3,k1_xboole_0) != sK4(sK3,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.21/0.51    inference(superposition,[],[f101,f219])).
% 0.21/0.51  fof(f219,plain,(
% 0.21/0.51    sK4(sK3,k1_xboole_0) = sK5(sK3,k1_xboole_0)),
% 0.21/0.51    inference(resolution,[],[f213,f127])).
% 0.21/0.51  fof(f127,plain,(
% 0.21/0.51    ( ! [X1] : (~r1_tarski(X1,sK4(sK3,k1_xboole_0)) | sK4(sK3,k1_xboole_0) = X1) )),
% 0.21/0.51    inference(resolution,[],[f124,f59])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.51    inference(flattening,[],[f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.51  fof(f124,plain,(
% 0.21/0.51    ( ! [X11] : (r1_tarski(sK4(sK3,k1_xboole_0),X11)) )),
% 0.21/0.51    inference(resolution,[],[f117,f60])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.51    inference(nnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.51  fof(f117,plain,(
% 0.21/0.51    ( ! [X5] : (m1_subset_1(sK4(sK3,k1_xboole_0),X5)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f115,f42])).
% 0.21/0.51  fof(f115,plain,(
% 0.21/0.51    ( ! [X5] : (m1_subset_1(sK4(sK3,k1_xboole_0),X5) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))) )),
% 0.21/0.51    inference(resolution,[],[f103,f42])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | m1_subset_1(sK4(sK3,X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))) )),
% 0.21/0.51    inference(resolution,[],[f99,f62])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.51    inference(flattening,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    ( ! [X3] : (r2_hidden(sK4(sK3,X3),X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))) )),
% 0.21/0.51    inference(resolution,[],[f95,f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X0,X1] : (sP0(X0,X1) | r2_hidden(sK4(X0,X1),X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0,X1] : ((sP0(X0,X1) | ((~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK4(X0,X1))),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK5(X0,X1)))) & sK4(X0,X1) != sK5(X0,X1) & r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK4(X0,X1),X1) & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X5))) | X4 = X5 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~sP0(X0,X1)))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f27,f29,f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X1,X0] : (? [X2] : (? [X3] : (~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X3))) & X2 != X3 & r2_hidden(X3,X1) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK4(X0,X1))),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X3))) & sK4(X0,X1) != X3 & r2_hidden(X3,X1) & r2_hidden(sK4(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  % (11303)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X1,X0] : (? [X3] : (~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK4(X0,X1))),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X3))) & sK4(X0,X1) != X3 & r2_hidden(X3,X1) & r2_hidden(sK4(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK4(X0,X1))),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK5(X0,X1)))) & sK4(X0,X1) != sK5(X0,X1) & r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK4(X0,X1),X1) & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (? [X3] : (~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X3))) & X2 != X3 & r2_hidden(X3,X1) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X5))) | X4 = X5 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~sP0(X0,X1)))),
% 0.21/0.51    inference(rectify,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (? [X3] : (~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X3))) & X2 != X3 & r2_hidden(X3,X1) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X3))) | X2 = X3 | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~sP0(X0,X1)))),
% 0.21/0.51    inference(nnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2] : (! [X3] : (r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X3))) | X2 = X3 | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    ( ! [X0] : (~sP0(sK3,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f94,f84])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    ( ! [X1] : (sP1(X1,sK3) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f83,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ~v2_struct_0(sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X1] : (~v3_tex_2(X1,sK3) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK3) & v3_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ? [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (! [X1] : (~v3_tex_2(X1,sK3) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK3) & v3_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ? [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f9])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    ? [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.51    inference(negated_conjecture,[],[f7])).
% 0.21/0.51  fof(f7,conjecture,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tex_2)).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    ( ! [X1] : (sP1(X1,sK3) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) | v2_struct_0(sK3)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f82,f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    v2_pre_topc(sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    ( ! [X1] : (sP1(X1,sK3) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f78,f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    v3_tdlat_3(sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ( ! [X1] : (sP1(X1,sK3) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) | ~v3_tdlat_3(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 0.21/0.51    inference(resolution,[],[f40,f52])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ( ! [X0,X1] : (sP1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (sP1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(definition_folding,[],[f12,f18,f17])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X1,X0] : ((v2_tex_2(X1,X0) <=> sP0(X0,X1)) | ~sP1(X1,X0))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (! [X3] : (r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X3))) | X2 = X3 | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (! [X3] : (((r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X3))) | X2 = X3) | (~r2_hidden(X3,X1) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r2_hidden(X3,X1) & r2_hidden(X2,X1)) => (r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X3))) | X2 = X3)))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_tex_2)).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    l1_pre_topc(sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  % (11298)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~sP0(sK3,X0) | ~sP1(X0,sK3)) )),
% 0.21/0.51    inference(resolution,[],[f91,f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v2_tex_2(X0,X1) | ~sP0(X1,X0) | ~sP1(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0,X1] : (((v2_tex_2(X0,X1) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v2_tex_2(X0,X1))) | ~sP1(X0,X1))),
% 0.21/0.51    inference(rectify,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X1,X0] : (((v2_tex_2(X1,X0) | ~sP0(X0,X1)) & (sP0(X0,X1) | ~v2_tex_2(X1,X0))) | ~sP1(X1,X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f18])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    ( ! [X0] : (~v2_tex_2(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f90,f37])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    ( ! [X0] : (~v2_tex_2(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | v2_struct_0(sK3)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f89,f38])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    ( ! [X0] : (~v2_tex_2(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f88,f39])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    ( ! [X0] : (~v2_tex_2(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~v3_tdlat_3(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f87,f40])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    ( ! [X0] : (~v2_tex_2(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK3) | ~v3_tdlat_3(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 0.21/0.51    inference(resolution,[],[f86,f56])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ( ! [X0,X1] : (sP2(X0,X1) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (sP2(X0,X1) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(definition_folding,[],[f14,f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1] : (? [X2] : (v3_tex_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP2(X0,X1))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (? [X2] : (v3_tex_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((? [X2] : ((v3_tex_2(X2,X0) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(v3_tex_2(X2,X0) & r1_tarski(X1,X2))) & v2_tex_2(X1,X0))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tex_2)).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    ( ! [X0] : (~sP2(sK3,X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f85,f53])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~sP2(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ! [X0,X1] : ((v3_tex_2(sK6(X0,X1),X0) & r1_tarski(X1,sK6(X0,X1)) & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~sP2(X0,X1))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f31,f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ! [X1,X0] : (? [X2] : (v3_tex_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (v3_tex_2(sK6(X0,X1),X0) & r1_tarski(X1,sK6(X0,X1)) & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0,X1] : (? [X2] : (v3_tex_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP2(X0,X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f20])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(sK6(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) | ~sP2(sK3,X0)) )),
% 0.21/0.51    inference(resolution,[],[f41,f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v3_tex_2(sK6(X0,X1),X0) | ~sP2(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X1] : (~v3_tex_2(X1,sK3) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f213,plain,(
% 0.21/0.51    ( ! [X12] : (r1_tarski(sK5(sK3,k1_xboole_0),X12)) )),
% 0.21/0.51    inference(resolution,[],[f203,f60])).
% 0.21/0.51  fof(f203,plain,(
% 0.21/0.51    ( ! [X7] : (m1_subset_1(sK5(sK3,k1_xboole_0),X7)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f199,f42])).
% 0.21/0.51  fof(f199,plain,(
% 0.21/0.51    ( ! [X7] : (m1_subset_1(sK5(sK3,k1_xboole_0),X7) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))) )),
% 0.21/0.51    inference(resolution,[],[f106,f42])).
% 0.21/0.51  fof(f106,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | m1_subset_1(sK5(sK3,X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))) )),
% 0.21/0.51    inference(resolution,[],[f100,f62])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    ( ! [X4] : (r2_hidden(sK5(sK3,X4),X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))) )),
% 0.21/0.51    inference(resolution,[],[f95,f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ( ! [X0,X1] : (sP0(X0,X1) | r2_hidden(sK5(X0,X1),X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    ( ! [X5] : (sK4(sK3,X5) != sK5(sK3,X5) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3)))) )),
% 0.21/0.51    inference(resolution,[],[f95,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X0,X1] : (sP0(X0,X1) | sK4(X0,X1) != sK5(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (11304)------------------------------
% 0.21/0.51  % (11304)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (11304)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (11304)Memory used [KB]: 1791
% 0.21/0.51  % (11304)Time elapsed: 0.091 s
% 0.21/0.51  % (11304)------------------------------
% 0.21/0.51  % (11304)------------------------------
% 0.21/0.51  % (11295)Success in time 0.15 s
%------------------------------------------------------------------------------
