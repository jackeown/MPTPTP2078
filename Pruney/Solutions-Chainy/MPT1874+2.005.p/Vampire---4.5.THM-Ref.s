%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:22 EST 2020

% Result     : Theorem 1.25s
% Output     : Refutation 1.25s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 241 expanded)
%              Number of leaves         :   18 (  82 expanded)
%              Depth                    :   22
%              Number of atoms          :  344 (1400 expanded)
%              Number of equality atoms :   34 ( 185 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f338,plain,(
    $false ),
    inference(subsumption_resolution,[],[f337,f74])).

fof(f74,plain,(
    m1_subset_1(sK4,sK3) ),
    inference(resolution,[],[f64,f51])).

fof(f51,plain,(
    r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK4) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)))
    & r2_hidden(sK4,sK3)
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & v2_tex_2(sK3,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f13,f29,f28,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k6_domain_1(u1_struct_0(sK2),X2) != k9_subset_1(u1_struct_0(sK2),X1,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X2)))
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(sK2)) )
          & v2_tex_2(X1,sK2)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k6_domain_1(u1_struct_0(sK2),X2) != k9_subset_1(u1_struct_0(sK2),X1,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X2)))
            & r2_hidden(X2,X1)
            & m1_subset_1(X2,u1_struct_0(sK2)) )
        & v2_tex_2(X1,sK2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( ? [X2] :
          ( k6_domain_1(u1_struct_0(sK2),X2) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X2)))
          & r2_hidden(X2,sK3)
          & m1_subset_1(X2,u1_struct_0(sK2)) )
      & v2_tex_2(sK3,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X2] :
        ( k6_domain_1(u1_struct_0(sK2),X2) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X2)))
        & r2_hidden(X2,sK3)
        & m1_subset_1(X2,u1_struct_0(sK2)) )
   => ( k6_domain_1(u1_struct_0(sK2),sK4) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)))
      & r2_hidden(sK4,sK3)
      & m1_subset_1(sK4,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tex_2(X1,X0)
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( r2_hidden(X2,X1)
                   => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,X1)
                 => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_tex_2)).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f337,plain,(
    ~ m1_subset_1(sK4,sK3) ),
    inference(subsumption_resolution,[],[f336,f72])).

fof(f72,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(resolution,[],[f62,f51])).

fof(f62,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK6(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f38,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f336,plain,
    ( v1_xboole_0(sK3)
    | ~ m1_subset_1(sK4,sK3) ),
    inference(duplicate_literal_removal,[],[f328])).

fof(f328,plain,
    ( v1_xboole_0(sK3)
    | ~ m1_subset_1(sK4,sK3)
    | ~ m1_subset_1(sK4,sK3)
    | v1_xboole_0(sK3) ),
    inference(resolution,[],[f304,f181])).

fof(f181,plain,(
    ! [X10] :
      ( ~ r1_tarski(k6_domain_1(X10,sK4),sK3)
      | ~ m1_subset_1(sK4,X10)
      | v1_xboole_0(X10) ) ),
    inference(subsumption_resolution,[],[f180,f77])).

fof(f77,plain,(
    ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f76,f72])).

fof(f76,plain,
    ( v1_xboole_0(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(resolution,[],[f54,f48])).

fof(f48,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f30])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f180,plain,(
    ! [X10] :
      ( ~ r1_tarski(k6_domain_1(X10,sK4),sK3)
      | ~ m1_subset_1(sK4,X10)
      | v1_xboole_0(X10)
      | v1_xboole_0(u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f159,f50])).

fof(f50,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f30])).

fof(f159,plain,(
    ! [X10] :
      ( ~ r1_tarski(k6_domain_1(X10,sK4),sK3)
      | ~ m1_subset_1(sK4,X10)
      | v1_xboole_0(X10)
      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
      | v1_xboole_0(u1_struct_0(sK2)) ) ),
    inference(superposition,[],[f141,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( k6_domain_1(X1,X0) = k6_domain_1(X2,X0)
      | ~ m1_subset_1(X0,X2)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1) ) ),
    inference(superposition,[],[f71,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f66,f53])).

fof(f53,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f141,plain,(
    ~ r1_tarski(k6_domain_1(u1_struct_0(sK2),sK4),sK3) ),
    inference(subsumption_resolution,[],[f140,f77])).

fof(f140,plain,
    ( ~ r1_tarski(k6_domain_1(u1_struct_0(sK2),sK4),sK3)
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f138,f50])).

fof(f138,plain,
    ( ~ r1_tarski(k6_domain_1(u1_struct_0(sK2),sK4),sK3)
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(resolution,[],[f117,f67])).

fof(f67,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f117,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(k6_domain_1(u1_struct_0(sK2),sK4),sK3) ),
    inference(subsumption_resolution,[],[f116,f110])).

fof(f110,plain,(
    sP0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f109,f49])).

fof(f49,plain,(
    v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f109,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | sP0(sK2,sK3) ),
    inference(resolution,[],[f107,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ v2_tex_2(X0,X1)
      | sP0(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( v2_tex_2(X0,X1)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v2_tex_2(X0,X1) ) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ( ( v2_tex_2(X1,X0)
          | ~ sP0(X0,X1) )
        & ( sP0(X0,X1)
          | ~ v2_tex_2(X1,X0) ) )
      | ~ sP1(X1,X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ( v2_tex_2(X1,X0)
      <=> sP0(X0,X1) )
      | ~ sP1(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f107,plain,(
    sP1(sK3,sK2) ),
    inference(subsumption_resolution,[],[f106,f45])).

fof(f45,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f106,plain,
    ( sP1(sK3,sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f105,f46])).

fof(f46,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f105,plain,
    ( sP1(sK3,sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f101,f47])).

fof(f47,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f101,plain,
    ( sP1(sK3,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f61,f48])).

% (18394)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f16,f25,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
          | ~ r1_tarski(X2,X1)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r1_tarski(X2,X1)
                 => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tex_2)).

fof(f116,plain,
    ( ~ r1_tarski(k6_domain_1(u1_struct_0(sK2),sK4),sK3)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ sP0(sK2,sK3) ),
    inference(trivial_inequality_removal,[],[f114])).

fof(f114,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK4) != k6_domain_1(u1_struct_0(sK2),sK4)
    | ~ r1_tarski(k6_domain_1(u1_struct_0(sK2),sK4),sK3)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ sP0(sK2,sK3) ),
    inference(superposition,[],[f52,f57])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
      | ~ r1_tarski(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( sK5(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK5(X0,X1)))
          & r1_tarski(sK5(X0,X1),X1)
          & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
            | ~ r1_tarski(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK5(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK5(X0,X1)))
        & r1_tarski(sK5(X0,X1),X1)
        & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
            & r1_tarski(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
            | ~ r1_tarski(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
            & r1_tarski(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
            | ~ r1_tarski(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f52,plain,(
    k6_domain_1(u1_struct_0(sK2),sK4) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) ),
    inference(cnf_transformation,[],[f30])).

fof(f304,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_domain_1(X1,X0),X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f287])).

fof(f287,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r1_tarski(k6_domain_1(X1,X0),X1)
      | r1_tarski(k6_domain_1(X1,X0),X1) ) ),
    inference(resolution,[],[f133,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f42,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f133,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(sK7(k6_domain_1(X2,X3),X4),X2)
      | ~ m1_subset_1(X3,X2)
      | v1_xboole_0(X2)
      | r1_tarski(k6_domain_1(X2,X3),X4) ) ),
    inference(resolution,[],[f95,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k6_domain_1(X1,X0))
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | r2_hidden(X2,X1) ) ),
    inference(resolution,[],[f67,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:57:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (18382)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.50  % (18384)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.50  % (18390)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.51  % (18377)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (18406)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.51  % (18389)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (18385)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (18405)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (18397)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (18379)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (18380)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (18381)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.25/0.53  % (18398)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.25/0.53  % (18392)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.25/0.53  % (18399)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.25/0.53  % (18402)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.25/0.54  % (18406)Refutation found. Thanks to Tanya!
% 1.25/0.54  % SZS status Theorem for theBenchmark
% 1.25/0.54  % (18385)Refutation not found, incomplete strategy% (18385)------------------------------
% 1.25/0.54  % (18385)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.54  % (18385)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.54  
% 1.25/0.54  % (18385)Memory used [KB]: 10874
% 1.25/0.54  % (18385)Time elapsed: 0.119 s
% 1.25/0.54  % (18385)------------------------------
% 1.25/0.54  % (18385)------------------------------
% 1.25/0.54  % (18388)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.25/0.54  % (18391)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.25/0.54  % (18378)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.25/0.54  % (18379)Refutation not found, incomplete strategy% (18379)------------------------------
% 1.25/0.54  % (18379)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.54  % (18379)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.54  
% 1.25/0.54  % (18379)Memory used [KB]: 10874
% 1.25/0.54  % (18379)Time elapsed: 0.127 s
% 1.25/0.54  % (18379)------------------------------
% 1.25/0.54  % (18379)------------------------------
% 1.25/0.54  % (18403)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.25/0.54  % (18404)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.25/0.54  % SZS output start Proof for theBenchmark
% 1.25/0.54  fof(f338,plain,(
% 1.25/0.54    $false),
% 1.25/0.54    inference(subsumption_resolution,[],[f337,f74])).
% 1.25/0.54  fof(f74,plain,(
% 1.25/0.54    m1_subset_1(sK4,sK3)),
% 1.25/0.54    inference(resolution,[],[f64,f51])).
% 1.25/0.54  fof(f51,plain,(
% 1.25/0.54    r2_hidden(sK4,sK3)),
% 1.25/0.54    inference(cnf_transformation,[],[f30])).
% 1.25/0.54  fof(f30,plain,(
% 1.25/0.54    ((k6_domain_1(u1_struct_0(sK2),sK4) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) & r2_hidden(sK4,sK3) & m1_subset_1(sK4,u1_struct_0(sK2))) & v2_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 1.25/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f13,f29,f28,f27])).
% 1.25/0.54  fof(f27,plain,(
% 1.25/0.54    ? [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(sK2),X2) != k9_subset_1(u1_struct_0(sK2),X1,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK2))) & v2_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 1.25/0.54    introduced(choice_axiom,[])).
% 1.25/0.54  fof(f28,plain,(
% 1.25/0.54    ? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(sK2),X2) != k9_subset_1(u1_struct_0(sK2),X1,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK2))) & v2_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) => (? [X2] : (k6_domain_1(u1_struct_0(sK2),X2) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X2))) & r2_hidden(X2,sK3) & m1_subset_1(X2,u1_struct_0(sK2))) & v2_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))))),
% 1.25/0.54    introduced(choice_axiom,[])).
% 1.25/0.54  fof(f29,plain,(
% 1.25/0.54    ? [X2] : (k6_domain_1(u1_struct_0(sK2),X2) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X2))) & r2_hidden(X2,sK3) & m1_subset_1(X2,u1_struct_0(sK2))) => (k6_domain_1(u1_struct_0(sK2),sK4) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) & r2_hidden(sK4,sK3) & m1_subset_1(sK4,u1_struct_0(sK2)))),
% 1.25/0.54    introduced(choice_axiom,[])).
% 1.25/0.54  fof(f13,plain,(
% 1.25/0.54    ? [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.25/0.54    inference(flattening,[],[f12])).
% 1.25/0.54  fof(f12,plain,(
% 1.25/0.54    ? [X0] : (? [X1] : ((? [X2] : ((k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.25/0.54    inference(ennf_transformation,[],[f11])).
% 1.25/0.54  fof(f11,negated_conjecture,(
% 1.25/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))))),
% 1.25/0.54    inference(negated_conjecture,[],[f10])).
% 1.25/0.54  fof(f10,conjecture,(
% 1.25/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))))),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_tex_2)).
% 1.25/0.54  fof(f64,plain,(
% 1.25/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f17])).
% 1.25/0.54  fof(f17,plain,(
% 1.25/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.25/0.54    inference(ennf_transformation,[],[f6])).
% 1.25/0.54  fof(f6,axiom,(
% 1.25/0.54    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 1.25/0.54  fof(f337,plain,(
% 1.25/0.54    ~m1_subset_1(sK4,sK3)),
% 1.25/0.54    inference(subsumption_resolution,[],[f336,f72])).
% 1.25/0.54  fof(f72,plain,(
% 1.25/0.54    ~v1_xboole_0(sK3)),
% 1.25/0.54    inference(resolution,[],[f62,f51])).
% 1.25/0.54  fof(f62,plain,(
% 1.25/0.54    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f40])).
% 1.25/0.54  fof(f40,plain,(
% 1.25/0.54    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK6(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.25/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f38,f39])).
% 1.25/0.54  fof(f39,plain,(
% 1.25/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK6(X0),X0))),
% 1.25/0.54    introduced(choice_axiom,[])).
% 1.25/0.54  fof(f38,plain,(
% 1.25/0.54    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.25/0.54    inference(rectify,[],[f37])).
% 1.25/0.54  fof(f37,plain,(
% 1.25/0.54    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.25/0.54    inference(nnf_transformation,[],[f1])).
% 1.25/0.54  fof(f1,axiom,(
% 1.25/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.25/0.54  fof(f336,plain,(
% 1.25/0.54    v1_xboole_0(sK3) | ~m1_subset_1(sK4,sK3)),
% 1.25/0.54    inference(duplicate_literal_removal,[],[f328])).
% 1.25/0.54  fof(f328,plain,(
% 1.25/0.54    v1_xboole_0(sK3) | ~m1_subset_1(sK4,sK3) | ~m1_subset_1(sK4,sK3) | v1_xboole_0(sK3)),
% 1.25/0.54    inference(resolution,[],[f304,f181])).
% 1.25/0.54  fof(f181,plain,(
% 1.25/0.54    ( ! [X10] : (~r1_tarski(k6_domain_1(X10,sK4),sK3) | ~m1_subset_1(sK4,X10) | v1_xboole_0(X10)) )),
% 1.25/0.54    inference(subsumption_resolution,[],[f180,f77])).
% 1.25/0.54  fof(f77,plain,(
% 1.25/0.54    ~v1_xboole_0(u1_struct_0(sK2))),
% 1.25/0.54    inference(subsumption_resolution,[],[f76,f72])).
% 1.25/0.54  fof(f76,plain,(
% 1.25/0.54    v1_xboole_0(sK3) | ~v1_xboole_0(u1_struct_0(sK2))),
% 1.25/0.54    inference(resolution,[],[f54,f48])).
% 1.25/0.54  fof(f48,plain,(
% 1.25/0.54    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.25/0.54    inference(cnf_transformation,[],[f30])).
% 1.25/0.54  fof(f54,plain,(
% 1.25/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f14])).
% 1.25/0.54  fof(f14,plain,(
% 1.25/0.54    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.25/0.54    inference(ennf_transformation,[],[f5])).
% 1.25/0.54  fof(f5,axiom,(
% 1.25/0.54    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 1.25/0.54  fof(f180,plain,(
% 1.25/0.54    ( ! [X10] : (~r1_tarski(k6_domain_1(X10,sK4),sK3) | ~m1_subset_1(sK4,X10) | v1_xboole_0(X10) | v1_xboole_0(u1_struct_0(sK2))) )),
% 1.25/0.54    inference(subsumption_resolution,[],[f159,f50])).
% 1.25/0.54  fof(f50,plain,(
% 1.25/0.54    m1_subset_1(sK4,u1_struct_0(sK2))),
% 1.25/0.54    inference(cnf_transformation,[],[f30])).
% 1.25/0.54  fof(f159,plain,(
% 1.25/0.54    ( ! [X10] : (~r1_tarski(k6_domain_1(X10,sK4),sK3) | ~m1_subset_1(sK4,X10) | v1_xboole_0(X10) | ~m1_subset_1(sK4,u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK2))) )),
% 1.25/0.54    inference(superposition,[],[f141,f97])).
% 1.25/0.54  fof(f97,plain,(
% 1.25/0.54    ( ! [X2,X0,X1] : (k6_domain_1(X1,X0) = k6_domain_1(X2,X0) | ~m1_subset_1(X0,X2) | v1_xboole_0(X2) | ~m1_subset_1(X0,X1) | v1_xboole_0(X1)) )),
% 1.25/0.54    inference(superposition,[],[f71,f71])).
% 1.25/0.54  fof(f71,plain,(
% 1.25/0.54    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k2_tarski(X1,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.25/0.54    inference(definition_unfolding,[],[f66,f53])).
% 1.25/0.54  fof(f53,plain,(
% 1.25/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f3])).
% 1.25/0.54  fof(f3,axiom,(
% 1.25/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.25/0.54  fof(f66,plain,(
% 1.25/0.54    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f20])).
% 1.25/0.54  fof(f20,plain,(
% 1.25/0.54    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.25/0.54    inference(flattening,[],[f19])).
% 1.25/0.54  fof(f19,plain,(
% 1.25/0.54    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.25/0.54    inference(ennf_transformation,[],[f8])).
% 1.25/0.54  fof(f8,axiom,(
% 1.25/0.54    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.25/0.54  fof(f141,plain,(
% 1.25/0.54    ~r1_tarski(k6_domain_1(u1_struct_0(sK2),sK4),sK3)),
% 1.25/0.54    inference(subsumption_resolution,[],[f140,f77])).
% 1.25/0.54  fof(f140,plain,(
% 1.25/0.54    ~r1_tarski(k6_domain_1(u1_struct_0(sK2),sK4),sK3) | v1_xboole_0(u1_struct_0(sK2))),
% 1.25/0.54    inference(subsumption_resolution,[],[f138,f50])).
% 1.25/0.54  fof(f138,plain,(
% 1.25/0.54    ~r1_tarski(k6_domain_1(u1_struct_0(sK2),sK4),sK3) | ~m1_subset_1(sK4,u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK2))),
% 1.25/0.54    inference(resolution,[],[f117,f67])).
% 1.25/0.54  fof(f67,plain,(
% 1.25/0.54    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f22])).
% 1.25/0.54  fof(f22,plain,(
% 1.25/0.54    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.25/0.54    inference(flattening,[],[f21])).
% 1.25/0.54  fof(f21,plain,(
% 1.25/0.54    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.25/0.54    inference(ennf_transformation,[],[f7])).
% 1.25/0.54  fof(f7,axiom,(
% 1.25/0.54    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 1.25/0.54  fof(f117,plain,(
% 1.25/0.54    ~m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK4),k1_zfmisc_1(u1_struct_0(sK2))) | ~r1_tarski(k6_domain_1(u1_struct_0(sK2),sK4),sK3)),
% 1.25/0.54    inference(subsumption_resolution,[],[f116,f110])).
% 1.25/0.54  fof(f110,plain,(
% 1.25/0.54    sP0(sK2,sK3)),
% 1.25/0.54    inference(subsumption_resolution,[],[f109,f49])).
% 1.25/0.54  fof(f49,plain,(
% 1.25/0.54    v2_tex_2(sK3,sK2)),
% 1.25/0.54    inference(cnf_transformation,[],[f30])).
% 1.25/0.54  fof(f109,plain,(
% 1.25/0.54    ~v2_tex_2(sK3,sK2) | sP0(sK2,sK3)),
% 1.25/0.54    inference(resolution,[],[f107,f55])).
% 1.25/0.54  fof(f55,plain,(
% 1.25/0.54    ( ! [X0,X1] : (~sP1(X0,X1) | ~v2_tex_2(X0,X1) | sP0(X1,X0)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f32])).
% 1.25/0.54  fof(f32,plain,(
% 1.25/0.54    ! [X0,X1] : (((v2_tex_2(X0,X1) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v2_tex_2(X0,X1))) | ~sP1(X0,X1))),
% 1.25/0.54    inference(rectify,[],[f31])).
% 1.25/0.54  fof(f31,plain,(
% 1.25/0.54    ! [X1,X0] : (((v2_tex_2(X1,X0) | ~sP0(X0,X1)) & (sP0(X0,X1) | ~v2_tex_2(X1,X0))) | ~sP1(X1,X0))),
% 1.25/0.54    inference(nnf_transformation,[],[f25])).
% 1.25/0.54  fof(f25,plain,(
% 1.25/0.54    ! [X1,X0] : ((v2_tex_2(X1,X0) <=> sP0(X0,X1)) | ~sP1(X1,X0))),
% 1.25/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.25/0.54  fof(f107,plain,(
% 1.25/0.54    sP1(sK3,sK2)),
% 1.25/0.54    inference(subsumption_resolution,[],[f106,f45])).
% 1.25/0.54  fof(f45,plain,(
% 1.25/0.54    ~v2_struct_0(sK2)),
% 1.25/0.54    inference(cnf_transformation,[],[f30])).
% 1.25/0.54  fof(f106,plain,(
% 1.25/0.54    sP1(sK3,sK2) | v2_struct_0(sK2)),
% 1.25/0.54    inference(subsumption_resolution,[],[f105,f46])).
% 1.25/0.54  fof(f46,plain,(
% 1.25/0.54    v2_pre_topc(sK2)),
% 1.25/0.54    inference(cnf_transformation,[],[f30])).
% 1.25/0.54  fof(f105,plain,(
% 1.25/0.54    sP1(sK3,sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.25/0.54    inference(subsumption_resolution,[],[f101,f47])).
% 1.25/0.54  fof(f47,plain,(
% 1.25/0.54    l1_pre_topc(sK2)),
% 1.25/0.54    inference(cnf_transformation,[],[f30])).
% 1.25/0.54  fof(f101,plain,(
% 1.25/0.54    sP1(sK3,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.25/0.54    inference(resolution,[],[f61,f48])).
% 1.25/0.54  % (18394)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.25/0.54  fof(f61,plain,(
% 1.25/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP1(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f26])).
% 1.25/0.54  fof(f26,plain,(
% 1.25/0.54    ! [X0] : (! [X1] : (sP1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.25/0.54    inference(definition_folding,[],[f16,f25,f24])).
% 1.25/0.54  fof(f24,plain,(
% 1.25/0.54    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.25/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.25/0.54  fof(f16,plain,(
% 1.25/0.54    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.25/0.54    inference(flattening,[],[f15])).
% 1.25/0.54  fof(f15,plain,(
% 1.25/0.54    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.25/0.54    inference(ennf_transformation,[],[f9])).
% 1.25/0.54  fof(f9,axiom,(
% 1.25/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2)))))),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tex_2)).
% 1.25/0.54  fof(f116,plain,(
% 1.25/0.54    ~r1_tarski(k6_domain_1(u1_struct_0(sK2),sK4),sK3) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK4),k1_zfmisc_1(u1_struct_0(sK2))) | ~sP0(sK2,sK3)),
% 1.25/0.54    inference(trivial_inequality_removal,[],[f114])).
% 1.25/0.54  fof(f114,plain,(
% 1.25/0.54    k6_domain_1(u1_struct_0(sK2),sK4) != k6_domain_1(u1_struct_0(sK2),sK4) | ~r1_tarski(k6_domain_1(u1_struct_0(sK2),sK4),sK3) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK4),k1_zfmisc_1(u1_struct_0(sK2))) | ~sP0(sK2,sK3)),
% 1.25/0.54    inference(superposition,[],[f52,f57])).
% 1.25/0.54  fof(f57,plain,(
% 1.25/0.54    ( ! [X0,X3,X1] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~sP0(X0,X1)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f36])).
% 1.25/0.54  fof(f36,plain,(
% 1.25/0.54    ! [X0,X1] : ((sP0(X0,X1) | (sK5(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK5(X0,X1))) & r1_tarski(sK5(X0,X1),X1) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0,X1)))),
% 1.25/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f35])).
% 1.25/0.54  fof(f35,plain,(
% 1.25/0.54    ! [X1,X0] : (? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK5(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK5(X0,X1))) & r1_tarski(sK5(X0,X1),X1) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.25/0.54    introduced(choice_axiom,[])).
% 1.25/0.54  fof(f34,plain,(
% 1.25/0.54    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0,X1)))),
% 1.25/0.54    inference(rectify,[],[f33])).
% 1.25/0.54  fof(f33,plain,(
% 1.25/0.54    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0,X1)))),
% 1.25/0.54    inference(nnf_transformation,[],[f24])).
% 1.25/0.54  fof(f52,plain,(
% 1.25/0.54    k6_domain_1(u1_struct_0(sK2),sK4) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)))),
% 1.25/0.54    inference(cnf_transformation,[],[f30])).
% 1.25/0.54  fof(f304,plain,(
% 1.25/0.54    ( ! [X0,X1] : (r1_tarski(k6_domain_1(X1,X0),X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.25/0.54    inference(duplicate_literal_removal,[],[f287])).
% 1.25/0.54  fof(f287,plain,(
% 1.25/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r1_tarski(k6_domain_1(X1,X0),X1) | r1_tarski(k6_domain_1(X1,X0),X1)) )),
% 1.25/0.54    inference(resolution,[],[f133,f70])).
% 1.25/0.54  fof(f70,plain,(
% 1.25/0.54    ( ! [X0,X1] : (~r2_hidden(sK7(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f44])).
% 1.25/0.54  fof(f44,plain,(
% 1.25/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.25/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f42,f43])).
% 1.25/0.54  fof(f43,plain,(
% 1.25/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 1.25/0.54    introduced(choice_axiom,[])).
% 1.25/0.54  fof(f42,plain,(
% 1.25/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.25/0.54    inference(rectify,[],[f41])).
% 1.25/0.54  fof(f41,plain,(
% 1.25/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.25/0.54    inference(nnf_transformation,[],[f23])).
% 1.25/0.54  fof(f23,plain,(
% 1.25/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.25/0.54    inference(ennf_transformation,[],[f2])).
% 1.25/0.54  fof(f2,axiom,(
% 1.25/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.25/0.54  fof(f133,plain,(
% 1.25/0.54    ( ! [X4,X2,X3] : (r2_hidden(sK7(k6_domain_1(X2,X3),X4),X2) | ~m1_subset_1(X3,X2) | v1_xboole_0(X2) | r1_tarski(k6_domain_1(X2,X3),X4)) )),
% 1.25/0.54    inference(resolution,[],[f95,f69])).
% 1.25/0.54  fof(f69,plain,(
% 1.25/0.54    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f44])).
% 1.25/0.54  fof(f95,plain,(
% 1.25/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,k6_domain_1(X1,X0)) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1) | r2_hidden(X2,X1)) )),
% 1.25/0.54    inference(resolution,[],[f67,f65])).
% 1.25/0.54  fof(f65,plain,(
% 1.25/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f18])).
% 1.25/0.54  fof(f18,plain,(
% 1.25/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.25/0.54    inference(ennf_transformation,[],[f4])).
% 1.25/0.54  fof(f4,axiom,(
% 1.25/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 1.25/0.54  % SZS output end Proof for theBenchmark
% 1.25/0.54  % (18406)------------------------------
% 1.25/0.54  % (18406)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.54  % (18406)Termination reason: Refutation
% 1.25/0.54  
% 1.25/0.54  % (18406)Memory used [KB]: 1918
% 1.25/0.54  % (18406)Time elapsed: 0.123 s
% 1.25/0.54  % (18406)------------------------------
% 1.25/0.54  % (18406)------------------------------
% 1.25/0.55  % (18376)Success in time 0.179 s
%------------------------------------------------------------------------------
