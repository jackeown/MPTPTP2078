%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:41 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 178 expanded)
%              Number of leaves         :   14 (  57 expanded)
%              Depth                    :   18
%              Number of atoms          :  252 ( 697 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f100,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f78,f90,f95,f99])).

fof(f99,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f98])).

fof(f98,plain,
    ( $false
    | spl2_3 ),
    inference(subsumption_resolution,[],[f97,f27])).

fof(f27,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    & v3_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
            & v3_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),X1),sK0)
          & v3_tops_1(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),X1),sK0)
        & v3_tops_1(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
      & v3_tops_1(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          & v3_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          & v3_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tops_1(X1,X0)
             => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_tops_1)).

fof(f97,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_3 ),
    inference(subsumption_resolution,[],[f96,f28])).

fof(f28,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f96,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_3 ),
    inference(resolution,[],[f85,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f85,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl2_3
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f95,plain,(
    spl2_4 ),
    inference(avatar_contradiction_clause,[],[f94])).

fof(f94,plain,
    ( $false
    | spl2_4 ),
    inference(subsumption_resolution,[],[f93,f27])).

fof(f93,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_4 ),
    inference(subsumption_resolution,[],[f91,f28])).

fof(f91,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_4 ),
    inference(resolution,[],[f89,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

% (13222)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=on:gs=on:gsem=on:irw=on:nm=0:nwc=2.5:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_2 on theBenchmark
% (13220)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f89,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl2_4
  <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f90,plain,
    ( ~ spl2_3
    | ~ spl2_4
    | spl2_2 ),
    inference(avatar_split_clause,[],[f81,f70,f87,f83])).

fof(f70,plain,
    ( spl2_2
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f81,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_2 ),
    inference(subsumption_resolution,[],[f79,f28])).

fof(f79,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_2 ),
    inference(resolution,[],[f72,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

fof(f72,plain,
    ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f78,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f77])).

fof(f77,plain,
    ( $false
    | spl2_1 ),
    inference(subsumption_resolution,[],[f76,f28])).

fof(f76,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_1 ),
    inference(resolution,[],[f68,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f68,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl2_1
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f73,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f60,f70,f66])).

fof(f60,plain,
    ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f58,f30])).

fof(f30,plain,(
    ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f58,plain,(
    ! [X0] :
      ( v1_tops_1(X0,sK0)
      | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f55,f28])).

fof(f55,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),X0)
      | v1_tops_1(X0,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f54,f29])).

fof(f29,plain,(
    v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v3_tops_1(X1,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1)),X0)
      | v1_tops_1(X0,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f53,f27])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1)),X0)
      | ~ v3_tops_1(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(duplicate_literal_removal,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1)),X0)
      | ~ v3_tops_1(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f51,f40])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_pre_topc(sK0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_tops_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1)),X0)
      | ~ v3_tops_1(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f50,f27])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_tops_1(X0,sK0)
      | ~ m1_subset_1(k2_pre_topc(sK0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1)),X0)
      | ~ v3_tops_1(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f49,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v2_tops_1(k2_pre_topc(X0,X1),X0)
      | ~ v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tops_1(X1,X0)
              | ~ v2_tops_1(k2_pre_topc(X0,X1),X0) )
            & ( v2_tops_1(k2_pre_topc(X0,X1),X0)
              | ~ v3_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tops_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v2_tops_1(X0,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_tops_1(X1,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),X0),X1) ) ),
    inference(subsumption_resolution,[],[f48,f37])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),X0),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_tops_1(X1,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tops_1(X0,sK0) ) ),
    inference(resolution,[],[f47,f41])).

fof(f41,plain,(
    ! [X0] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tops_1(X0,sK0) ) ),
    inference(resolution,[],[f32,f27])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_1(X0,sK0)
      | ~ r1_tarski(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_tops_1(X1,sK0) ) ),
    inference(resolution,[],[f36,f27])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,X2)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tops_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_1(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ v1_tops_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_1(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ v1_tops_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v1_tops_1(X1,X0) )
               => v1_tops_1(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_tops_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n010.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 11:25:29 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.48  % (13204)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.23/0.48  % (13204)Refutation found. Thanks to Tanya!
% 0.23/0.48  % SZS status Theorem for theBenchmark
% 0.23/0.48  % SZS output start Proof for theBenchmark
% 0.23/0.48  fof(f100,plain,(
% 0.23/0.48    $false),
% 0.23/0.48    inference(avatar_sat_refutation,[],[f73,f78,f90,f95,f99])).
% 0.23/0.48  fof(f99,plain,(
% 0.23/0.48    spl2_3),
% 0.23/0.48    inference(avatar_contradiction_clause,[],[f98])).
% 0.23/0.48  fof(f98,plain,(
% 0.23/0.48    $false | spl2_3),
% 0.23/0.48    inference(subsumption_resolution,[],[f97,f27])).
% 0.23/0.48  fof(f27,plain,(
% 0.23/0.48    l1_pre_topc(sK0)),
% 0.23/0.48    inference(cnf_transformation,[],[f23])).
% 0.23/0.48  fof(f23,plain,(
% 0.23/0.48    (~v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) & v3_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.23/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f22,f21])).
% 0.23/0.48  fof(f21,plain,(
% 0.23/0.48    ? [X0] : (? [X1] : (~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) & v3_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~v1_tops_1(k3_subset_1(u1_struct_0(sK0),X1),sK0) & v3_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.23/0.48    introduced(choice_axiom,[])).
% 0.23/0.48  fof(f22,plain,(
% 0.23/0.48    ? [X1] : (~v1_tops_1(k3_subset_1(u1_struct_0(sK0),X1),sK0) & v3_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) & v3_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.23/0.48    introduced(choice_axiom,[])).
% 0.23/0.48  fof(f11,plain,(
% 0.23/0.48    ? [X0] : (? [X1] : (~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) & v3_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.23/0.48    inference(flattening,[],[f10])).
% 0.23/0.48  fof(f10,plain,(
% 0.23/0.48    ? [X0] : (? [X1] : ((~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) & v3_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.23/0.48    inference(ennf_transformation,[],[f9])).
% 0.23/0.48  fof(f9,negated_conjecture,(
% 0.23/0.48    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.23/0.48    inference(negated_conjecture,[],[f8])).
% 0.23/0.48  fof(f8,conjecture,(
% 0.23/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_tops_1)).
% 0.23/0.48  fof(f97,plain,(
% 0.23/0.48    ~l1_pre_topc(sK0) | spl2_3),
% 0.23/0.48    inference(subsumption_resolution,[],[f96,f28])).
% 0.23/0.48  fof(f28,plain,(
% 0.23/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.23/0.48    inference(cnf_transformation,[],[f23])).
% 0.23/0.48  fof(f96,plain,(
% 0.23/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_3),
% 0.23/0.48    inference(resolution,[],[f85,f40])).
% 0.23/0.48  fof(f40,plain,(
% 0.23/0.48    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.23/0.48    inference(cnf_transformation,[],[f20])).
% 0.23/0.48  fof(f20,plain,(
% 0.23/0.48    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.23/0.48    inference(flattening,[],[f19])).
% 0.23/0.48  fof(f19,plain,(
% 0.23/0.48    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.23/0.48    inference(ennf_transformation,[],[f3])).
% 0.23/0.48  fof(f3,axiom,(
% 0.23/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.23/0.48  fof(f85,plain,(
% 0.23/0.48    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_3),
% 0.23/0.48    inference(avatar_component_clause,[],[f83])).
% 0.23/0.48  fof(f83,plain,(
% 0.23/0.48    spl2_3 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.23/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.23/0.48  fof(f95,plain,(
% 0.23/0.48    spl2_4),
% 0.23/0.48    inference(avatar_contradiction_clause,[],[f94])).
% 0.23/0.48  fof(f94,plain,(
% 0.23/0.48    $false | spl2_4),
% 0.23/0.48    inference(subsumption_resolution,[],[f93,f27])).
% 0.23/0.48  fof(f93,plain,(
% 0.23/0.48    ~l1_pre_topc(sK0) | spl2_4),
% 0.23/0.48    inference(subsumption_resolution,[],[f91,f28])).
% 0.23/0.48  fof(f91,plain,(
% 0.23/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_4),
% 0.23/0.48    inference(resolution,[],[f89,f31])).
% 0.23/0.48  fof(f31,plain,(
% 0.23/0.48    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.23/0.48    inference(cnf_transformation,[],[f12])).
% 0.23/0.48  fof(f12,plain,(
% 0.23/0.48    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.48    inference(ennf_transformation,[],[f4])).
% 0.23/0.49  % (13222)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=on:gs=on:gsem=on:irw=on:nm=0:nwc=2.5:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.49  % (13220)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 0.23/0.49  fof(f4,axiom,(
% 0.23/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).
% 0.23/0.49  fof(f89,plain,(
% 0.23/0.49    ~r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | spl2_4),
% 0.23/0.49    inference(avatar_component_clause,[],[f87])).
% 0.23/0.49  fof(f87,plain,(
% 0.23/0.49    spl2_4 <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.23/0.49  fof(f90,plain,(
% 0.23/0.49    ~spl2_3 | ~spl2_4 | spl2_2),
% 0.23/0.49    inference(avatar_split_clause,[],[f81,f70,f87,f83])).
% 0.23/0.49  fof(f70,plain,(
% 0.23/0.49    spl2_2 <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.23/0.49  fof(f81,plain,(
% 0.23/0.49    ~r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_2),
% 0.23/0.49    inference(subsumption_resolution,[],[f79,f28])).
% 0.23/0.49  fof(f79,plain,(
% 0.23/0.49    ~r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl2_2),
% 0.23/0.49    inference(resolution,[],[f72,f38])).
% 0.23/0.49  fof(f38,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.23/0.49    inference(cnf_transformation,[],[f26])).
% 0.23/0.49  fof(f26,plain,(
% 0.23/0.49    ! [X0,X1] : (! [X2] : (((r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.23/0.49    inference(nnf_transformation,[],[f18])).
% 0.23/0.49  fof(f18,plain,(
% 0.23/0.49    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.23/0.49    inference(ennf_transformation,[],[f2])).
% 0.23/0.49  fof(f2,axiom,(
% 0.23/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).
% 0.23/0.49  fof(f72,plain,(
% 0.23/0.49    ~r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),sK1)) | spl2_2),
% 0.23/0.49    inference(avatar_component_clause,[],[f70])).
% 0.23/0.49  fof(f78,plain,(
% 0.23/0.49    spl2_1),
% 0.23/0.49    inference(avatar_contradiction_clause,[],[f77])).
% 0.23/0.49  fof(f77,plain,(
% 0.23/0.49    $false | spl2_1),
% 0.23/0.49    inference(subsumption_resolution,[],[f76,f28])).
% 0.23/0.49  fof(f76,plain,(
% 0.23/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl2_1),
% 0.23/0.49    inference(resolution,[],[f68,f37])).
% 0.23/0.49  fof(f37,plain,(
% 0.23/0.49    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.23/0.49    inference(cnf_transformation,[],[f17])).
% 0.23/0.49  fof(f17,plain,(
% 0.23/0.49    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.23/0.49    inference(ennf_transformation,[],[f1])).
% 0.23/0.49  fof(f1,axiom,(
% 0.23/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.23/0.49  fof(f68,plain,(
% 0.23/0.49    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_1),
% 0.23/0.49    inference(avatar_component_clause,[],[f66])).
% 0.23/0.49  fof(f66,plain,(
% 0.23/0.49    spl2_1 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.23/0.49  fof(f73,plain,(
% 0.23/0.49    ~spl2_1 | ~spl2_2),
% 0.23/0.49    inference(avatar_split_clause,[],[f60,f70,f66])).
% 0.23/0.49  fof(f60,plain,(
% 0.23/0.49    ~r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),sK1)) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.23/0.49    inference(resolution,[],[f58,f30])).
% 0.23/0.49  fof(f30,plain,(
% 0.23/0.49    ~v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 0.23/0.49    inference(cnf_transformation,[],[f23])).
% 0.23/0.49  fof(f58,plain,(
% 0.23/0.49    ( ! [X0] : (v1_tops_1(X0,sK0) | ~r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.23/0.49    inference(subsumption_resolution,[],[f55,f28])).
% 0.23/0.49  fof(f55,plain,(
% 0.23/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),X0) | v1_tops_1(X0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.23/0.49    inference(resolution,[],[f54,f29])).
% 0.23/0.49  fof(f29,plain,(
% 0.23/0.49    v3_tops_1(sK1,sK0)),
% 0.23/0.49    inference(cnf_transformation,[],[f23])).
% 0.23/0.49  fof(f54,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~v3_tops_1(X1,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1)),X0) | v1_tops_1(X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.23/0.49    inference(subsumption_resolution,[],[f53,f27])).
% 0.23/0.49  fof(f53,plain,(
% 0.23/0.49    ( ! [X0,X1] : (v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1)),X0) | ~v3_tops_1(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 0.23/0.49    inference(duplicate_literal_removal,[],[f52])).
% 0.23/0.49  fof(f52,plain,(
% 0.23/0.49    ( ! [X0,X1] : (v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1)),X0) | ~v3_tops_1(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 0.23/0.49    inference(resolution,[],[f51,f40])).
% 0.23/0.49  fof(f51,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~m1_subset_1(k2_pre_topc(sK0,X1),k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1)),X0) | ~v3_tops_1(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.23/0.49    inference(subsumption_resolution,[],[f50,f27])).
% 0.23/0.49  fof(f50,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(X0,sK0) | ~m1_subset_1(k2_pre_topc(sK0,X1),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1)),X0) | ~v3_tops_1(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 0.23/0.49    inference(resolution,[],[f49,f34])).
% 0.23/0.49  fof(f34,plain,(
% 0.23/0.49    ( ! [X0,X1] : (v2_tops_1(k2_pre_topc(X0,X1),X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f25])).
% 0.23/0.49  fof(f25,plain,(
% 0.23/0.49    ! [X0] : (! [X1] : (((v3_tops_1(X1,X0) | ~v2_tops_1(k2_pre_topc(X0,X1),X0)) & (v2_tops_1(k2_pre_topc(X0,X1),X0) | ~v3_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.49    inference(nnf_transformation,[],[f14])).
% 0.23/0.49  fof(f14,plain,(
% 0.23/0.49    ! [X0] : (! [X1] : ((v3_tops_1(X1,X0) <=> v2_tops_1(k2_pre_topc(X0,X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.49    inference(ennf_transformation,[],[f6])).
% 0.23/0.49  fof(f6,axiom,(
% 0.23/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) <=> v2_tops_1(k2_pre_topc(X0,X1),X0))))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tops_1)).
% 0.23/0.49  fof(f49,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~v2_tops_1(X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(X1,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k3_subset_1(u1_struct_0(sK0),X0),X1)) )),
% 0.23/0.49    inference(subsumption_resolution,[],[f48,f37])).
% 0.23/0.49  fof(f48,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~r1_tarski(k3_subset_1(u1_struct_0(sK0),X0),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(X1,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tops_1(X0,sK0)) )),
% 0.23/0.49    inference(resolution,[],[f47,f41])).
% 0.23/0.49  fof(f41,plain,(
% 0.23/0.49    ( ! [X0] : (v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tops_1(X0,sK0)) )),
% 0.23/0.49    inference(resolution,[],[f32,f27])).
% 0.23/0.49  fof(f32,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f24])).
% 0.23/0.49  fof(f24,plain,(
% 0.23/0.49    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.49    inference(nnf_transformation,[],[f13])).
% 0.23/0.49  fof(f13,plain,(
% 0.23/0.49    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.49    inference(ennf_transformation,[],[f5])).
% 0.23/0.49  fof(f5,axiom,(
% 0.23/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_1)).
% 0.23/0.49  fof(f47,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~v1_tops_1(X0,sK0) | ~r1_tarski(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(X1,sK0)) )),
% 0.23/0.49    inference(resolution,[],[f36,f27])).
% 0.23/0.49  fof(f36,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~r1_tarski(X1,X2) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_tops_1(X2,X0)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f16])).
% 0.23/0.49  fof(f16,plain,(
% 0.23/0.49    ! [X0] : (! [X1] : (! [X2] : (v1_tops_1(X2,X0) | ~r1_tarski(X1,X2) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.49    inference(flattening,[],[f15])).
% 0.23/0.49  fof(f15,plain,(
% 0.23/0.49    ! [X0] : (! [X1] : (! [X2] : ((v1_tops_1(X2,X0) | (~r1_tarski(X1,X2) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.49    inference(ennf_transformation,[],[f7])).
% 0.23/0.49  fof(f7,axiom,(
% 0.23/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v1_tops_1(X1,X0)) => v1_tops_1(X2,X0)))))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_tops_1)).
% 0.23/0.49  % SZS output end Proof for theBenchmark
% 0.23/0.49  % (13204)------------------------------
% 0.23/0.49  % (13204)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.49  % (13204)Termination reason: Refutation
% 0.23/0.49  
% 0.23/0.49  % (13204)Memory used [KB]: 5373
% 0.23/0.49  % (13204)Time elapsed: 0.065 s
% 0.23/0.49  % (13204)------------------------------
% 0.23/0.49  % (13204)------------------------------
% 0.23/0.49  % (13214)WARNING: option uwaf not known.
% 0.23/0.49  % (13203)Success in time 0.121 s
%------------------------------------------------------------------------------
