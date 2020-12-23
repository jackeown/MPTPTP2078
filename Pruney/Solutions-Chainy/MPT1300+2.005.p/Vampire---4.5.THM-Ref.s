%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:27 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 227 expanded)
%              Number of leaves         :   12 (  82 expanded)
%              Depth                    :   14
%              Number of atoms          :  221 (1218 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f94,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f90,f93])).

fof(f93,plain,(
    ~ spl6_1 ),
    inference(avatar_contradiction_clause,[],[f92])).

fof(f92,plain,
    ( $false
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f91,f55])).

fof(f55,plain,(
    ~ sP0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f53,f30])).

fof(f30,plain,(
    ~ v1_tops_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ v1_tops_2(sK3,sK2)
    & v1_tops_2(sK4,sK2)
    & r1_tarski(sK3,sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f7,f16,f15,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v1_tops_2(X1,X0)
                & v1_tops_2(X2,X0)
                & r1_tarski(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(X1,sK2)
              & v1_tops_2(X2,sK2)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v1_tops_2(X1,sK2)
            & v1_tops_2(X2,sK2)
            & r1_tarski(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
   => ( ? [X2] :
          ( ~ v1_tops_2(sK3,sK2)
          & v1_tops_2(X2,sK2)
          & r1_tarski(sK3,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
      & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X2] :
        ( ~ v1_tops_2(sK3,sK2)
        & v1_tops_2(X2,sK2)
        & r1_tarski(sK3,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
   => ( ~ v1_tops_2(sK3,sK2)
      & v1_tops_2(sK4,sK2)
      & r1_tarski(sK3,sK4)
      & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ) ),
    introduced(choice_axiom,[])).

% (27351)lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733 on theBenchmark
fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(X1,X0)
              & v1_tops_2(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(X1,X0)
              & v1_tops_2(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( ( v1_tops_2(X2,X0)
                    & r1_tarski(X1,X2) )
                 => v1_tops_2(X1,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( ( v1_tops_2(X2,X0)
                  & r1_tarski(X1,X2) )
               => v1_tops_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tops_2)).

fof(f53,plain,
    ( ~ sP0(sK2,sK3)
    | v1_tops_2(sK3,sK2) ),
    inference(resolution,[],[f52,f26])).

fof(f26,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f17])).

fof(f52,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
      | ~ sP0(sK2,X1)
      | v1_tops_2(X1,sK2) ) ),
    inference(resolution,[],[f41,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ sP0(X1,X0)
      | v1_tops_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( v1_tops_2(X0,X1)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v1_tops_2(X0,X1) ) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ( ( v1_tops_2(X1,X0)
          | ~ sP0(X0,X1) )
        & ( sP0(X0,X1)
          | ~ v1_tops_2(X1,X0) ) )
      | ~ sP1(X1,X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X1,X0] :
      ( ( v1_tops_2(X1,X0)
      <=> sP0(X0,X1) )
      | ~ sP1(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f41,plain,(
    ! [X0] :
      ( sP1(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ) ),
    inference(resolution,[],[f25,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | sP1(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f9,f12,f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( v3_pre_topc(X2,X0)
          | ~ r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_2)).

fof(f25,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f91,plain,
    ( sP0(sK2,sK3)
    | ~ spl6_1 ),
    inference(resolution,[],[f66,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(sK5(X0,X1),X0)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ~ v3_pre_topc(sK5(X0,X1),X0)
          & r2_hidden(sK5(X0,X1),X1)
          & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( v3_pre_topc(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK5(X0,X1),X0)
        & r2_hidden(sK5(X0,X1),X1)
        & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ~ v3_pre_topc(X2,X0)
            & r2_hidden(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( v3_pre_topc(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ~ v3_pre_topc(X2,X0)
            & r2_hidden(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( v3_pre_topc(X2,X0)
            | ~ r2_hidden(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f66,plain,
    ( v3_pre_topc(sK5(sK2,sK3),sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl6_1
  <=> v3_pre_topc(sK5(sK2,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f90,plain,(
    ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f89])).

fof(f89,plain,
    ( $false
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f88,f58])).

fof(f58,plain,(
    r2_hidden(sK5(sK2,sK3),sK3) ),
    inference(resolution,[],[f55,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f88,plain,
    ( ~ r2_hidden(sK5(sK2,sK3),sK3)
    | ~ spl6_2 ),
    inference(resolution,[],[f87,f44])).

fof(f44,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK4)
      | ~ r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f42,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f42,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK4)) ),
    inference(resolution,[],[f28,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f28,plain,(
    r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f17])).

fof(f87,plain,
    ( ~ r2_hidden(sK5(sK2,sK3),sK4)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f86,f27])).

fof(f27,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f17])).

fof(f86,plain,
    ( ~ r2_hidden(sK5(sK2,sK3),sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ spl6_2 ),
    inference(resolution,[],[f71,f29])).

fof(f29,plain,(
    v1_tops_2(sK4,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f71,plain,
    ( ! [X0] :
        ( ~ v1_tops_2(X0,sK2)
        | ~ r2_hidden(sK5(sK2,sK3),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
    | ~ spl6_2 ),
    inference(resolution,[],[f69,f51])).

fof(f51,plain,(
    ! [X0] :
      ( sP0(sK2,X0)
      | ~ v1_tops_2(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ) ),
    inference(resolution,[],[f41,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ v1_tops_2(X0,X1)
      | sP0(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f69,plain,
    ( ! [X0] :
        ( ~ sP0(sK2,X0)
        | ~ r2_hidden(sK5(sK2,sK3),X0) )
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl6_2
  <=> ! [X0] :
        ( ~ r2_hidden(sK5(sK2,sK3),X0)
        | ~ sP0(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f70,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f59,f68,f64])).

fof(f59,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5(sK2,sK3),X0)
      | v3_pre_topc(sK5(sK2,sK3),sK2)
      | ~ sP0(sK2,X0) ) ),
    inference(resolution,[],[f57,f33])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X3,X1)
      | v3_pre_topc(X3,X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f57,plain,(
    m1_subset_1(sK5(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(resolution,[],[f55,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:10:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (27341)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.22/0.49  % (27334)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.22/0.49  % (27349)ott+11_5:1_afp=100000:afq=1.1:br=off:gs=on:nm=64:nwc=1:sos=all:urr=on:updr=off_287 on theBenchmark
% 0.22/0.49  % (27340)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % (27341)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f94,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f70,f90,f93])).
% 0.22/0.49  fof(f93,plain,(
% 0.22/0.49    ~spl6_1),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f92])).
% 0.22/0.49  fof(f92,plain,(
% 0.22/0.49    $false | ~spl6_1),
% 0.22/0.49    inference(subsumption_resolution,[],[f91,f55])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    ~sP0(sK2,sK3)),
% 0.22/0.49    inference(subsumption_resolution,[],[f53,f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ~v1_tops_2(sK3,sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ((~v1_tops_2(sK3,sK2) & v1_tops_2(sK4,sK2) & r1_tarski(sK3,sK4) & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & l1_pre_topc(sK2)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f7,f16,f15,f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_2(X1,X0) & v1_tops_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tops_2(X1,sK2) & v1_tops_2(X2,sK2) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & l1_pre_topc(sK2))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ? [X1] : (? [X2] : (~v1_tops_2(X1,sK2) & v1_tops_2(X2,sK2) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) => (? [X2] : (~v1_tops_2(sK3,sK2) & v1_tops_2(X2,sK2) & r1_tarski(sK3,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ? [X2] : (~v1_tops_2(sK3,sK2) & v1_tops_2(X2,sK2) & r1_tarski(sK3,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) => (~v1_tops_2(sK3,sK2) & v1_tops_2(sK4,sK2) & r1_tarski(sK3,sK4) & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  % (27351)lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733 on theBenchmark
% 0.22/0.49  fof(f7,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_2(X1,X0) & v1_tops_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.22/0.49    inference(flattening,[],[f6])).
% 0.22/0.49  fof(f6,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : ((~v1_tops_2(X1,X0) & (v1_tops_2(X2,X0) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,negated_conjecture,(
% 0.22/0.49    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_tops_2(X2,X0) & r1_tarski(X1,X2)) => v1_tops_2(X1,X0)))))),
% 0.22/0.49    inference(negated_conjecture,[],[f4])).
% 0.22/0.49  fof(f4,conjecture,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_tops_2(X2,X0) & r1_tarski(X1,X2)) => v1_tops_2(X1,X0)))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tops_2)).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    ~sP0(sK2,sK3) | v1_tops_2(sK3,sK2)),
% 0.22/0.49    inference(resolution,[],[f52,f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) | ~sP0(sK2,X1) | v1_tops_2(X1,sK2)) )),
% 0.22/0.49    inference(resolution,[],[f41,f32])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~sP1(X0,X1) | ~sP0(X1,X0) | v1_tops_2(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0,X1] : (((v1_tops_2(X0,X1) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v1_tops_2(X0,X1))) | ~sP1(X0,X1))),
% 0.22/0.49    inference(rectify,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X1,X0] : (((v1_tops_2(X1,X0) | ~sP0(X0,X1)) & (sP0(X0,X1) | ~v1_tops_2(X1,X0))) | ~sP1(X1,X0))),
% 0.22/0.49    inference(nnf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ! [X1,X0] : ((v1_tops_2(X1,X0) <=> sP0(X0,X1)) | ~sP1(X1,X0))),
% 0.22/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ( ! [X0] : (sP1(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) )),
% 0.22/0.49    inference(resolution,[],[f25,f37])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | sP1(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (sP1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(definition_folding,[],[f9,f12,f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.49  fof(f9,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(flattening,[],[f8])).
% 0.22/0.49  fof(f8,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,X1) => v3_pre_topc(X2,X0))))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_2)).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    l1_pre_topc(sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f91,plain,(
% 0.22/0.49    sP0(sK2,sK3) | ~spl6_1),
% 0.22/0.49    inference(resolution,[],[f66,f36])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v3_pre_topc(sK5(X0,X1),X0) | sP0(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0,X1] : ((sP0(X0,X1) | (~v3_pre_topc(sK5(X0,X1),X0) & r2_hidden(sK5(X0,X1),X1) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0,X1)))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f21,f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X1,X0] : (? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK5(X0,X1),X0) & r2_hidden(sK5(X0,X1),X1) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0,X1)))),
% 0.22/0.49    inference(rectify,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0,X1)))),
% 0.22/0.49    inference(nnf_transformation,[],[f11])).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    v3_pre_topc(sK5(sK2,sK3),sK2) | ~spl6_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f64])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    spl6_1 <=> v3_pre_topc(sK5(sK2,sK3),sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.49  fof(f90,plain,(
% 0.22/0.49    ~spl6_2),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f89])).
% 0.22/0.49  fof(f89,plain,(
% 0.22/0.49    $false | ~spl6_2),
% 0.22/0.49    inference(subsumption_resolution,[],[f88,f58])).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    r2_hidden(sK5(sK2,sK3),sK3)),
% 0.22/0.49    inference(resolution,[],[f55,f35])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ( ! [X0,X1] : (sP0(X0,X1) | r2_hidden(sK5(X0,X1),X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f88,plain,(
% 0.22/0.49    ~r2_hidden(sK5(sK2,sK3),sK3) | ~spl6_2),
% 0.22/0.49    inference(resolution,[],[f87,f44])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    ( ! [X0] : (r2_hidden(X0,sK4) | ~r2_hidden(X0,sK3)) )),
% 0.22/0.49    inference(resolution,[],[f42,f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    m1_subset_1(sK3,k1_zfmisc_1(sK4))),
% 0.22/0.49    inference(resolution,[],[f28,f40])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.49    inference(nnf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    r1_tarski(sK3,sK4)),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f87,plain,(
% 0.22/0.49    ~r2_hidden(sK5(sK2,sK3),sK4) | ~spl6_2),
% 0.22/0.49    inference(subsumption_resolution,[],[f86,f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f86,plain,(
% 0.22/0.49    ~r2_hidden(sK5(sK2,sK3),sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) | ~spl6_2),
% 0.22/0.49    inference(resolution,[],[f71,f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    v1_tops_2(sK4,sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f71,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_tops_2(X0,sK2) | ~r2_hidden(sK5(sK2,sK3),X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) ) | ~spl6_2),
% 0.22/0.49    inference(resolution,[],[f69,f51])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    ( ! [X0] : (sP0(sK2,X0) | ~v1_tops_2(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) )),
% 0.22/0.49    inference(resolution,[],[f41,f31])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~sP1(X0,X1) | ~v1_tops_2(X0,X1) | sP0(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f19])).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    ( ! [X0] : (~sP0(sK2,X0) | ~r2_hidden(sK5(sK2,sK3),X0)) ) | ~spl6_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f68])).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    spl6_2 <=> ! [X0] : (~r2_hidden(sK5(sK2,sK3),X0) | ~sP0(sK2,X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    spl6_1 | spl6_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f59,f68,f64])).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(sK5(sK2,sK3),X0) | v3_pre_topc(sK5(sK2,sK3),sK2) | ~sP0(sK2,X0)) )),
% 0.22/0.49    inference(resolution,[],[f57,f33])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X3,X1) | v3_pre_topc(X3,X0) | ~sP0(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    m1_subset_1(sK5(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.22/0.49    inference(resolution,[],[f55,f34])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ( ! [X0,X1] : (sP0(X0,X1) | m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (27341)------------------------------
% 0.22/0.49  % (27341)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (27341)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (27341)Memory used [KB]: 9850
% 0.22/0.49  % (27341)Time elapsed: 0.061 s
% 0.22/0.49  % (27341)------------------------------
% 0.22/0.49  % (27341)------------------------------
% 0.22/0.50  % (27331)Success in time 0.124 s
%------------------------------------------------------------------------------
