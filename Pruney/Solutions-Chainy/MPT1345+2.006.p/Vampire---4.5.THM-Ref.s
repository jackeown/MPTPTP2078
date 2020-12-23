%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:39 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  147 (4060 expanded)
%              Number of leaves         :   16 (1509 expanded)
%              Depth                    :   23
%              Number of atoms          :  528 (28902 expanded)
%              Number of equality atoms :  122 (1095 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f867,plain,(
    $false ),
    inference(subsumption_resolution,[],[f866,f165])).

fof(f165,plain,(
    v5_pre_topc(sK4,sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f158,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
        | ~ v5_pre_topc(X2,X0,X1)
        | ~ v2_funct_1(X2)
        | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
        | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
      & ( ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
          & v5_pre_topc(X2,X0,X1)
          & v2_funct_1(X2)
          & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
          & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
        | ~ v5_pre_topc(X2,X0,X1)
        | ~ v2_funct_1(X2)
        | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
        | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
      & ( ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
          & v5_pre_topc(X2,X0,X1)
          & v2_funct_1(X2)
          & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
          & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( sP0(X0,X1,X2)
    <=> ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
        & v5_pre_topc(X2,X0,X1)
        & v2_funct_1(X2)
        & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
        & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f158,plain,(
    sP0(sK2,sK3,sK4) ),
    inference(unit_resulting_resolution,[],[f47,f115,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | ~ v3_tops_2(X0,X2,X1)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( v3_tops_2(X0,X2,X1)
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ v3_tops_2(X0,X2,X1) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ( ( v3_tops_2(X2,X0,X1)
          | ~ sP0(X0,X1,X2) )
        & ( sP0(X0,X1,X2)
          | ~ v3_tops_2(X2,X0,X1) ) )
      | ~ sP1(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ( v3_tops_2(X2,X0,X1)
      <=> sP0(X0,X1,X2) )
      | ~ sP1(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f115,plain,(
    sP1(sK4,sK3,sK2) ),
    inference(unit_resulting_resolution,[],[f41,f43,f44,f45,f46,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X2,X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f20,f31,f30])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <=> ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  & v5_pre_topc(X2,X0,X1)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <=> ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  & v5_pre_topc(X2,X0,X1)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v3_tops_2(X2,X0,X1)
              <=> ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  & v5_pre_topc(X2,X0,X1)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tops_2)).

% (16020)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% (16031)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% (16014)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% (16020)Refutation not found, incomplete strategy% (16020)------------------------------
% (16020)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (16016)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% (16020)Termination reason: Refutation not found, incomplete strategy

% (16020)Memory used [KB]: 10490
% (16020)Time elapsed: 0.111 s
% (16020)------------------------------
% (16020)------------------------------
% (16022)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% (16024)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
fof(f46,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ~ v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
    & v3_tops_2(sK4,sK2,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    & v1_funct_1(sK4)
    & l1_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f14,f35,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                & v3_tops_2(X2,X0,X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X2),X1,sK2)
              & v3_tops_2(X2,sK2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

% (16028)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
fof(f34,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X2),X1,sK2)
            & v3_tops_2(X2,sK2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ~ v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X2),sK3,sK2)
          & v3_tops_2(X2,sK2,sK3)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
          & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X2] :
        ( ~ v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X2),sK3,sK2)
        & v3_tops_2(X2,sK2,sK3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
        & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3))
        & v1_funct_1(X2) )
   => ( ~ v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
      & v3_tops_2(sK4,sK2,sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
      & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
              & v3_tops_2(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
              & v3_tops_2(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( v3_tops_2(X2,X0,X1)
                 => v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v3_tops_2(X2,X0,X1)
               => v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_tops_2)).

fof(f45,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f36])).

fof(f44,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f43,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f41,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f47,plain,(
    v3_tops_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f866,plain,(
    ~ v5_pre_topc(sK4,sK2,sK3) ),
    inference(forward_demodulation,[],[f863,f597])).

fof(f597,plain,(
    sK4 = k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)) ),
    inference(forward_demodulation,[],[f595,f188])).

fof(f188,plain,(
    sK4 = k2_funct_1(k2_funct_1(sK4)) ),
    inference(unit_resulting_resolution,[],[f119,f44,f164,f67])).

fof(f67,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

fof(f164,plain,(
    v2_funct_1(sK4) ),
    inference(unit_resulting_resolution,[],[f158,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f119,plain,(
    v1_relat_1(sK4) ),
    inference(unit_resulting_resolution,[],[f65,f46,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f65,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f595,plain,(
    k2_funct_1(k2_funct_1(sK4)) = k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)) ),
    inference(unit_resulting_resolution,[],[f190,f191,f551,f552,f594,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_tops_2(X0,X1,X2) = k2_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(f594,plain,(
    k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)) ),
    inference(forward_demodulation,[],[f549,f547])).

fof(f547,plain,(
    k2_funct_1(sK4) = k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4) ),
    inference(trivial_inequality_removal,[],[f544])).

fof(f544,plain,
    ( k2_struct_0(sK3) != k2_struct_0(sK3)
    | k2_funct_1(sK4) = k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4) ),
    inference(backward_demodulation,[],[f450,f527])).

fof(f527,plain,(
    k2_struct_0(sK3) = k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK3),sK4) ),
    inference(forward_demodulation,[],[f526,f93])).

fof(f93,plain,(
    u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(unit_resulting_resolution,[],[f72,f66])).

fof(f66,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f72,plain,(
    l1_struct_0(sK2) ),
    inference(unit_resulting_resolution,[],[f41,f71])).

fof(f71,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f526,plain,(
    k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4) ),
    inference(forward_demodulation,[],[f163,f109])).

fof(f109,plain,(
    u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(unit_resulting_resolution,[],[f78,f66])).

fof(f78,plain,(
    l1_struct_0(sK3) ),
    inference(unit_resulting_resolution,[],[f43,f71])).

fof(f163,plain,(
    k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) ),
    inference(unit_resulting_resolution,[],[f158,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f450,plain,
    ( k2_struct_0(sK3) != k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK3),sK4)
    | k2_funct_1(sK4) = k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4) ),
    inference(subsumption_resolution,[],[f449,f44])).

fof(f449,plain,
    ( k2_funct_1(sK4) = k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)
    | k2_struct_0(sK3) != k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK3),sK4)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f448,f392])).

fof(f392,plain,(
    v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3)) ),
    inference(backward_demodulation,[],[f306,f109])).

fof(f306,plain,(
    v1_funct_2(sK4,k2_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(backward_demodulation,[],[f45,f93])).

fof(f448,plain,
    ( k2_funct_1(sK4) = k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)
    | k2_struct_0(sK3) != k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK3),sK4)
    | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f444,f164])).

fof(f444,plain,
    ( k2_funct_1(sK4) = k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)
    | ~ v2_funct_1(sK4)
    | k2_struct_0(sK3) != k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK3),sK4)
    | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3))
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f391,f49])).

fof(f391,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) ),
    inference(backward_demodulation,[],[f307,f109])).

fof(f307,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(backward_demodulation,[],[f46,f93])).

fof(f549,plain,(
    k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)) ),
    inference(trivial_inequality_removal,[],[f542])).

fof(f542,plain,
    ( k2_struct_0(sK3) != k2_struct_0(sK3)
    | k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)) ),
    inference(backward_demodulation,[],[f541,f527])).

% (16025)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
fof(f541,plain,
    ( k2_struct_0(sK3) != k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK3),sK4)
    | k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)) ),
    inference(forward_demodulation,[],[f540,f109])).

fof(f540,plain,
    ( k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4))
    | k2_struct_0(sK3) != k2_relset_1(k2_struct_0(sK2),u1_struct_0(sK3),sK4) ),
    inference(forward_demodulation,[],[f349,f109])).

fof(f349,plain,
    ( k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),u1_struct_0(sK3),sK4))
    | k2_struct_0(sK3) != k2_relset_1(k2_struct_0(sK2),u1_struct_0(sK3),sK4) ),
    inference(forward_demodulation,[],[f314,f93])).

fof(f314,plain,
    ( k2_struct_0(sK3) != k2_relset_1(k2_struct_0(sK2),u1_struct_0(sK3),sK4)
    | k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) ),
    inference(backward_demodulation,[],[f284,f93])).

fof(f284,plain,
    ( k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) ),
    inference(subsumption_resolution,[],[f139,f164])).

fof(f139,plain,
    ( k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | ~ v2_funct_1(sK4)
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) ),
    inference(subsumption_resolution,[],[f138,f72])).

fof(f138,plain,
    ( k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | ~ v2_funct_1(sK4)
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | ~ l1_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f137,f42])).

fof(f42,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f137,plain,
    ( k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | ~ v2_funct_1(sK4)
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | v2_struct_0(sK3)
    | ~ l1_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f136,f78])).

fof(f136,plain,
    ( k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | ~ v2_funct_1(sK4)
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK3)
    | ~ l1_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f135,f44])).

fof(f135,plain,
    ( k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | ~ v2_funct_1(sK4)
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK3)
    | ~ l1_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f121,f45])).

fof(f121,plain,
    ( k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | ~ v2_funct_1(sK4)
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK3)
    | ~ l1_struct_0(sK2) ),
    inference(resolution,[],[f46,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
      | ~ v2_funct_1(X2)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( ( l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                  & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).

fof(f552,plain,(
    m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK2)))) ),
    inference(backward_demodulation,[],[f439,f547])).

fof(f439,plain,(
    m1_subset_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK2)))) ),
    inference(unit_resulting_resolution,[],[f44,f392,f391,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).

fof(f551,plain,(
    v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),k2_struct_0(sK2)) ),
    inference(backward_demodulation,[],[f438,f547])).

fof(f438,plain,(
    v1_funct_2(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4),k2_struct_0(sK3),k2_struct_0(sK2)) ),
    inference(unit_resulting_resolution,[],[f44,f392,f391,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f191,plain,(
    v2_funct_1(k2_funct_1(sK4)) ),
    inference(unit_resulting_resolution,[],[f119,f44,f164,f70])).

fof(f70,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f190,plain,(
    v1_funct_1(k2_funct_1(sK4)) ),
    inference(unit_resulting_resolution,[],[f119,f44,f164,f69])).

fof(f69,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f863,plain,(
    ~ v5_pre_topc(k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)),sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f191,f613,f556,f594,f593,f726])).

fof(f726,plain,(
    ! [X3] :
      ( k2_struct_0(sK3) != k1_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),X3)
      | sP0(sK3,sK2,X3)
      | ~ v5_pre_topc(X3,sK3,sK2)
      | ~ v2_funct_1(X3)
      | ~ v5_pre_topc(k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),X3),sK2,sK3)
      | k2_struct_0(sK2) != k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),X3) ) ),
    inference(superposition,[],[f326,f109])).

fof(f326,plain,(
    ! [X23,X22] :
      ( k2_struct_0(sK2) != k2_relset_1(u1_struct_0(X22),k2_struct_0(sK2),X23)
      | sP0(X22,sK2,X23)
      | ~ v5_pre_topc(X23,X22,sK2)
      | ~ v2_funct_1(X23)
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X22),k2_struct_0(sK2),X23),sK2,X22)
      | k2_struct_0(X22) != k1_relset_1(u1_struct_0(X22),k2_struct_0(sK2),X23) ) ),
    inference(superposition,[],[f60,f93])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v2_funct_1(X2)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f593,plain,(
    k2_struct_0(sK3) = k1_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)) ),
    inference(forward_demodulation,[],[f548,f547])).

fof(f548,plain,(
    k2_struct_0(sK3) = k1_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)) ),
    inference(trivial_inequality_removal,[],[f543])).

fof(f543,plain,
    ( k2_struct_0(sK3) != k2_struct_0(sK3)
    | k2_struct_0(sK3) = k1_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)) ),
    inference(backward_demodulation,[],[f535,f527])).

fof(f535,plain,
    ( k2_struct_0(sK3) != k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK3),sK4)
    | k2_struct_0(sK3) = k1_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)) ),
    inference(forward_demodulation,[],[f534,f109])).

fof(f534,plain,
    ( k2_struct_0(sK3) = k1_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4))
    | k2_struct_0(sK3) != k2_relset_1(k2_struct_0(sK2),u1_struct_0(sK3),sK4) ),
    inference(forward_demodulation,[],[f348,f109])).

fof(f348,plain,
    ( k2_struct_0(sK3) = k1_relset_1(u1_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),u1_struct_0(sK3),sK4))
    | k2_struct_0(sK3) != k2_relset_1(k2_struct_0(sK2),u1_struct_0(sK3),sK4) ),
    inference(forward_demodulation,[],[f313,f93])).

fof(f313,plain,
    ( k2_struct_0(sK3) != k2_relset_1(k2_struct_0(sK2),u1_struct_0(sK3),sK4)
    | k2_struct_0(sK3) = k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) ),
    inference(backward_demodulation,[],[f279,f93])).

fof(f279,plain,
    ( k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | k2_struct_0(sK3) = k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) ),
    inference(subsumption_resolution,[],[f134,f164])).

fof(f134,plain,
    ( k2_struct_0(sK3) = k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | ~ v2_funct_1(sK4)
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) ),
    inference(subsumption_resolution,[],[f133,f72])).

fof(f133,plain,
    ( k2_struct_0(sK3) = k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | ~ v2_funct_1(sK4)
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | ~ l1_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f132,f42])).

fof(f132,plain,
    ( k2_struct_0(sK3) = k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | ~ v2_funct_1(sK4)
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | v2_struct_0(sK3)
    | ~ l1_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f131,f78])).

fof(f131,plain,
    ( k2_struct_0(sK3) = k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | ~ v2_funct_1(sK4)
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK3)
    | ~ l1_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f130,f44])).

fof(f130,plain,
    ( k2_struct_0(sK3) = k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | ~ v2_funct_1(sK4)
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK3)
    | ~ l1_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f120,f45])).

fof(f120,plain,
    ( k2_struct_0(sK3) = k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | ~ v2_funct_1(sK4)
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK3)
    | ~ l1_struct_0(sK2) ),
    inference(resolution,[],[f46,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
      | ~ v2_funct_1(X2)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f556,plain,(
    ~ sP0(sK3,sK2,k2_funct_1(sK4)) ),
    inference(backward_demodulation,[],[f515,f547])).

fof(f515,plain,(
    ~ sP0(sK3,sK2,k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)) ),
    inference(unit_resulting_resolution,[],[f457,f498,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v3_tops_2(X0,X2,X1)
      | ~ sP0(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f498,plain,(
    sP1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4),sK2,sK3) ),
    inference(forward_demodulation,[],[f497,f93])).

fof(f497,plain,(
    sP1(k2_tops_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4),sK2,sK3) ),
    inference(forward_demodulation,[],[f217,f109])).

fof(f217,plain,(
    sP1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f43,f41,f116,f117,f118,f61])).

fof(f118,plain,(
    m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(unit_resulting_resolution,[],[f44,f45,f46,f52])).

fof(f117,plain,(
    v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(unit_resulting_resolution,[],[f44,f45,f46,f51])).

fof(f116,plain,(
    v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) ),
    inference(unit_resulting_resolution,[],[f44,f45,f46,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_tops_2(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f457,plain,(
    ~ v3_tops_2(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4),sK3,sK2) ),
    inference(forward_demodulation,[],[f308,f109])).

fof(f308,plain,(
    ~ v3_tops_2(k2_tops_2(k2_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) ),
    inference(backward_demodulation,[],[f48,f93])).

fof(f48,plain,(
    ~ v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f613,plain,(
    v5_pre_topc(k2_funct_1(sK4),sK3,sK2) ),
    inference(forward_demodulation,[],[f529,f547])).

fof(f529,plain,(
    v5_pre_topc(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4),sK3,sK2) ),
    inference(forward_demodulation,[],[f528,f93])).

fof(f528,plain,(
    v5_pre_topc(k2_tops_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4),sK3,sK2) ),
    inference(forward_demodulation,[],[f166,f109])).

fof(f166,plain,(
    v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) ),
    inference(unit_resulting_resolution,[],[f158,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:35:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (16027)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.20/0.47  % (16017)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (16013)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.49  % (16021)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.50  % (16013)Refutation not found, incomplete strategy% (16013)------------------------------
% 0.20/0.50  % (16013)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (16013)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (16013)Memory used [KB]: 10618
% 0.20/0.50  % (16013)Time elapsed: 0.077 s
% 0.20/0.50  % (16013)------------------------------
% 0.20/0.50  % (16013)------------------------------
% 0.20/0.50  % (16030)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.50  % (16011)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.50  % (16018)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.20/0.51  % (16012)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.51  % (16023)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.51  % (16019)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.52  % (16027)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f867,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(subsumption_resolution,[],[f866,f165])).
% 0.20/0.52  fof(f165,plain,(
% 0.20/0.52    v5_pre_topc(sK4,sK2,sK3)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f158,f58])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | ~sP0(X0,X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f40])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v5_pre_topc(X2,X0,X1) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) & ((v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~sP0(X0,X1,X2)))),
% 0.20/0.52    inference(flattening,[],[f39])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v5_pre_topc(X2,X0,X1) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) & ((v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~sP0(X0,X1,X2)))),
% 0.20/0.52    inference(nnf_transformation,[],[f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (sP0(X0,X1,X2) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)))),
% 0.20/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.52  fof(f158,plain,(
% 0.20/0.52    sP0(sK2,sK3,sK4)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f47,f115,f53])).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (sP0(X2,X1,X0) | ~v3_tops_2(X0,X2,X1) | ~sP1(X0,X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f38])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (((v3_tops_2(X0,X2,X1) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~v3_tops_2(X0,X2,X1))) | ~sP1(X0,X1,X2))),
% 0.20/0.52    inference(rectify,[],[f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ! [X2,X1,X0] : (((v3_tops_2(X2,X0,X1) | ~sP0(X0,X1,X2)) & (sP0(X0,X1,X2) | ~v3_tops_2(X2,X0,X1))) | ~sP1(X2,X1,X0))),
% 0.20/0.52    inference(nnf_transformation,[],[f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ! [X2,X1,X0] : ((v3_tops_2(X2,X0,X1) <=> sP0(X0,X1,X2)) | ~sP1(X2,X1,X0))),
% 0.20/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.52  fof(f115,plain,(
% 0.20/0.52    sP1(sK4,sK3,sK2)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f41,f43,f44,f45,f46,f61])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (sP1(X2,X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (sP1(X2,X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(definition_folding,[],[f20,f31,f30])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(flattening,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tops_2)).
% 0.20/0.52  % (16020)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.20/0.52  % (16031)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.52  % (16014)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.52  % (16020)Refutation not found, incomplete strategy% (16020)------------------------------
% 0.20/0.52  % (16020)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (16016)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.52  % (16020)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (16020)Memory used [KB]: 10490
% 0.20/0.52  % (16020)Time elapsed: 0.111 s
% 0.20/0.52  % (16020)------------------------------
% 0.20/0.52  % (16020)------------------------------
% 0.20/0.53  % (16022)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.53  % (16024)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 0.20/0.53    inference(cnf_transformation,[],[f36])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ((~v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) & v3_tops_2(sK4,sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4)) & l1_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2)),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f14,f35,f34,f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v3_tops_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X2),X1,sK2) & v3_tops_2(X2,sK2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  % (16028)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ? [X1] : (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X2),X1,sK2) & v3_tops_2(X2,sK2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X2),sK3,sK2) & v3_tops_2(X2,sK2,sK3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X2)) & l1_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X2),sK3,sK2) & v3_tops_2(X2,sK2,sK3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X2)) => (~v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) & v3_tops_2(sK4,sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f14,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v3_tops_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0))),
% 0.20/0.53    inference(flattening,[],[f13])).
% 0.20/0.53  fof(f13,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (? [X2] : ((~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v3_tops_2(X2,X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & ~v2_struct_0(X1))) & l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,negated_conjecture,(
% 0.20/0.53    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) => v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)))))),
% 0.20/0.53    inference(negated_conjecture,[],[f11])).
% 0.20/0.53  fof(f11,conjecture,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) => v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_tops_2)).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))),
% 0.20/0.53    inference(cnf_transformation,[],[f36])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    v1_funct_1(sK4)),
% 0.20/0.53    inference(cnf_transformation,[],[f36])).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    l1_pre_topc(sK3)),
% 0.20/0.53    inference(cnf_transformation,[],[f36])).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    l1_pre_topc(sK2)),
% 0.20/0.53    inference(cnf_transformation,[],[f36])).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    v3_tops_2(sK4,sK2,sK3)),
% 0.20/0.53    inference(cnf_transformation,[],[f36])).
% 0.20/0.53  fof(f866,plain,(
% 0.20/0.53    ~v5_pre_topc(sK4,sK2,sK3)),
% 0.20/0.53    inference(forward_demodulation,[],[f863,f597])).
% 0.20/0.53  fof(f597,plain,(
% 0.20/0.53    sK4 = k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4))),
% 0.20/0.53    inference(forward_demodulation,[],[f595,f188])).
% 0.20/0.53  fof(f188,plain,(
% 0.20/0.53    sK4 = k2_funct_1(k2_funct_1(sK4))),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f119,f44,f164,f67])).
% 0.20/0.53  fof(f67,plain,(
% 0.20/0.53    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(flattening,[],[f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).
% 0.20/0.53  fof(f164,plain,(
% 0.20/0.53    v2_funct_1(sK4)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f158,f57])).
% 0.20/0.53  fof(f57,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~sP0(X0,X1,X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f40])).
% 0.20/0.53  fof(f119,plain,(
% 0.20/0.53    v1_relat_1(sK4)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f65,f46,f64])).
% 0.20/0.53  fof(f64,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.53  fof(f65,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.53  fof(f595,plain,(
% 0.20/0.53    k2_funct_1(k2_funct_1(sK4)) = k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4))),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f190,f191,f551,f552,f594,f49])).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f16])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.53    inference(flattening,[],[f15])).
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.53    inference(ennf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_tops_2(X0,X1,X2) = k2_funct_1(X2)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).
% 0.20/0.53  fof(f594,plain,(
% 0.20/0.53    k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4))),
% 0.20/0.53    inference(forward_demodulation,[],[f549,f547])).
% 0.20/0.53  fof(f547,plain,(
% 0.20/0.53    k2_funct_1(sK4) = k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)),
% 0.20/0.53    inference(trivial_inequality_removal,[],[f544])).
% 0.20/0.53  fof(f544,plain,(
% 0.20/0.53    k2_struct_0(sK3) != k2_struct_0(sK3) | k2_funct_1(sK4) = k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)),
% 0.20/0.53    inference(backward_demodulation,[],[f450,f527])).
% 0.20/0.53  fof(f527,plain,(
% 0.20/0.53    k2_struct_0(sK3) = k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK3),sK4)),
% 0.20/0.53    inference(forward_demodulation,[],[f526,f93])).
% 0.20/0.53  fof(f93,plain,(
% 0.20/0.53    u1_struct_0(sK2) = k2_struct_0(sK2)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f72,f66])).
% 0.20/0.53  fof(f66,plain,(
% 0.20/0.53    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.53  fof(f72,plain,(
% 0.20/0.53    l1_struct_0(sK2)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f41,f71])).
% 0.20/0.53  fof(f71,plain,(
% 0.20/0.53    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.53  fof(f526,plain,(
% 0.20/0.53    k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4)),
% 0.20/0.53    inference(forward_demodulation,[],[f163,f109])).
% 0.20/0.53  fof(f109,plain,(
% 0.20/0.53    u1_struct_0(sK3) = k2_struct_0(sK3)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f78,f66])).
% 0.20/0.53  fof(f78,plain,(
% 0.20/0.53    l1_struct_0(sK3)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f43,f71])).
% 0.20/0.53  fof(f163,plain,(
% 0.20/0.53    k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f158,f56])).
% 0.20/0.53  fof(f56,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) | ~sP0(X0,X1,X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f40])).
% 0.20/0.53  fof(f450,plain,(
% 0.20/0.53    k2_struct_0(sK3) != k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK3),sK4) | k2_funct_1(sK4) = k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)),
% 0.20/0.53    inference(subsumption_resolution,[],[f449,f44])).
% 0.20/0.53  fof(f449,plain,(
% 0.20/0.53    k2_funct_1(sK4) = k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4) | k2_struct_0(sK3) != k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK3),sK4) | ~v1_funct_1(sK4)),
% 0.20/0.53    inference(subsumption_resolution,[],[f448,f392])).
% 0.20/0.53  fof(f392,plain,(
% 0.20/0.53    v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3))),
% 0.20/0.53    inference(backward_demodulation,[],[f306,f109])).
% 0.20/0.53  fof(f306,plain,(
% 0.20/0.53    v1_funct_2(sK4,k2_struct_0(sK2),u1_struct_0(sK3))),
% 0.20/0.53    inference(backward_demodulation,[],[f45,f93])).
% 0.20/0.53  fof(f448,plain,(
% 0.20/0.53    k2_funct_1(sK4) = k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4) | k2_struct_0(sK3) != k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK3),sK4) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 0.20/0.53    inference(subsumption_resolution,[],[f444,f164])).
% 0.20/0.53  fof(f444,plain,(
% 0.20/0.53    k2_funct_1(sK4) = k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4) | ~v2_funct_1(sK4) | k2_struct_0(sK3) != k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK3),sK4) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 0.20/0.53    inference(resolution,[],[f391,f49])).
% 0.20/0.53  fof(f391,plain,(
% 0.20/0.53    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3))))),
% 0.20/0.53    inference(backward_demodulation,[],[f307,f109])).
% 0.20/0.53  fof(f307,plain,(
% 0.20/0.53    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),u1_struct_0(sK3))))),
% 0.20/0.53    inference(backward_demodulation,[],[f46,f93])).
% 0.20/0.53  fof(f549,plain,(
% 0.20/0.53    k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4))),
% 0.20/0.53    inference(trivial_inequality_removal,[],[f542])).
% 0.20/0.53  fof(f542,plain,(
% 0.20/0.53    k2_struct_0(sK3) != k2_struct_0(sK3) | k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4))),
% 0.20/0.53    inference(backward_demodulation,[],[f541,f527])).
% 0.20/0.53  % (16025)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.20/0.53  fof(f541,plain,(
% 0.20/0.53    k2_struct_0(sK3) != k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK3),sK4) | k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4))),
% 0.20/0.53    inference(forward_demodulation,[],[f540,f109])).
% 0.20/0.53  fof(f540,plain,(
% 0.20/0.53    k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)) | k2_struct_0(sK3) != k2_relset_1(k2_struct_0(sK2),u1_struct_0(sK3),sK4)),
% 0.20/0.53    inference(forward_demodulation,[],[f349,f109])).
% 0.20/0.53  fof(f349,plain,(
% 0.20/0.53    k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),u1_struct_0(sK3),sK4)) | k2_struct_0(sK3) != k2_relset_1(k2_struct_0(sK2),u1_struct_0(sK3),sK4)),
% 0.20/0.53    inference(forward_demodulation,[],[f314,f93])).
% 0.20/0.53  fof(f314,plain,(
% 0.20/0.53    k2_struct_0(sK3) != k2_relset_1(k2_struct_0(sK2),u1_struct_0(sK3),sK4) | k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))),
% 0.20/0.53    inference(backward_demodulation,[],[f284,f93])).
% 0.20/0.53  fof(f284,plain,(
% 0.20/0.53    k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) | k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))),
% 0.20/0.53    inference(subsumption_resolution,[],[f139,f164])).
% 0.20/0.53  fof(f139,plain,(
% 0.20/0.53    k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) | ~v2_funct_1(sK4) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),
% 0.20/0.53    inference(subsumption_resolution,[],[f138,f72])).
% 0.20/0.53  fof(f138,plain,(
% 0.20/0.53    k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) | ~v2_funct_1(sK4) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) | ~l1_struct_0(sK2)),
% 0.20/0.53    inference(subsumption_resolution,[],[f137,f42])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    ~v2_struct_0(sK3)),
% 0.20/0.53    inference(cnf_transformation,[],[f36])).
% 0.20/0.53  fof(f137,plain,(
% 0.20/0.53    k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) | ~v2_funct_1(sK4) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) | v2_struct_0(sK3) | ~l1_struct_0(sK2)),
% 0.20/0.53    inference(subsumption_resolution,[],[f136,f78])).
% 0.20/0.53  fof(f136,plain,(
% 0.20/0.53    k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) | ~v2_funct_1(sK4) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) | ~l1_struct_0(sK3) | v2_struct_0(sK3) | ~l1_struct_0(sK2)),
% 0.20/0.53    inference(subsumption_resolution,[],[f135,f44])).
% 0.20/0.53  fof(f135,plain,(
% 0.20/0.53    k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) | ~v2_funct_1(sK4) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) | ~v1_funct_1(sK4) | ~l1_struct_0(sK3) | v2_struct_0(sK3) | ~l1_struct_0(sK2)),
% 0.20/0.53    inference(subsumption_resolution,[],[f121,f45])).
% 0.20/0.53  fof(f121,plain,(
% 0.20/0.53    k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) | ~v2_funct_1(sK4) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~l1_struct_0(sK3) | v2_struct_0(sK3) | ~l1_struct_0(sK2)),
% 0.20/0.53    inference(resolution,[],[f46,f63])).
% 0.20/0.53  fof(f63,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : ((k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f21])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (((k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_struct_0(X1) | v2_struct_0(X1))) | ~l1_struct_0(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,axiom,(
% 0.20/0.53    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).
% 0.20/0.53  fof(f552,plain,(
% 0.20/0.53    m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK2))))),
% 0.20/0.53    inference(backward_demodulation,[],[f439,f547])).
% 0.20/0.53  fof(f439,plain,(
% 0.20/0.53    m1_subset_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK2))))),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f44,f392,f391,f52])).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.53    inference(flattening,[],[f17])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.53    inference(ennf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).
% 0.20/0.53  fof(f551,plain,(
% 0.20/0.53    v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),k2_struct_0(sK2))),
% 0.20/0.53    inference(backward_demodulation,[],[f438,f547])).
% 0.20/0.53  fof(f438,plain,(
% 0.20/0.53    v1_funct_2(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4),k2_struct_0(sK3),k2_struct_0(sK2))),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f44,f392,f391,f51])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f18])).
% 0.20/0.53  fof(f191,plain,(
% 0.20/0.53    v2_funct_1(k2_funct_1(sK4))),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f119,f44,f164,f70])).
% 0.20/0.53  fof(f70,plain,(
% 0.20/0.53    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(flattening,[],[f27])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).
% 0.20/0.53  fof(f190,plain,(
% 0.20/0.53    v1_funct_1(k2_funct_1(sK4))),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f119,f44,f164,f69])).
% 0.20/0.53  fof(f69,plain,(
% 0.20/0.53    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f28])).
% 0.20/0.53  fof(f863,plain,(
% 0.20/0.53    ~v5_pre_topc(k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)),sK2,sK3)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f191,f613,f556,f594,f593,f726])).
% 0.20/0.53  fof(f726,plain,(
% 0.20/0.53    ( ! [X3] : (k2_struct_0(sK3) != k1_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),X3) | sP0(sK3,sK2,X3) | ~v5_pre_topc(X3,sK3,sK2) | ~v2_funct_1(X3) | ~v5_pre_topc(k2_tops_2(k2_struct_0(sK3),k2_struct_0(sK2),X3),sK2,sK3) | k2_struct_0(sK2) != k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),X3)) )),
% 0.20/0.53    inference(superposition,[],[f326,f109])).
% 0.20/0.53  fof(f326,plain,(
% 0.20/0.53    ( ! [X23,X22] : (k2_struct_0(sK2) != k2_relset_1(u1_struct_0(X22),k2_struct_0(sK2),X23) | sP0(X22,sK2,X23) | ~v5_pre_topc(X23,X22,sK2) | ~v2_funct_1(X23) | ~v5_pre_topc(k2_tops_2(u1_struct_0(X22),k2_struct_0(sK2),X23),sK2,X22) | k2_struct_0(X22) != k1_relset_1(u1_struct_0(X22),k2_struct_0(sK2),X23)) )),
% 0.20/0.53    inference(superposition,[],[f60,f93])).
% 0.20/0.53  fof(f60,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | ~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v5_pre_topc(X2,X0,X1) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f40])).
% 0.20/0.53  fof(f593,plain,(
% 0.20/0.53    k2_struct_0(sK3) = k1_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4))),
% 0.20/0.53    inference(forward_demodulation,[],[f548,f547])).
% 0.20/0.53  fof(f548,plain,(
% 0.20/0.53    k2_struct_0(sK3) = k1_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4))),
% 0.20/0.53    inference(trivial_inequality_removal,[],[f543])).
% 0.20/0.53  fof(f543,plain,(
% 0.20/0.53    k2_struct_0(sK3) != k2_struct_0(sK3) | k2_struct_0(sK3) = k1_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4))),
% 0.20/0.53    inference(backward_demodulation,[],[f535,f527])).
% 0.20/0.53  fof(f535,plain,(
% 0.20/0.53    k2_struct_0(sK3) != k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK3),sK4) | k2_struct_0(sK3) = k1_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4))),
% 0.20/0.53    inference(forward_demodulation,[],[f534,f109])).
% 0.20/0.53  fof(f534,plain,(
% 0.20/0.53    k2_struct_0(sK3) = k1_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)) | k2_struct_0(sK3) != k2_relset_1(k2_struct_0(sK2),u1_struct_0(sK3),sK4)),
% 0.20/0.53    inference(forward_demodulation,[],[f348,f109])).
% 0.20/0.53  fof(f348,plain,(
% 0.20/0.53    k2_struct_0(sK3) = k1_relset_1(u1_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),u1_struct_0(sK3),sK4)) | k2_struct_0(sK3) != k2_relset_1(k2_struct_0(sK2),u1_struct_0(sK3),sK4)),
% 0.20/0.53    inference(forward_demodulation,[],[f313,f93])).
% 0.20/0.53  fof(f313,plain,(
% 0.20/0.53    k2_struct_0(sK3) != k2_relset_1(k2_struct_0(sK2),u1_struct_0(sK3),sK4) | k2_struct_0(sK3) = k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))),
% 0.20/0.53    inference(backward_demodulation,[],[f279,f93])).
% 0.20/0.53  fof(f279,plain,(
% 0.20/0.53    k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) | k2_struct_0(sK3) = k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))),
% 0.20/0.53    inference(subsumption_resolution,[],[f134,f164])).
% 0.20/0.53  fof(f134,plain,(
% 0.20/0.53    k2_struct_0(sK3) = k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) | ~v2_funct_1(sK4) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),
% 0.20/0.53    inference(subsumption_resolution,[],[f133,f72])).
% 0.20/0.53  fof(f133,plain,(
% 0.20/0.53    k2_struct_0(sK3) = k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) | ~v2_funct_1(sK4) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) | ~l1_struct_0(sK2)),
% 0.20/0.53    inference(subsumption_resolution,[],[f132,f42])).
% 0.20/0.53  fof(f132,plain,(
% 0.20/0.53    k2_struct_0(sK3) = k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) | ~v2_funct_1(sK4) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) | v2_struct_0(sK3) | ~l1_struct_0(sK2)),
% 0.20/0.53    inference(subsumption_resolution,[],[f131,f78])).
% 0.20/0.53  fof(f131,plain,(
% 0.20/0.53    k2_struct_0(sK3) = k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) | ~v2_funct_1(sK4) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) | ~l1_struct_0(sK3) | v2_struct_0(sK3) | ~l1_struct_0(sK2)),
% 0.20/0.53    inference(subsumption_resolution,[],[f130,f44])).
% 0.20/0.53  fof(f130,plain,(
% 0.20/0.53    k2_struct_0(sK3) = k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) | ~v2_funct_1(sK4) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) | ~v1_funct_1(sK4) | ~l1_struct_0(sK3) | v2_struct_0(sK3) | ~l1_struct_0(sK2)),
% 0.20/0.53    inference(subsumption_resolution,[],[f120,f45])).
% 0.20/0.53  fof(f120,plain,(
% 0.20/0.53    k2_struct_0(sK3) = k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) | ~v2_funct_1(sK4) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~l1_struct_0(sK3) | v2_struct_0(sK3) | ~l1_struct_0(sK2)),
% 0.20/0.53    inference(resolution,[],[f46,f62])).
% 0.20/0.53  fof(f62,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f22])).
% 0.20/0.53  fof(f556,plain,(
% 0.20/0.53    ~sP0(sK3,sK2,k2_funct_1(sK4))),
% 0.20/0.53    inference(backward_demodulation,[],[f515,f547])).
% 0.20/0.53  fof(f515,plain,(
% 0.20/0.53    ~sP0(sK3,sK2,k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4))),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f457,f498,f54])).
% 0.20/0.53  fof(f54,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (v3_tops_2(X0,X2,X1) | ~sP0(X2,X1,X0) | ~sP1(X0,X1,X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f38])).
% 0.20/0.53  fof(f498,plain,(
% 0.20/0.53    sP1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4),sK2,sK3)),
% 0.20/0.53    inference(forward_demodulation,[],[f497,f93])).
% 0.20/0.53  fof(f497,plain,(
% 0.20/0.53    sP1(k2_tops_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4),sK2,sK3)),
% 0.20/0.53    inference(forward_demodulation,[],[f217,f109])).
% 0.20/0.53  fof(f217,plain,(
% 0.20/0.53    sP1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK2,sK3)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f43,f41,f116,f117,f118,f61])).
% 0.20/0.53  fof(f118,plain,(
% 0.20/0.53    m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f44,f45,f46,f52])).
% 0.20/0.53  fof(f117,plain,(
% 0.20/0.53    v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2))),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f44,f45,f46,f51])).
% 0.20/0.53  fof(f116,plain,(
% 0.20/0.53    v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f44,f45,f46,f50])).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (v1_funct_1(k2_tops_2(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f18])).
% 0.20/0.53  fof(f457,plain,(
% 0.20/0.53    ~v3_tops_2(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4),sK3,sK2)),
% 0.20/0.53    inference(forward_demodulation,[],[f308,f109])).
% 0.20/0.53  fof(f308,plain,(
% 0.20/0.53    ~v3_tops_2(k2_tops_2(k2_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)),
% 0.20/0.53    inference(backward_demodulation,[],[f48,f93])).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    ~v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)),
% 0.20/0.53    inference(cnf_transformation,[],[f36])).
% 0.20/0.53  fof(f613,plain,(
% 0.20/0.53    v5_pre_topc(k2_funct_1(sK4),sK3,sK2)),
% 0.20/0.53    inference(forward_demodulation,[],[f529,f547])).
% 0.20/0.53  fof(f529,plain,(
% 0.20/0.53    v5_pre_topc(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4),sK3,sK2)),
% 0.20/0.53    inference(forward_demodulation,[],[f528,f93])).
% 0.20/0.53  fof(f528,plain,(
% 0.20/0.53    v5_pre_topc(k2_tops_2(u1_struct_0(sK2),k2_struct_0(sK3),sK4),sK3,sK2)),
% 0.20/0.53    inference(forward_demodulation,[],[f166,f109])).
% 0.20/0.53  fof(f166,plain,(
% 0.20/0.53    v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f158,f59])).
% 0.20/0.53  fof(f59,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~sP0(X0,X1,X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f40])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (16027)------------------------------
% 0.20/0.53  % (16027)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (16027)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (16027)Memory used [KB]: 2174
% 0.20/0.53  % (16027)Time elapsed: 0.092 s
% 0.20/0.53  % (16027)------------------------------
% 0.20/0.53  % (16027)------------------------------
% 0.20/0.53  % (16009)Success in time 0.177 s
%------------------------------------------------------------------------------
