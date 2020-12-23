%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:24 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 113 expanded)
%              Number of leaves         :   18 (  52 expanded)
%              Depth                    :    7
%              Number of atoms          :  195 ( 311 expanded)
%              Number of equality atoms :   19 (  22 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f192,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f39,f44,f50,f61,f66,f72,f89,f139,f191])).

fof(f191,plain,
    ( ~ spl3_2
    | ~ spl3_9
    | spl3_13 ),
    inference(avatar_contradiction_clause,[],[f190])).

fof(f190,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_9
    | spl3_13 ),
    inference(trivial_inequality_removal,[],[f188])).

fof(f188,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl3_2
    | ~ spl3_9
    | spl3_13 ),
    inference(unit_resulting_resolution,[],[f88,f38,f138,f28])).

fof(f28,plain,(
    ! [X2,X0,X3] :
      ( sP2(X3,X0)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
      | ~ l1_pre_topc(X2)
      | ~ m1_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f28_D])).

fof(f28_D,plain,(
    ! [X0,X3] :
      ( ! [X2] :
          ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
          | ~ l1_pre_topc(X2)
          | ~ m1_pre_topc(X2,X0) )
    <=> ~ sP2(X3,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP2])])).

fof(f138,plain,
    ( ~ sP2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl3_13
  <=> sP2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f38,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl3_2
  <=> m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f88,plain,
    ( l1_pre_topc(sK1)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl3_9
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f139,plain,
    ( ~ spl3_13
    | spl3_1
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f128,f86,f69,f63,f41,f31,f136])).

fof(f31,plain,
    ( spl3_1
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f41,plain,
    ( spl3_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f63,plain,
    ( spl3_6
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f69,plain,
    ( spl3_7
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f128,plain,
    ( ~ sP2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl3_1
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f88,f33,f43,f65,f71,f29])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | m1_pre_topc(X3,X1)
      | ~ l1_pre_topc(X3)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ sP2(X3,X0) ) ),
    inference(general_splitting,[],[f23,f28_D])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_pre_topc(X3,X1)
      | ~ m1_pre_topc(X2,X0)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | ~ l1_pre_topc(X3)
      | ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( m1_pre_topc(X3,X1)
                  | ~ m1_pre_topc(X2,X0)
                  | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ l1_pre_topc(X3) )
              | ~ l1_pre_topc(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( m1_pre_topc(X3,X1)
                  | ~ m1_pre_topc(X2,X0)
                  | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ l1_pre_topc(X3) )
              | ~ l1_pre_topc(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( l1_pre_topc(X2)
             => ! [X3] :
                  ( l1_pre_topc(X3)
                 => ( ( m1_pre_topc(X2,X0)
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                      & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                   => m1_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_pre_topc)).

fof(f71,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f69])).

fof(f65,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f63])).

fof(f43,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f33,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f89,plain,
    ( spl3_9
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f77,f63,f36,f86])).

fof(f77,plain,
    ( l1_pre_topc(sK1)
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f38,f65,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f72,plain,
    ( ~ spl3_6
    | spl3_7
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f67,f58,f69,f63])).

fof(f58,plain,
    ( spl3_5
  <=> v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f67,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl3_5 ),
    inference(resolution,[],[f60,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f60,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f58])).

fof(f66,plain,
    ( spl3_6
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f55,f47,f63])).

fof(f47,plain,
    ( spl3_4
  <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f55,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f49,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f49,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f47])).

fof(f61,plain,
    ( spl3_5
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f56,f47,f58])).

fof(f56,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f49,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f50,plain,
    ( spl3_4
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f45,f41,f47])).

fof(f45,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f43,f27])).

fof(f27,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f44,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f19,f41])).

fof(f19,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    & m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f17,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ m1_pre_topc(X1,X0)
            & m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ m1_pre_topc(X1,sK0)
          & m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X1] :
        ( ~ m1_pre_topc(X1,sK0)
        & m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
   => ( ~ m1_pre_topc(sK1,sK0)
      & m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ m1_pre_topc(X1,X0)
          & m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
           => m1_pre_topc(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

fof(f39,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f20,f36])).

fof(f20,plain,(
    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f34,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f21,f31])).

fof(f21,plain,(
    ~ m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:14:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.52  % (2251)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.52  % (2256)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.52  % (2257)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.52  % (2255)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.52  % (2261)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.53  % (2266)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.53  % (2258)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (2261)Refutation not found, incomplete strategy% (2261)------------------------------
% 0.22/0.53  % (2261)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (2261)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (2261)Memory used [KB]: 10490
% 0.22/0.53  % (2261)Time elapsed: 0.113 s
% 0.22/0.53  % (2261)------------------------------
% 0.22/0.53  % (2261)------------------------------
% 0.22/0.54  % (2257)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f192,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f34,f39,f44,f50,f61,f66,f72,f89,f139,f191])).
% 0.22/0.54  fof(f191,plain,(
% 0.22/0.54    ~spl3_2 | ~spl3_9 | spl3_13),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f190])).
% 0.22/0.54  fof(f190,plain,(
% 0.22/0.54    $false | (~spl3_2 | ~spl3_9 | spl3_13)),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f188])).
% 0.22/0.54  fof(f188,plain,(
% 0.22/0.54    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) | (~spl3_2 | ~spl3_9 | spl3_13)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f88,f38,f138,f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ( ! [X2,X0,X3] : (sP2(X3,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | ~l1_pre_topc(X2) | ~m1_pre_topc(X2,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f28_D])).
% 0.22/0.54  fof(f28_D,plain,(
% 0.22/0.54    ( ! [X0,X3] : (( ! [X2] : (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | ~l1_pre_topc(X2) | ~m1_pre_topc(X2,X0)) ) <=> ~sP2(X3,X0)) )),
% 0.22/0.54    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP2])])).
% 0.22/0.54  fof(f138,plain,(
% 0.22/0.54    ~sP2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | spl3_13),
% 0.22/0.54    inference(avatar_component_clause,[],[f136])).
% 0.22/0.54  fof(f136,plain,(
% 0.22/0.54    spl3_13 <=> sP2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl3_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    spl3_2 <=> m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.54  fof(f88,plain,(
% 0.22/0.54    l1_pre_topc(sK1) | ~spl3_9),
% 0.22/0.54    inference(avatar_component_clause,[],[f86])).
% 0.22/0.54  fof(f86,plain,(
% 0.22/0.54    spl3_9 <=> l1_pre_topc(sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.54  fof(f139,plain,(
% 0.22/0.54    ~spl3_13 | spl3_1 | ~spl3_3 | ~spl3_6 | ~spl3_7 | ~spl3_9),
% 0.22/0.54    inference(avatar_split_clause,[],[f128,f86,f69,f63,f41,f31,f136])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    spl3_1 <=> m1_pre_topc(sK1,sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    spl3_3 <=> l1_pre_topc(sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    spl3_6 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.54  fof(f69,plain,(
% 0.22/0.54    spl3_7 <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.54  fof(f128,plain,(
% 0.22/0.54    ~sP2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (spl3_1 | ~spl3_3 | ~spl3_6 | ~spl3_7 | ~spl3_9)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f88,f33,f43,f65,f71,f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ( ! [X0,X3,X1] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | m1_pre_topc(X3,X1) | ~l1_pre_topc(X3) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~sP2(X3,X0)) )),
% 0.22/0.54    inference(general_splitting,[],[f23,f28_D])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (m1_pre_topc(X3,X1) | ~m1_pre_topc(X2,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~l1_pre_topc(X3) | ~l1_pre_topc(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (m1_pre_topc(X3,X1) | ~m1_pre_topc(X2,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~l1_pre_topc(X3)) | ~l1_pre_topc(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f10])).
% 0.22/0.54  fof(f10,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_pre_topc(X3,X1) | (~m1_pre_topc(X2,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X3)) | ~l1_pre_topc(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (l1_pre_topc(X2) => ! [X3] : (l1_pre_topc(X3) => ((m1_pre_topc(X2,X0) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => m1_pre_topc(X3,X1))))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_pre_topc)).
% 0.22/0.54  fof(f71,plain,(
% 0.22/0.54    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~spl3_7),
% 0.22/0.54    inference(avatar_component_clause,[],[f69])).
% 0.22/0.54  fof(f65,plain,(
% 0.22/0.54    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl3_6),
% 0.22/0.54    inference(avatar_component_clause,[],[f63])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    l1_pre_topc(sK0) | ~spl3_3),
% 0.22/0.54    inference(avatar_component_clause,[],[f41])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ~m1_pre_topc(sK1,sK0) | spl3_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f31])).
% 0.22/0.54  fof(f89,plain,(
% 0.22/0.54    spl3_9 | ~spl3_2 | ~spl3_6),
% 0.22/0.54    inference(avatar_split_clause,[],[f77,f63,f36,f86])).
% 0.22/0.54  fof(f77,plain,(
% 0.22/0.54    l1_pre_topc(sK1) | (~spl3_2 | ~spl3_6)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f38,f65,f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    ~spl3_6 | spl3_7 | ~spl3_5),
% 0.22/0.54    inference(avatar_split_clause,[],[f67,f58,f69,f63])).
% 0.22/0.54  fof(f58,plain,(
% 0.22/0.54    spl3_5 <=> v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.54  fof(f67,plain,(
% 0.22/0.54    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl3_5),
% 0.22/0.54    inference(resolution,[],[f60,f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ( ! [X0] : (~v1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~l1_pre_topc(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f14])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f13])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl3_5),
% 0.22/0.54    inference(avatar_component_clause,[],[f58])).
% 0.22/0.54  fof(f66,plain,(
% 0.22/0.54    spl3_6 | ~spl3_4),
% 0.22/0.54    inference(avatar_split_clause,[],[f55,f47,f63])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    spl3_4 <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl3_4),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f49,f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,plain,(
% 0.22/0.54    ! [X0,X1] : ((l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.54    inference(ennf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_4),
% 0.22/0.54    inference(avatar_component_clause,[],[f47])).
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    spl3_5 | ~spl3_4),
% 0.22/0.54    inference(avatar_split_clause,[],[f56,f47,f58])).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl3_4),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f49,f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f12])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    spl3_4 | ~spl3_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f45,f41,f47])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_3),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f43,f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    spl3_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f19,f41])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    l1_pre_topc(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    (~m1_pre_topc(sK1,sK0) & m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) & l1_pre_topc(sK0)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f17,f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (~m1_pre_topc(X1,X0) & m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~m1_pre_topc(X1,sK0) & m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) & l1_pre_topc(sK0))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ? [X1] : (~m1_pre_topc(X1,sK0) & m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) => (~m1_pre_topc(sK1,sK0) & m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f8,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (~m1_pre_topc(X1,X0) & m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) & l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,negated_conjecture,(
% 0.22/0.54    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 0.22/0.54    inference(negated_conjecture,[],[f6])).
% 0.22/0.54  fof(f6,conjecture,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    spl3_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f20,f36])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ~spl3_1),
% 0.22/0.54    inference(avatar_split_clause,[],[f21,f31])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ~m1_pre_topc(sK1,sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (2257)------------------------------
% 0.22/0.54  % (2257)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (2257)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (2257)Memory used [KB]: 10746
% 0.22/0.54  % (2257)Time elapsed: 0.117 s
% 0.22/0.54  % (2257)------------------------------
% 0.22/0.54  % (2257)------------------------------
% 0.22/0.54  % (2258)Refutation not found, incomplete strategy% (2258)------------------------------
% 0.22/0.54  % (2258)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (2258)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (2258)Memory used [KB]: 6012
% 0.22/0.54  % (2258)Time elapsed: 0.045 s
% 0.22/0.54  % (2258)------------------------------
% 0.22/0.54  % (2258)------------------------------
% 0.22/0.54  % (2250)Success in time 0.176 s
%------------------------------------------------------------------------------
