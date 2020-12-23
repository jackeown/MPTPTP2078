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
% DateTime   : Thu Dec  3 13:20:33 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 141 expanded)
%              Number of leaves         :   20 (  62 expanded)
%              Depth                    :    7
%              Number of atoms          :  254 ( 529 expanded)
%              Number of equality atoms :   12 (  50 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f140,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f34,f39,f44,f49,f53,f57,f61,f65,f71,f78,f100,f108,f135,f139])).

fof(f139,plain,
    ( spl2_1
    | ~ spl2_10
    | ~ spl2_19 ),
    inference(avatar_contradiction_clause,[],[f138])).

fof(f138,plain,
    ( $false
    | spl2_1
    | ~ spl2_10
    | ~ spl2_19 ),
    inference(subsumption_resolution,[],[f136,f28])).

fof(f28,plain,
    ( ~ v2_pre_topc(sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl2_1
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f136,plain,
    ( v2_pre_topc(sK1)
    | ~ spl2_10
    | ~ spl2_19 ),
    inference(resolution,[],[f134,f70])).

fof(f70,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_pre_topc(X0) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl2_10
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f134,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl2_19
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f135,plain,
    ( spl2_19
    | ~ spl2_5
    | ~ spl2_11
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f130,f105,f76,f46,f132])).

fof(f46,plain,
    ( spl2_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f76,plain,
    ( spl2_11
  <=> ! [X0] :
        ( ~ m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        | ~ l1_pre_topc(X0)
        | m1_pre_topc(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f105,plain,
    ( spl2_16
  <=> m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f130,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl2_5
    | ~ spl2_11
    | ~ spl2_16 ),
    inference(subsumption_resolution,[],[f128,f48])).

fof(f48,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f46])).

fof(f128,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_pre_topc(sK1,sK0)
    | ~ spl2_11
    | ~ spl2_16 ),
    inference(resolution,[],[f107,f77])).

fof(f77,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        | ~ l1_pre_topc(X0)
        | m1_pre_topc(sK1,X0) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f76])).

fof(f107,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f105])).

fof(f108,plain,
    ( spl2_16
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f103,f98,f41,f36,f105])).

fof(f36,plain,
    ( spl2_3
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f41,plain,
    ( spl2_4
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f98,plain,
    ( spl2_15
  <=> ! [X0] :
        ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f103,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_15 ),
    inference(forward_demodulation,[],[f101,f38])).

fof(f38,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f36])).

fof(f101,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl2_4
    | ~ spl2_15 ),
    inference(resolution,[],[f99,f43])).

fof(f43,plain,
    ( l1_pre_topc(sK1)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f41])).

fof(f99,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f98])).

fof(f100,plain,
    ( spl2_15
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f96,f59,f51,f98])).

fof(f51,plain,
    ( spl2_6
  <=> ! [X0] :
        ( m1_pre_topc(X0,X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f59,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ m1_pre_topc(X0,X1)
        | ~ l1_pre_topc(X1)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f96,plain,
    ( ! [X0] :
        ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(duplicate_literal_removal,[],[f95])).

fof(f95,plain,
    ( ! [X0] :
        ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        | ~ l1_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(resolution,[],[f60,f52])).

fof(f52,plain,
    ( ! [X0] :
        ( m1_pre_topc(X0,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f51])).

fof(f60,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,X1)
        | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ l1_pre_topc(X1)
        | ~ l1_pre_topc(X0) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f59])).

fof(f78,plain,
    ( spl2_11
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f73,f55,f41,f76])).

fof(f55,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ l1_pre_topc(X1)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f73,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        | ~ l1_pre_topc(X0)
        | m1_pre_topc(sK1,X0) )
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(resolution,[],[f56,f43])).

fof(f56,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ l1_pre_topc(X1)
        | m1_pre_topc(X0,X1) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f55])).

fof(f71,plain,
    ( spl2_10
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f67,f63,f46,f31,f69])).

fof(f31,plain,
    ( spl2_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f63,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( v2_pre_topc(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f67,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_pre_topc(X0) )
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f66,f48])).

fof(f66,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | v2_pre_topc(X0) )
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(resolution,[],[f64,f33])).

fof(f33,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f64,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0)
        | v2_pre_topc(X1) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f63])).

fof(f65,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f24,f63])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f61,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f22,f59])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f57,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f23,f55])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f53,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f21,f51])).

fof(f21,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f49,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f16,f46])).

fof(f16,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

% (23717)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
fof(f14,plain,
    ( ~ v2_pre_topc(sK1)
    & v2_pre_topc(sK0)
    & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f13,f12])).

fof(f12,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_pre_topc(X1)
            & v2_pre_topc(X0)
            & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v2_pre_topc(X1)
          & v2_pre_topc(sK0)
          & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X1] :
        ( ~ v2_pre_topc(X1)
        & v2_pre_topc(sK0)
        & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        & l1_pre_topc(X1) )
   => ( ~ v2_pre_topc(sK1)
      & v2_pre_topc(sK0)
      & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_pre_topc(X1)
          & v2_pre_topc(X0)
          & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_pre_topc(X1)
          & v2_pre_topc(X0)
          & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ( ( v2_pre_topc(X0)
                & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) )
             => v2_pre_topc(X1) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( ( v2_pre_topc(X0)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) )
           => v2_pre_topc(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tex_2)).

fof(f44,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f17,f41])).

fof(f17,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f39,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f18,f36])).

fof(f18,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f34,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f19,f31])).

fof(f19,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f29,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f20,f26])).

fof(f20,plain,(
    ~ v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:11:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.44  % (23719)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.44  % (23718)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.44  % (23718)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f140,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(avatar_sat_refutation,[],[f29,f34,f39,f44,f49,f53,f57,f61,f65,f71,f78,f100,f108,f135,f139])).
% 0.22/0.44  fof(f139,plain,(
% 0.22/0.44    spl2_1 | ~spl2_10 | ~spl2_19),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f138])).
% 0.22/0.44  fof(f138,plain,(
% 0.22/0.44    $false | (spl2_1 | ~spl2_10 | ~spl2_19)),
% 0.22/0.44    inference(subsumption_resolution,[],[f136,f28])).
% 0.22/0.44  fof(f28,plain,(
% 0.22/0.44    ~v2_pre_topc(sK1) | spl2_1),
% 0.22/0.44    inference(avatar_component_clause,[],[f26])).
% 0.22/0.44  fof(f26,plain,(
% 0.22/0.44    spl2_1 <=> v2_pre_topc(sK1)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.44  fof(f136,plain,(
% 0.22/0.44    v2_pre_topc(sK1) | (~spl2_10 | ~spl2_19)),
% 0.22/0.44    inference(resolution,[],[f134,f70])).
% 0.22/0.44  fof(f70,plain,(
% 0.22/0.44    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_pre_topc(X0)) ) | ~spl2_10),
% 0.22/0.44    inference(avatar_component_clause,[],[f69])).
% 0.22/0.44  fof(f69,plain,(
% 0.22/0.44    spl2_10 <=> ! [X0] : (~m1_pre_topc(X0,sK0) | v2_pre_topc(X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.44  fof(f134,plain,(
% 0.22/0.44    m1_pre_topc(sK1,sK0) | ~spl2_19),
% 0.22/0.44    inference(avatar_component_clause,[],[f132])).
% 0.22/0.44  fof(f132,plain,(
% 0.22/0.44    spl2_19 <=> m1_pre_topc(sK1,sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.22/0.44  fof(f135,plain,(
% 0.22/0.44    spl2_19 | ~spl2_5 | ~spl2_11 | ~spl2_16),
% 0.22/0.44    inference(avatar_split_clause,[],[f130,f105,f76,f46,f132])).
% 0.22/0.44  fof(f46,plain,(
% 0.22/0.44    spl2_5 <=> l1_pre_topc(sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.44  fof(f76,plain,(
% 0.22/0.44    spl2_11 <=> ! [X0] : (~m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | m1_pre_topc(sK1,X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.22/0.44  fof(f105,plain,(
% 0.22/0.44    spl2_16 <=> m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.22/0.44  fof(f130,plain,(
% 0.22/0.44    m1_pre_topc(sK1,sK0) | (~spl2_5 | ~spl2_11 | ~spl2_16)),
% 0.22/0.44    inference(subsumption_resolution,[],[f128,f48])).
% 0.22/0.44  fof(f48,plain,(
% 0.22/0.44    l1_pre_topc(sK0) | ~spl2_5),
% 0.22/0.44    inference(avatar_component_clause,[],[f46])).
% 0.22/0.44  fof(f128,plain,(
% 0.22/0.44    ~l1_pre_topc(sK0) | m1_pre_topc(sK1,sK0) | (~spl2_11 | ~spl2_16)),
% 0.22/0.44    inference(resolution,[],[f107,f77])).
% 0.22/0.44  fof(f77,plain,(
% 0.22/0.44    ( ! [X0] : (~m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | m1_pre_topc(sK1,X0)) ) | ~spl2_11),
% 0.22/0.44    inference(avatar_component_clause,[],[f76])).
% 0.22/0.44  fof(f107,plain,(
% 0.22/0.44    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_16),
% 0.22/0.44    inference(avatar_component_clause,[],[f105])).
% 0.22/0.44  fof(f108,plain,(
% 0.22/0.44    spl2_16 | ~spl2_3 | ~spl2_4 | ~spl2_15),
% 0.22/0.44    inference(avatar_split_clause,[],[f103,f98,f41,f36,f105])).
% 0.22/0.44  fof(f36,plain,(
% 0.22/0.44    spl2_3 <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.44  fof(f41,plain,(
% 0.22/0.44    spl2_4 <=> l1_pre_topc(sK1)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.44  fof(f98,plain,(
% 0.22/0.44    spl2_15 <=> ! [X0] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.22/0.44  fof(f103,plain,(
% 0.22/0.44    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl2_3 | ~spl2_4 | ~spl2_15)),
% 0.22/0.44    inference(forward_demodulation,[],[f101,f38])).
% 0.22/0.44  fof(f38,plain,(
% 0.22/0.44    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) | ~spl2_3),
% 0.22/0.44    inference(avatar_component_clause,[],[f36])).
% 0.22/0.44  fof(f101,plain,(
% 0.22/0.44    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl2_4 | ~spl2_15)),
% 0.22/0.44    inference(resolution,[],[f99,f43])).
% 0.22/0.44  fof(f43,plain,(
% 0.22/0.44    l1_pre_topc(sK1) | ~spl2_4),
% 0.22/0.44    inference(avatar_component_clause,[],[f41])).
% 0.22/0.44  fof(f99,plain,(
% 0.22/0.44    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) ) | ~spl2_15),
% 0.22/0.44    inference(avatar_component_clause,[],[f98])).
% 0.22/0.44  fof(f100,plain,(
% 0.22/0.44    spl2_15 | ~spl2_6 | ~spl2_8),
% 0.22/0.44    inference(avatar_split_clause,[],[f96,f59,f51,f98])).
% 0.22/0.44  fof(f51,plain,(
% 0.22/0.44    spl2_6 <=> ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.44  fof(f59,plain,(
% 0.22/0.44    spl2_8 <=> ! [X1,X0] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.44  fof(f96,plain,(
% 0.22/0.44    ( ! [X0] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) ) | (~spl2_6 | ~spl2_8)),
% 0.22/0.44    inference(duplicate_literal_removal,[],[f95])).
% 0.22/0.44  fof(f95,plain,(
% 0.22/0.44    ( ! [X0] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~l1_pre_topc(X0) | ~l1_pre_topc(X0)) ) | (~spl2_6 | ~spl2_8)),
% 0.22/0.44    inference(resolution,[],[f60,f52])).
% 0.22/0.44  fof(f52,plain,(
% 0.22/0.44    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) ) | ~spl2_6),
% 0.22/0.44    inference(avatar_component_clause,[],[f51])).
% 0.22/0.44  fof(f60,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) ) | ~spl2_8),
% 0.22/0.44    inference(avatar_component_clause,[],[f59])).
% 0.22/0.44  fof(f78,plain,(
% 0.22/0.44    spl2_11 | ~spl2_4 | ~spl2_7),
% 0.22/0.44    inference(avatar_split_clause,[],[f73,f55,f41,f76])).
% 0.22/0.44  fof(f55,plain,(
% 0.22/0.44    spl2_7 <=> ! [X1,X0] : (m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.44  fof(f73,plain,(
% 0.22/0.44    ( ! [X0] : (~m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | m1_pre_topc(sK1,X0)) ) | (~spl2_4 | ~spl2_7)),
% 0.22/0.44    inference(resolution,[],[f56,f43])).
% 0.22/0.44  fof(f56,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1) | m1_pre_topc(X0,X1)) ) | ~spl2_7),
% 0.22/0.44    inference(avatar_component_clause,[],[f55])).
% 0.22/0.44  fof(f71,plain,(
% 0.22/0.44    spl2_10 | ~spl2_2 | ~spl2_5 | ~spl2_9),
% 0.22/0.44    inference(avatar_split_clause,[],[f67,f63,f46,f31,f69])).
% 0.22/0.44  fof(f31,plain,(
% 0.22/0.44    spl2_2 <=> v2_pre_topc(sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.44  fof(f63,plain,(
% 0.22/0.44    spl2_9 <=> ! [X1,X0] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.44  fof(f67,plain,(
% 0.22/0.44    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_pre_topc(X0)) ) | (~spl2_2 | ~spl2_5 | ~spl2_9)),
% 0.22/0.44    inference(subsumption_resolution,[],[f66,f48])).
% 0.22/0.44  fof(f66,plain,(
% 0.22/0.44    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | v2_pre_topc(X0)) ) | (~spl2_2 | ~spl2_9)),
% 0.22/0.44    inference(resolution,[],[f64,f33])).
% 0.22/0.44  fof(f33,plain,(
% 0.22/0.44    v2_pre_topc(sK0) | ~spl2_2),
% 0.22/0.44    inference(avatar_component_clause,[],[f31])).
% 0.22/0.44  fof(f64,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_pre_topc(X1)) ) | ~spl2_9),
% 0.22/0.44    inference(avatar_component_clause,[],[f63])).
% 0.22/0.44  fof(f65,plain,(
% 0.22/0.44    spl2_9),
% 0.22/0.44    inference(avatar_split_clause,[],[f24,f63])).
% 0.22/0.44  fof(f24,plain,(
% 0.22/0.44    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f11])).
% 0.22/0.44  fof(f11,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.44    inference(flattening,[],[f10])).
% 0.22/0.44  fof(f10,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.44    inference(ennf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.22/0.44  fof(f61,plain,(
% 0.22/0.44    spl2_8),
% 0.22/0.44    inference(avatar_split_clause,[],[f22,f59])).
% 0.22/0.44  fof(f22,plain,(
% 0.22/0.44    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f15])).
% 0.22/0.44  fof(f15,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.44    inference(nnf_transformation,[],[f9])).
% 0.22/0.44  fof(f9,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).
% 0.22/0.44  fof(f57,plain,(
% 0.22/0.44    spl2_7),
% 0.22/0.44    inference(avatar_split_clause,[],[f23,f55])).
% 0.22/0.44  fof(f23,plain,(
% 0.22/0.44    ( ! [X0,X1] : (m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f15])).
% 0.22/0.44  fof(f53,plain,(
% 0.22/0.44    spl2_6),
% 0.22/0.44    inference(avatar_split_clause,[],[f21,f51])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f8])).
% 0.22/0.44  fof(f8,plain,(
% 0.22/0.44    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.22/0.44  fof(f49,plain,(
% 0.22/0.44    spl2_5),
% 0.22/0.44    inference(avatar_split_clause,[],[f16,f46])).
% 0.22/0.44  fof(f16,plain,(
% 0.22/0.44    l1_pre_topc(sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f14])).
% 0.22/0.44  % (23717)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.44  fof(f14,plain,(
% 0.22/0.44    (~v2_pre_topc(sK1) & v2_pre_topc(sK0) & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & l1_pre_topc(sK1)) & l1_pre_topc(sK0)),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f13,f12])).
% 0.22/0.44  fof(f12,plain,(
% 0.22/0.44    ? [X0] : (? [X1] : (~v2_pre_topc(X1) & v2_pre_topc(X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) & l1_pre_topc(X1)) & l1_pre_topc(X0)) => (? [X1] : (~v2_pre_topc(X1) & v2_pre_topc(sK0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) & l1_pre_topc(X1)) & l1_pre_topc(sK0))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f13,plain,(
% 0.22/0.44    ? [X1] : (~v2_pre_topc(X1) & v2_pre_topc(sK0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) & l1_pre_topc(X1)) => (~v2_pre_topc(sK1) & v2_pre_topc(sK0) & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & l1_pre_topc(sK1))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f7,plain,(
% 0.22/0.44    ? [X0] : (? [X1] : (~v2_pre_topc(X1) & v2_pre_topc(X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.22/0.44    inference(flattening,[],[f6])).
% 0.22/0.44  fof(f6,plain,(
% 0.22/0.44    ? [X0] : (? [X1] : ((~v2_pre_topc(X1) & (v2_pre_topc(X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f5])).
% 0.22/0.44  fof(f5,negated_conjecture,(
% 0.22/0.44    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v2_pre_topc(X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => v2_pre_topc(X1))))),
% 0.22/0.44    inference(negated_conjecture,[],[f4])).
% 0.22/0.44  fof(f4,conjecture,(
% 0.22/0.44    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v2_pre_topc(X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => v2_pre_topc(X1))))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tex_2)).
% 0.22/0.44  fof(f44,plain,(
% 0.22/0.44    spl2_4),
% 0.22/0.44    inference(avatar_split_clause,[],[f17,f41])).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    l1_pre_topc(sK1)),
% 0.22/0.44    inference(cnf_transformation,[],[f14])).
% 0.22/0.44  fof(f39,plain,(
% 0.22/0.44    spl2_3),
% 0.22/0.44    inference(avatar_split_clause,[],[f18,f36])).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 0.22/0.44    inference(cnf_transformation,[],[f14])).
% 0.22/0.44  fof(f34,plain,(
% 0.22/0.44    spl2_2),
% 0.22/0.44    inference(avatar_split_clause,[],[f19,f31])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    v2_pre_topc(sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f14])).
% 0.22/0.44  fof(f29,plain,(
% 0.22/0.44    ~spl2_1),
% 0.22/0.44    inference(avatar_split_clause,[],[f20,f26])).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    ~v2_pre_topc(sK1)),
% 0.22/0.44    inference(cnf_transformation,[],[f14])).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (23718)------------------------------
% 0.22/0.44  % (23718)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (23718)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (23718)Memory used [KB]: 10618
% 0.22/0.44  % (23718)Time elapsed: 0.006 s
% 0.22/0.44  % (23718)------------------------------
% 0.22/0.44  % (23718)------------------------------
% 0.22/0.45  % (23721)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.22/0.45  % (23720)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.45  % (23712)Success in time 0.088 s
%------------------------------------------------------------------------------
