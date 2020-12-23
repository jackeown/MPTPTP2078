%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:58 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 747 expanded)
%              Number of leaves         :   16 ( 276 expanded)
%              Depth                    :   26
%              Number of atoms          :  367 (6472 expanded)
%              Number of equality atoms :    5 (  10 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f170,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f76,f153,f161,f167])).

fof(f167,plain,
    ( spl4_3
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f166])).

fof(f166,plain,
    ( $false
    | spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f165,f104])).

fof(f104,plain,(
    l1_struct_0(sK3) ),
    inference(resolution,[],[f103,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f103,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f98,f36])).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( ~ r1_tsep_1(sK3,sK1)
      | ~ r1_tsep_1(sK1,sK3) )
    & ( r1_tsep_1(sK3,sK2)
      | r1_tsep_1(sK2,sK3) )
    & m1_pre_topc(sK1,sK2)
    & m1_pre_topc(sK3,sK0)
    & m1_pre_topc(sK2,sK0)
    & m1_pre_topc(sK1,sK0)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f28,f27,f26,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ r1_tsep_1(X3,X1)
                      | ~ r1_tsep_1(X1,X3) )
                    & ( r1_tsep_1(X3,X2)
                      | r1_tsep_1(X2,X3) )
                    & m1_pre_topc(X1,X2)
                    & m1_pre_topc(X3,X0) )
                & m1_pre_topc(X2,X0) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,sK0) )
              & m1_pre_topc(X2,sK0) )
          & m1_pre_topc(X1,sK0) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ r1_tsep_1(X3,X1)
                  | ~ r1_tsep_1(X1,X3) )
                & ( r1_tsep_1(X3,X2)
                  | r1_tsep_1(X2,X3) )
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X3,sK0) )
            & m1_pre_topc(X2,sK0) )
        & m1_pre_topc(X1,sK0) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ r1_tsep_1(X3,sK1)
                | ~ r1_tsep_1(sK1,X3) )
              & ( r1_tsep_1(X3,X2)
                | r1_tsep_1(X2,X3) )
              & m1_pre_topc(sK1,X2)
              & m1_pre_topc(X3,sK0) )
          & m1_pre_topc(X2,sK0) )
      & m1_pre_topc(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ r1_tsep_1(X3,sK1)
              | ~ r1_tsep_1(sK1,X3) )
            & ( r1_tsep_1(X3,X2)
              | r1_tsep_1(X2,X3) )
            & m1_pre_topc(sK1,X2)
            & m1_pre_topc(X3,sK0) )
        & m1_pre_topc(X2,sK0) )
   => ( ? [X3] :
          ( ( ~ r1_tsep_1(X3,sK1)
            | ~ r1_tsep_1(sK1,X3) )
          & ( r1_tsep_1(X3,sK2)
            | r1_tsep_1(sK2,X3) )
          & m1_pre_topc(sK1,sK2)
          & m1_pre_topc(X3,sK0) )
      & m1_pre_topc(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X3] :
        ( ( ~ r1_tsep_1(X3,sK1)
          | ~ r1_tsep_1(sK1,X3) )
        & ( r1_tsep_1(X3,sK2)
          | r1_tsep_1(sK2,X3) )
        & m1_pre_topc(sK1,sK2)
        & m1_pre_topc(X3,sK0) )
   => ( ( ~ r1_tsep_1(sK3,sK1)
        | ~ r1_tsep_1(sK1,sK3) )
      & ( r1_tsep_1(sK3,sK2)
        | r1_tsep_1(sK2,sK3) )
      & m1_pre_topc(sK1,sK2)
      & m1_pre_topc(sK3,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0) )
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0) )
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ! [X3] :
                    ( m1_pre_topc(X3,X0)
                   => ( m1_pre_topc(X1,X2)
                     => ( ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) )
                        | ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( m1_pre_topc(X1,X2)
                     => ( ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) )
                        | ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( m1_pre_topc(X1,X2)
                   => ( ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) )
                      | ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tmap_1)).

fof(f98,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f39,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f39,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f165,plain,
    ( ~ l1_struct_0(sK3)
    | spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f164,f95])).

fof(f95,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f93,f45])).

fof(f93,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f88,f36])).

fof(f88,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f38,f46])).

% (29807)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% (29791)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% (29800)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
fof(f38,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f164,plain,
    ( ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK3)
    | spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f162,f70])).

fof(f70,plain,
    ( ~ r1_tsep_1(sK2,sK3)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl4_3
  <=> r1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f162,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK3)
    | ~ spl4_4 ),
    inference(resolution,[],[f75,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | r1_tsep_1(X1,X0)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(f75,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl4_4
  <=> r1_tsep_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f161,plain,
    ( spl4_2
    | ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f160])).

fof(f160,plain,
    ( $false
    | spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f159,f94])).

fof(f94,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f85,f45])).

fof(f85,plain,(
    l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f80,f36])).

fof(f80,plain,
    ( l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f37,f46])).

fof(f37,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f159,plain,
    ( ~ l1_struct_0(sK1)
    | spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f158,f104])).

fof(f158,plain,
    ( ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK1)
    | spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f156,f66])).

fof(f66,plain,
    ( ~ r1_tsep_1(sK3,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl4_2
  <=> r1_tsep_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f156,plain,
    ( r1_tsep_1(sK3,sK1)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK1)
    | ~ spl4_3 ),
    inference(resolution,[],[f155,f50])).

fof(f155,plain,
    ( r1_tsep_1(sK1,sK3)
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f154,f94])).

fof(f154,plain,
    ( r1_tsep_1(sK1,sK3)
    | ~ l1_struct_0(sK1)
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f148,f104])).

fof(f148,plain,
    ( r1_tsep_1(sK1,sK3)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK1)
    | ~ spl4_3 ),
    inference(resolution,[],[f147,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

fof(f147,plain,
    ( r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ spl4_3 ),
    inference(resolution,[],[f127,f133])).

fof(f133,plain,(
    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f132,f37])).

fof(f132,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ m1_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f90,f40])).

fof(f40,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f90,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2))
      | ~ m1_pre_topc(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f89,f35])).

fof(f35,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f89,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2))
      | ~ m1_pre_topc(X0,sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f86,f36])).

fof(f86,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2))
      | ~ m1_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f38,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X2)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
                  | ~ m1_pre_topc(X1,X2) )
                & ( m1_pre_topc(X1,X2)
                  | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f127,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK2))
        | r1_xboole_0(X0,u1_struct_0(sK3)) )
    | ~ spl4_3 ),
    inference(superposition,[],[f56,f123])).

fof(f123,plain,
    ( u1_struct_0(sK3) = k4_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ spl4_3 ),
    inference(resolution,[],[f119,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f119,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f118,f104])).

fof(f118,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ l1_struct_0(sK3)
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f117,f95])).

fof(f117,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK3)
    | ~ spl4_3 ),
    inference(resolution,[],[f113,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f113,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f112,f95])).

fof(f112,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ l1_struct_0(sK2)
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f110,f104])).

fof(f110,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | ~ spl4_3 ),
    inference(resolution,[],[f71,f50])).

fof(f71,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f153,plain,
    ( spl4_1
    | ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f152])).

fof(f152,plain,
    ( $false
    | spl4_1
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f151,f94])).

fof(f151,plain,
    ( ~ l1_struct_0(sK1)
    | spl4_1
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f150,f104])).

fof(f150,plain,
    ( ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK1)
    | spl4_1
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f148,f62])).

fof(f62,plain,
    ( ~ r1_tsep_1(sK1,sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl4_1
  <=> r1_tsep_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f76,plain,
    ( spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f41,f73,f69])).

fof(f41,plain,
    ( r1_tsep_1(sK3,sK2)
    | r1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f67,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f42,f64,f60])).

fof(f42,plain,
    ( ~ r1_tsep_1(sK3,sK1)
    | ~ r1_tsep_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:37:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (29794)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.48  % (29792)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.49  % (29808)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.49  % (29790)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.49  % (29789)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.49  % (29810)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.49  % (29812)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.50  % (29803)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.50  % (29798)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.50  % (29789)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f170,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f67,f76,f153,f161,f167])).
% 0.21/0.50  fof(f167,plain,(
% 0.21/0.50    spl4_3 | ~spl4_4),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f166])).
% 0.21/0.50  fof(f166,plain,(
% 0.21/0.50    $false | (spl4_3 | ~spl4_4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f165,f104])).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    l1_struct_0(sK3)),
% 0.21/0.50    inference(resolution,[],[f103,f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    l1_pre_topc(sK3)),
% 0.21/0.50    inference(subsumption_resolution,[],[f98,f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    l1_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ((((~r1_tsep_1(sK3,sK1) | ~r1_tsep_1(sK1,sK3)) & (r1_tsep_1(sK3,sK2) | r1_tsep_1(sK2,sK3)) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK3,sK0)) & m1_pre_topc(sK2,sK0)) & m1_pre_topc(sK1,sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f28,f27,f26,f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK0)) & m1_pre_topc(X2,sK0)) & m1_pre_topc(X1,sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ? [X1] : (? [X2] : (? [X3] : ((~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK0)) & m1_pre_topc(X2,sK0)) & m1_pre_topc(X1,sK0)) => (? [X2] : (? [X3] : ((~r1_tsep_1(X3,sK1) | ~r1_tsep_1(sK1,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(sK1,X2) & m1_pre_topc(X3,sK0)) & m1_pre_topc(X2,sK0)) & m1_pre_topc(sK1,sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ? [X2] : (? [X3] : ((~r1_tsep_1(X3,sK1) | ~r1_tsep_1(sK1,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(sK1,X2) & m1_pre_topc(X3,sK0)) & m1_pre_topc(X2,sK0)) => (? [X3] : ((~r1_tsep_1(X3,sK1) | ~r1_tsep_1(sK1,X3)) & (r1_tsep_1(X3,sK2) | r1_tsep_1(sK2,X3)) & m1_pre_topc(sK1,sK2) & m1_pre_topc(X3,sK0)) & m1_pre_topc(sK2,sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ? [X3] : ((~r1_tsep_1(X3,sK1) | ~r1_tsep_1(sK1,X3)) & (r1_tsep_1(X3,sK2) | r1_tsep_1(sK2,X3)) & m1_pre_topc(sK1,sK2) & m1_pre_topc(X3,sK0)) => ((~r1_tsep_1(sK3,sK1) | ~r1_tsep_1(sK1,sK3)) & (r1_tsep_1(sK3,sK2) | r1_tsep_1(sK2,sK3)) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK3,sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3))) & m1_pre_topc(X1,X2)) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => (m1_pre_topc(X1,X2) => ((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))))))))),
% 0.21/0.50    inference(pure_predicate_removal,[],[f11])).
% 0.21/0.50  fof(f11,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))))))))),
% 0.21/0.50    inference(negated_conjecture,[],[f10])).
% 0.21/0.50  fof(f10,conjecture,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tmap_1)).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    l1_pre_topc(sK3) | ~l1_pre_topc(sK0)),
% 0.21/0.50    inference(resolution,[],[f39,f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    m1_pre_topc(sK3,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f165,plain,(
% 0.21/0.50    ~l1_struct_0(sK3) | (spl4_3 | ~spl4_4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f164,f95])).
% 0.21/0.50  fof(f95,plain,(
% 0.21/0.50    l1_struct_0(sK2)),
% 0.21/0.50    inference(resolution,[],[f93,f45])).
% 0.21/0.50  fof(f93,plain,(
% 0.21/0.50    l1_pre_topc(sK2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f88,f36])).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    l1_pre_topc(sK2) | ~l1_pre_topc(sK0)),
% 0.21/0.50    inference(resolution,[],[f38,f46])).
% 0.21/0.50  % (29807)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.50  % (29791)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (29800)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    m1_pre_topc(sK2,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f164,plain,(
% 0.21/0.50    ~l1_struct_0(sK2) | ~l1_struct_0(sK3) | (spl4_3 | ~spl4_4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f162,f70])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ~r1_tsep_1(sK2,sK3) | spl4_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f69])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    spl4_3 <=> r1_tsep_1(sK2,sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    r1_tsep_1(sK2,sK3) | ~l1_struct_0(sK2) | ~l1_struct_0(sK3) | ~spl4_4),
% 0.21/0.50    inference(resolution,[],[f75,f50])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tsep_1(X0,X1) | r1_tsep_1(X1,X0) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    r1_tsep_1(sK3,sK2) | ~spl4_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f73])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    spl4_4 <=> r1_tsep_1(sK3,sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.50  fof(f161,plain,(
% 0.21/0.50    spl4_2 | ~spl4_3),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f160])).
% 0.21/0.50  fof(f160,plain,(
% 0.21/0.50    $false | (spl4_2 | ~spl4_3)),
% 0.21/0.50    inference(subsumption_resolution,[],[f159,f94])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    l1_struct_0(sK1)),
% 0.21/0.50    inference(resolution,[],[f85,f45])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    l1_pre_topc(sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f80,f36])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.21/0.50    inference(resolution,[],[f37,f46])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    m1_pre_topc(sK1,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f159,plain,(
% 0.21/0.50    ~l1_struct_0(sK1) | (spl4_2 | ~spl4_3)),
% 0.21/0.50    inference(subsumption_resolution,[],[f158,f104])).
% 0.21/0.50  fof(f158,plain,(
% 0.21/0.50    ~l1_struct_0(sK3) | ~l1_struct_0(sK1) | (spl4_2 | ~spl4_3)),
% 0.21/0.50    inference(subsumption_resolution,[],[f156,f66])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    ~r1_tsep_1(sK3,sK1) | spl4_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f64])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    spl4_2 <=> r1_tsep_1(sK3,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.50  fof(f156,plain,(
% 0.21/0.50    r1_tsep_1(sK3,sK1) | ~l1_struct_0(sK3) | ~l1_struct_0(sK1) | ~spl4_3),
% 0.21/0.50    inference(resolution,[],[f155,f50])).
% 0.21/0.50  fof(f155,plain,(
% 0.21/0.50    r1_tsep_1(sK1,sK3) | ~spl4_3),
% 0.21/0.50    inference(subsumption_resolution,[],[f154,f94])).
% 0.21/0.50  fof(f154,plain,(
% 0.21/0.50    r1_tsep_1(sK1,sK3) | ~l1_struct_0(sK1) | ~spl4_3),
% 0.21/0.50    inference(subsumption_resolution,[],[f148,f104])).
% 0.21/0.50  fof(f148,plain,(
% 0.21/0.50    r1_tsep_1(sK1,sK3) | ~l1_struct_0(sK3) | ~l1_struct_0(sK1) | ~spl4_3),
% 0.21/0.50    inference(resolution,[],[f147,f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) & (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).
% 0.21/0.50  fof(f147,plain,(
% 0.21/0.50    r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) | ~spl4_3),
% 0.21/0.50    inference(resolution,[],[f127,f133])).
% 0.21/0.50  fof(f133,plain,(
% 0.21/0.50    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))),
% 0.21/0.50    inference(subsumption_resolution,[],[f132,f37])).
% 0.21/0.50  fof(f132,plain,(
% 0.21/0.50    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) | ~m1_pre_topc(sK1,sK0)),
% 0.21/0.50    inference(resolution,[],[f90,f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    m1_pre_topc(sK1,sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_pre_topc(X0,sK2) | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) | ~m1_pre_topc(X0,sK0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f89,f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    v2_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_pre_topc(X0,sK2) | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) | ~m1_pre_topc(X0,sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f86,f36])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_pre_topc(X0,sK2) | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.50    inference(resolution,[],[f38,f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X2) | r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK2)) | r1_xboole_0(X0,u1_struct_0(sK3))) ) | ~spl4_3),
% 0.21/0.50    inference(superposition,[],[f56,f123])).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    u1_struct_0(sK3) = k4_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) | ~spl4_3),
% 0.21/0.50    inference(resolution,[],[f119,f54])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.50    inference(nnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.50  fof(f119,plain,(
% 0.21/0.50    r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) | ~spl4_3),
% 0.21/0.50    inference(subsumption_resolution,[],[f118,f104])).
% 0.21/0.50  fof(f118,plain,(
% 0.21/0.50    r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) | ~l1_struct_0(sK3) | ~spl4_3),
% 0.21/0.50    inference(subsumption_resolution,[],[f117,f95])).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) | ~l1_struct_0(sK2) | ~l1_struct_0(sK3) | ~spl4_3),
% 0.21/0.50    inference(resolution,[],[f113,f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tsep_1(X0,X1) | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f113,plain,(
% 0.21/0.50    r1_tsep_1(sK3,sK2) | ~spl4_3),
% 0.21/0.50    inference(subsumption_resolution,[],[f112,f95])).
% 0.21/0.50  fof(f112,plain,(
% 0.21/0.50    r1_tsep_1(sK3,sK2) | ~l1_struct_0(sK2) | ~spl4_3),
% 0.21/0.50    inference(subsumption_resolution,[],[f110,f104])).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    r1_tsep_1(sK3,sK2) | ~l1_struct_0(sK3) | ~l1_struct_0(sK2) | ~spl4_3),
% 0.21/0.50    inference(resolution,[],[f71,f50])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    r1_tsep_1(sK2,sK3) | ~spl4_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f69])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).
% 0.21/0.50  fof(f153,plain,(
% 0.21/0.50    spl4_1 | ~spl4_3),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f152])).
% 0.21/0.50  fof(f152,plain,(
% 0.21/0.50    $false | (spl4_1 | ~spl4_3)),
% 0.21/0.50    inference(subsumption_resolution,[],[f151,f94])).
% 0.21/0.50  fof(f151,plain,(
% 0.21/0.50    ~l1_struct_0(sK1) | (spl4_1 | ~spl4_3)),
% 0.21/0.50    inference(subsumption_resolution,[],[f150,f104])).
% 0.21/0.50  fof(f150,plain,(
% 0.21/0.50    ~l1_struct_0(sK3) | ~l1_struct_0(sK1) | (spl4_1 | ~spl4_3)),
% 0.21/0.50    inference(subsumption_resolution,[],[f148,f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ~r1_tsep_1(sK1,sK3) | spl4_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    spl4_1 <=> r1_tsep_1(sK1,sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    spl4_3 | spl4_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f41,f73,f69])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    r1_tsep_1(sK3,sK2) | r1_tsep_1(sK2,sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    ~spl4_1 | ~spl4_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f42,f64,f60])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ~r1_tsep_1(sK3,sK1) | ~r1_tsep_1(sK1,sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (29789)------------------------------
% 0.21/0.50  % (29789)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (29789)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (29789)Memory used [KB]: 10618
% 0.21/0.50  % (29789)Time elapsed: 0.100 s
% 0.21/0.50  % (29789)------------------------------
% 0.21/0.50  % (29789)------------------------------
% 0.21/0.50  % (29787)Success in time 0.148 s
%------------------------------------------------------------------------------
