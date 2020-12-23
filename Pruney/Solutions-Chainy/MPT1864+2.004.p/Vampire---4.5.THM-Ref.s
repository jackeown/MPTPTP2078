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
% DateTime   : Thu Dec  3 13:20:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 214 expanded)
%              Number of leaves         :   26 (  74 expanded)
%              Depth                    :   13
%              Number of atoms          :  286 ( 697 expanded)
%              Number of equality atoms :   32 ( 107 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f185,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f72,f77,f82,f88,f93,f124,f126,f161,f165,f172,f181,f184])).

% (29641)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f184,plain,
    ( ~ spl6_1
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_15
    | ~ spl6_16
    | spl6_18 ),
    inference(avatar_contradiction_clause,[],[f182])).

fof(f182,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_15
    | ~ spl6_16
    | spl6_18 ),
    inference(unit_resulting_resolution,[],[f66,f76,f92,f147,f151,f160,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK4(X0,X1,X2),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                            & v3_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).

fof(f160,plain,
    ( ~ v3_pre_topc(sK4(sK0,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),sK0)
    | spl6_18 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl6_18
  <=> v3_pre_topc(sK4(sK0,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f151,plain,
    ( m1_subset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl6_16
  <=> m1_subset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f147,plain,
    ( r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK1)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl6_15
  <=> r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f92,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl6_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f76,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl6_3
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f66,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl6_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f181,plain,
    ( ~ spl6_1
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_15
    | ~ spl6_16
    | spl6_17 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_15
    | ~ spl6_16
    | spl6_17 ),
    inference(unit_resulting_resolution,[],[f66,f76,f92,f147,f151,f156,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f156,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_17 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl6_17
  <=> m1_subset_1(sK4(sK0,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f172,plain,
    ( ~ spl6_11
    | spl6_16 ),
    inference(avatar_contradiction_clause,[],[f168])).

fof(f168,plain,
    ( $false
    | ~ spl6_11
    | spl6_16 ),
    inference(unit_resulting_resolution,[],[f123,f152,f57])).

% (29644)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f55])).

fof(f55,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f28,f54])).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f35,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f41,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f46,f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f47,f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f49,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f48,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f41,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f28,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(f152,plain,
    ( ~ m1_subset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_16 ),
    inference(avatar_component_clause,[],[f150])).

fof(f123,plain,
    ( r2_hidden(sK2,u1_struct_0(sK0))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl6_11
  <=> r2_hidden(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f165,plain,
    ( ~ spl6_2
    | spl6_15 ),
    inference(avatar_contradiction_clause,[],[f162])).

fof(f162,plain,
    ( $false
    | ~ spl6_2
    | spl6_15 ),
    inference(unit_resulting_resolution,[],[f71,f71,f148,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f44,f54])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X2)
      | r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f148,plain,
    ( ~ r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK1)
    | spl6_15 ),
    inference(avatar_component_clause,[],[f146])).

fof(f71,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl6_2
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f161,plain,
    ( ~ spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f144,f158,f154,f150,f146])).

fof(f144,plain,
    ( ~ v3_pre_topc(sK4(sK0,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),sK0)
    | ~ m1_subset_1(sK4(sK0,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK1) ),
    inference(equality_resolution,[],[f119])).

fof(f119,plain,(
    ! [X0] :
      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != X0
      | ~ v3_pre_topc(sK4(sK0,sK1,X0),sK0)
      | ~ m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,sK1) ) ),
    inference(global_subsumption,[],[f27,f26,f25,f118])).

fof(f118,plain,(
    ! [X0] :
      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != X0
      | ~ v3_pre_topc(sK4(sK0,sK1,X0),sK0)
      | ~ m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_tex_2(sK1,sK0) ) ),
    inference(superposition,[],[f56,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,sK4(X0,X1,X2)) = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f56,plain,(
    ! [X3] :
      ( k9_subset_1(u1_struct_0(sK0),sK1,X3) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(definition_unfolding,[],[f22,f55])).

fof(f22,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X3,sK0)
      | k9_subset_1(u1_struct_0(sK0),sK1,X3) != k1_tarski(sK2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tex_2(X1,X0)
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ~ ( ! [X3] :
                          ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                         => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2)
                              & v3_pre_topc(X3,X0) ) )
                      & r2_hidden(X2,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2)
                            & v3_pre_topc(X3,X0) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tex_2)).

fof(f25,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f26,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f27,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f126,plain,
    ( spl6_5
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(avatar_contradiction_clause,[],[f125])).

fof(f125,plain,
    ( $false
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f87,f92,f102,f61])).

fof(f61,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | sP5(X1) ) ),
    inference(cnf_transformation,[],[f61_D])).

fof(f61_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
          | ~ v1_xboole_0(X2) )
    <=> ~ sP5(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).

fof(f102,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl6_7
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f87,plain,
    ( ~ sP5(sK1)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl6_5
  <=> sP5(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f124,plain,
    ( spl6_7
    | spl6_11
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f95,f79,f121,f101])).

fof(f79,plain,
    ( spl6_4
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f95,plain,
    ( r2_hidden(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl6_4 ),
    inference(resolution,[],[f81,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f81,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f93,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f25,f90])).

fof(f88,plain,
    ( ~ spl6_5
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f83,f69,f85])).

fof(f83,plain,
    ( ~ sP5(sK1)
    | ~ spl6_2 ),
    inference(resolution,[],[f71,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP5(X1) ) ),
    inference(general_splitting,[],[f45,f61_D])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f82,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f23,f79])).

fof(f23,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f77,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f26,f74])).

fof(f72,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f24,f69])).

fof(f24,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f67,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f27,f64])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:04:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (29652)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.50  % (29663)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.50  % (29655)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.51  % (29647)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % (29663)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (29645)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f185,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f67,f72,f77,f82,f88,f93,f124,f126,f161,f165,f172,f181,f184])).
% 0.22/0.51  % (29641)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.51  fof(f184,plain,(
% 0.22/0.51    ~spl6_1 | ~spl6_3 | ~spl6_6 | ~spl6_15 | ~spl6_16 | spl6_18),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f182])).
% 0.22/0.51  fof(f182,plain,(
% 0.22/0.51    $false | (~spl6_1 | ~spl6_3 | ~spl6_6 | ~spl6_15 | ~spl6_16 | spl6_18)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f66,f76,f92,f147,f151,f160,f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (v3_pre_topc(sK4(X0,X1,X2),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,X1) | ~l1_pre_topc(X0) | ~v2_tex_2(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).
% 0.22/0.51  fof(f160,plain,(
% 0.22/0.51    ~v3_pre_topc(sK4(sK0,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),sK0) | spl6_18),
% 0.22/0.51    inference(avatar_component_clause,[],[f158])).
% 0.22/0.51  fof(f158,plain,(
% 0.22/0.51    spl6_18 <=> v3_pre_topc(sK4(sK0,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.22/0.51  fof(f151,plain,(
% 0.22/0.51    m1_subset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_16),
% 0.22/0.51    inference(avatar_component_clause,[],[f150])).
% 0.22/0.51  fof(f150,plain,(
% 0.22/0.51    spl6_16 <=> m1_subset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.22/0.51  fof(f147,plain,(
% 0.22/0.51    r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK1) | ~spl6_15),
% 0.22/0.51    inference(avatar_component_clause,[],[f146])).
% 0.22/0.51  fof(f146,plain,(
% 0.22/0.51    spl6_15 <=> r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.22/0.51  fof(f92,plain,(
% 0.22/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_6),
% 0.22/0.51    inference(avatar_component_clause,[],[f90])).
% 0.22/0.51  fof(f90,plain,(
% 0.22/0.51    spl6_6 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    v2_tex_2(sK1,sK0) | ~spl6_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f74])).
% 0.22/0.51  fof(f74,plain,(
% 0.22/0.51    spl6_3 <=> v2_tex_2(sK1,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    l1_pre_topc(sK0) | ~spl6_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f64])).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    spl6_1 <=> l1_pre_topc(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.51  fof(f181,plain,(
% 0.22/0.51    ~spl6_1 | ~spl6_3 | ~spl6_6 | ~spl6_15 | ~spl6_16 | spl6_17),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f177])).
% 0.22/0.51  fof(f177,plain,(
% 0.22/0.51    $false | (~spl6_1 | ~spl6_3 | ~spl6_6 | ~spl6_15 | ~spl6_16 | spl6_17)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f66,f76,f92,f147,f151,f156,f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,X1) | ~l1_pre_topc(X0) | ~v2_tex_2(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f156,plain,(
% 0.22/0.51    ~m1_subset_1(sK4(sK0,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | spl6_17),
% 0.22/0.51    inference(avatar_component_clause,[],[f154])).
% 0.22/0.51  fof(f154,plain,(
% 0.22/0.51    spl6_17 <=> m1_subset_1(sK4(sK0,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.22/0.51  fof(f172,plain,(
% 0.22/0.51    ~spl6_11 | spl6_16),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f168])).
% 0.22/0.51  fof(f168,plain,(
% 0.22/0.51    $false | (~spl6_11 | spl6_16)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f123,f152,f57])).
% 0.22/0.51  % (29644)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    ( ! [X0,X1] : (m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f40,f55])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f28,f54])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f35,f53])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f41,f52])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f46,f51])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f47,f50])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f48,f49])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,axiom,(
% 0.22/0.51    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).
% 0.22/0.51  fof(f152,plain,(
% 0.22/0.51    ~m1_subset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl6_16),
% 0.22/0.51    inference(avatar_component_clause,[],[f150])).
% 0.22/0.51  fof(f123,plain,(
% 0.22/0.51    r2_hidden(sK2,u1_struct_0(sK0)) | ~spl6_11),
% 0.22/0.51    inference(avatar_component_clause,[],[f121])).
% 0.22/0.51  fof(f121,plain,(
% 0.22/0.51    spl6_11 <=> r2_hidden(sK2,u1_struct_0(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.22/0.51  fof(f165,plain,(
% 0.22/0.51    ~spl6_2 | spl6_15),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f162])).
% 0.22/0.51  fof(f162,plain,(
% 0.22/0.51    $false | (~spl6_2 | spl6_15)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f71,f71,f148,f58])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f44,f54])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | r1_tarski(k2_tarski(X0,X1),X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.22/0.51  fof(f148,plain,(
% 0.22/0.51    ~r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK1) | spl6_15),
% 0.22/0.51    inference(avatar_component_clause,[],[f146])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    r2_hidden(sK2,sK1) | ~spl6_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f69])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    spl6_2 <=> r2_hidden(sK2,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.51  fof(f161,plain,(
% 0.22/0.51    ~spl6_15 | ~spl6_16 | ~spl6_17 | ~spl6_18),
% 0.22/0.51    inference(avatar_split_clause,[],[f144,f158,f154,f150,f146])).
% 0.22/0.51  fof(f144,plain,(
% 0.22/0.51    ~v3_pre_topc(sK4(sK0,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),sK0) | ~m1_subset_1(sK4(sK0,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK1)),
% 0.22/0.51    inference(equality_resolution,[],[f119])).
% 0.22/0.51  fof(f119,plain,(
% 0.22/0.51    ( ! [X0] : (k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != X0 | ~v3_pre_topc(sK4(sK0,sK1,X0),sK0) | ~m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1)) )),
% 0.22/0.51    inference(global_subsumption,[],[f27,f26,f25,f118])).
% 0.22/0.51  fof(f118,plain,(
% 0.22/0.51    ( ! [X0] : (k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != X0 | ~v3_pre_topc(sK4(sK0,sK1,X0),sK0) | ~m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | ~l1_pre_topc(sK0) | ~v2_tex_2(sK1,sK0)) )),
% 0.22/0.51    inference(superposition,[],[f56,f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k9_subset_1(u1_struct_0(X0),X1,sK4(X0,X1,X2)) = X2 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,X1) | ~l1_pre_topc(X0) | ~v2_tex_2(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    ( ! [X3] : (k9_subset_1(u1_struct_0(sK0),sK1,X3) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.51    inference(definition_unfolding,[],[f22,f55])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X3,sK0) | k9_subset_1(u1_struct_0(sK0),sK1,X3) != k1_tarski(sK2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : ((? [X2] : ((! [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v3_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,negated_conjecture,(
% 0.22/0.51    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & v3_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 0.22/0.51    inference(negated_conjecture,[],[f13])).
% 0.22/0.51  fof(f13,conjecture,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & v3_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tex_2)).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    v2_tex_2(sK1,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    l1_pre_topc(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f126,plain,(
% 0.22/0.51    spl6_5 | ~spl6_6 | ~spl6_7),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f125])).
% 0.22/0.51  fof(f125,plain,(
% 0.22/0.51    $false | (spl6_5 | ~spl6_6 | ~spl6_7)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f87,f92,f102,f61])).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | sP5(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f61_D])).
% 0.22/0.51  fof(f61_D,plain,(
% 0.22/0.51    ( ! [X1] : (( ! [X2] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) ) <=> ~sP5(X1)) )),
% 0.22/0.51    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).
% 0.22/0.51  fof(f102,plain,(
% 0.22/0.51    v1_xboole_0(u1_struct_0(sK0)) | ~spl6_7),
% 0.22/0.51    inference(avatar_component_clause,[],[f101])).
% 0.22/0.51  fof(f101,plain,(
% 0.22/0.51    spl6_7 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.51  fof(f87,plain,(
% 0.22/0.51    ~sP5(sK1) | spl6_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f85])).
% 0.22/0.51  fof(f85,plain,(
% 0.22/0.51    spl6_5 <=> sP5(sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.51  fof(f124,plain,(
% 0.22/0.51    spl6_7 | spl6_11 | ~spl6_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f95,f79,f121,f101])).
% 0.22/0.51  fof(f79,plain,(
% 0.22/0.51    spl6_4 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.51  fof(f95,plain,(
% 0.22/0.51    r2_hidden(sK2,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | ~spl6_4),
% 0.22/0.51    inference(resolution,[],[f81,f39])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    m1_subset_1(sK2,u1_struct_0(sK0)) | ~spl6_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f79])).
% 0.22/0.51  fof(f93,plain,(
% 0.22/0.51    spl6_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f25,f90])).
% 0.22/0.51  fof(f88,plain,(
% 0.22/0.51    ~spl6_5 | ~spl6_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f83,f69,f85])).
% 0.22/0.51  fof(f83,plain,(
% 0.22/0.51    ~sP5(sK1) | ~spl6_2),
% 0.22/0.51    inference(resolution,[],[f71,f62])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~sP5(X1)) )),
% 0.22/0.51    inference(general_splitting,[],[f45,f61_D])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.22/0.51  fof(f82,plain,(
% 0.22/0.51    spl6_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f23,f79])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    spl6_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f26,f74])).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    spl6_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f24,f69])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    r2_hidden(sK2,sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    spl6_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f27,f64])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (29663)------------------------------
% 0.22/0.51  % (29663)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (29663)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (29663)Memory used [KB]: 10746
% 0.22/0.51  % (29663)Time elapsed: 0.054 s
% 0.22/0.51  % (29663)------------------------------
% 0.22/0.51  % (29663)------------------------------
% 0.22/0.52  % (29651)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.52  % (29646)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (29639)Success in time 0.158 s
%------------------------------------------------------------------------------
