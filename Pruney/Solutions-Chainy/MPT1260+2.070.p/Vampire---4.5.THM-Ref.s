%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:44 EST 2020

% Result     : Theorem 2.21s
% Output     : Refutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 359 expanded)
%              Number of leaves         :   26 ( 109 expanded)
%              Depth                    :   16
%              Number of atoms          :  413 (1661 expanded)
%              Number of equality atoms :   72 ( 422 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1560,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f83,f201,f252,f285,f297,f1449,f1512,f1524,f1546,f1559])).

fof(f1559,plain,
    ( spl2_2
    | ~ spl2_8 ),
    inference(avatar_contradiction_clause,[],[f1558])).

fof(f1558,plain,
    ( $false
    | spl2_2
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f1557,f48])).

fof(f48,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f42,f41])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | ~ v3_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | ~ v3_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | ~ v3_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | v3_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | ~ v3_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | v3_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

fof(f1557,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_2
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f1556,f49])).

fof(f49,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f1556,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_2
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f1551,f81])).

fof(f81,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl2_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f1551,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_8 ),
    inference(superposition,[],[f55,f173])).

fof(f173,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl2_8
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f1546,plain,
    ( spl2_8
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f1545,f167,f171])).

fof(f167,plain,
    ( spl2_7
  <=> r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f1545,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f1544,f164])).

fof(f164,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f163,f48])).

fof(f163,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f53,f49])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f1544,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl2_7 ),
    inference(resolution,[],[f168,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f168,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f167])).

fof(f1524,plain,
    ( spl2_7
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f1523,f75,f167])).

fof(f75,plain,
    ( spl2_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f1523,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f375,f72])).

fof(f72,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f375,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK1) ),
    inference(resolution,[],[f357,f49])).

fof(f357,plain,(
    ! [X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X13,sK0)
      | r1_tarski(X13,k1_tops_1(sK0,sK1))
      | ~ r1_tarski(X13,sK1) ) ),
    inference(subsumption_resolution,[],[f354,f48])).

fof(f354,plain,(
    ! [X13] :
      ( ~ r1_tarski(X13,sK1)
      | ~ v3_pre_topc(X13,sK0)
      | r1_tarski(X13,k1_tops_1(sK0,sK1))
      | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f56,f49])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

fof(f1512,plain,
    ( spl2_1
    | ~ spl2_8 ),
    inference(avatar_contradiction_clause,[],[f1511])).

fof(f1511,plain,
    ( $false
    | spl2_1
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f1510,f47])).

fof(f47,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f1510,plain,
    ( ~ v2_pre_topc(sK0)
    | spl2_1
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f1509,f48])).

fof(f1509,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl2_1
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f1508,f49])).

fof(f1508,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl2_1
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f1502,f77])).

fof(f77,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f1502,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl2_8 ),
    inference(superposition,[],[f62,f173])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f1449,plain,
    ( spl2_8
    | ~ spl2_10
    | ~ spl2_13
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f1448,f282,f278,f197,f171])).

fof(f197,plain,
    ( spl2_10
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f278,plain,
    ( spl2_13
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f282,plain,
    ( spl2_14
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f1448,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl2_10
    | ~ spl2_13
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f1447,f48])).

fof(f1447,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_10
    | ~ spl2_13
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f1435,f49])).

fof(f1435,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_10
    | ~ spl2_13
    | ~ spl2_14 ),
    inference(superposition,[],[f301,f1374])).

fof(f1374,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_10
    | ~ spl2_13
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f1360,f448])).

fof(f448,plain,
    ( sK1 = k4_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_10
    | ~ spl2_13
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f443,f284])).

fof(f284,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f282])).

fof(f443,plain,
    ( sK1 = k4_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_10
    | ~ spl2_13 ),
    inference(superposition,[],[f440,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f440,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_10
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f431,f279])).

fof(f279,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f278])).

fof(f431,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_10 ),
    inference(superposition,[],[f127,f199])).

fof(f199,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f197])).

fof(f127,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f61,f60])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f1360,plain,
    ( k4_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_10
    | ~ spl2_13
    | ~ spl2_14 ),
    inference(superposition,[],[f454,f57])).

fof(f57,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f454,plain,
    ( ! [X1] : k4_xboole_0(k2_pre_topc(sK0,sK1),k2_xboole_0(k2_tops_1(sK0,sK1),X1)) = k4_xboole_0(sK1,X1)
    | ~ spl2_10
    | ~ spl2_13
    | ~ spl2_14 ),
    inference(superposition,[],[f69,f448])).

fof(f69,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f301,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f300])).

fof(f300,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f70,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f297,plain,(
    spl2_13 ),
    inference(avatar_contradiction_clause,[],[f296])).

fof(f296,plain,
    ( $false
    | spl2_13 ),
    inference(subsumption_resolution,[],[f295,f140])).

fof(f140,plain,(
    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f139,f48])).

fof(f139,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f52,f49])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f295,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | spl2_13 ),
    inference(resolution,[],[f280,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f280,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | spl2_13 ),
    inference(avatar_component_clause,[],[f278])).

fof(f285,plain,
    ( ~ spl2_13
    | spl2_14
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f274,f197,f282,f278])).

fof(f274,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_10 ),
    inference(superposition,[],[f114,f199])).

fof(f114,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k4_xboole_0(X2,X3),k1_zfmisc_1(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ) ),
    inference(duplicate_literal_removal,[],[f113])).

fof(f113,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k4_xboole_0(X2,X3),k1_zfmisc_1(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ) ),
    inference(superposition,[],[f59,f60])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f252,plain,(
    spl2_9 ),
    inference(avatar_contradiction_clause,[],[f251])).

fof(f251,plain,
    ( $false
    | spl2_9 ),
    inference(subsumption_resolution,[],[f250,f48])).

fof(f250,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_9 ),
    inference(subsumption_resolution,[],[f244,f49])).

fof(f244,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_9 ),
    inference(resolution,[],[f63,f195])).

fof(f195,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_9 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl2_9
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f201,plain,
    ( ~ spl2_9
    | spl2_10
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f191,f79,f197,f193])).

fof(f191,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(superposition,[],[f80,f70])).

fof(f80,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f83,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f50,f79,f75])).

fof(f50,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f82,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f51,f79,f75])).

fof(f51,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:41:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.45  % (20366)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.49  % (20360)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.49  % (20388)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.50  % (20363)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.50  % (20375)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (20367)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.50  % (20369)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.50  % (20364)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.50  % (20387)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.51  % (20381)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.51  % (20385)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.51  % (20379)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.51  % (20371)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.52  % (20376)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.52  % (20372)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  % (20386)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.52  % (20377)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.52  % (20380)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.52  % (20365)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.53  % (20383)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.53  % (20370)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.53  % (20368)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.53  % (20382)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.53  % (20361)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (20378)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.54  % (20374)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 2.21/0.67  % (20365)Refutation found. Thanks to Tanya!
% 2.21/0.67  % SZS status Theorem for theBenchmark
% 2.21/0.67  % SZS output start Proof for theBenchmark
% 2.21/0.67  fof(f1560,plain,(
% 2.21/0.67    $false),
% 2.21/0.67    inference(avatar_sat_refutation,[],[f82,f83,f201,f252,f285,f297,f1449,f1512,f1524,f1546,f1559])).
% 2.21/0.67  fof(f1559,plain,(
% 2.21/0.67    spl2_2 | ~spl2_8),
% 2.21/0.67    inference(avatar_contradiction_clause,[],[f1558])).
% 2.21/0.67  fof(f1558,plain,(
% 2.21/0.67    $false | (spl2_2 | ~spl2_8)),
% 2.21/0.67    inference(subsumption_resolution,[],[f1557,f48])).
% 2.21/0.67  fof(f48,plain,(
% 2.21/0.67    l1_pre_topc(sK0)),
% 2.21/0.67    inference(cnf_transformation,[],[f43])).
% 2.21/0.67  fof(f43,plain,(
% 2.21/0.67    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.21/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f42,f41])).
% 2.21/0.67  fof(f41,plain,(
% 2.21/0.67    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.21/0.67    introduced(choice_axiom,[])).
% 2.21/0.67  fof(f42,plain,(
% 2.21/0.67    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.21/0.67    introduced(choice_axiom,[])).
% 2.21/0.67  fof(f40,plain,(
% 2.21/0.67    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.21/0.67    inference(flattening,[],[f39])).
% 2.21/0.67  fof(f39,plain,(
% 2.21/0.67    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.21/0.67    inference(nnf_transformation,[],[f22])).
% 2.21/0.67  fof(f22,plain,(
% 2.21/0.67    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.21/0.67    inference(flattening,[],[f21])).
% 2.21/0.67  fof(f21,plain,(
% 2.21/0.67    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.21/0.67    inference(ennf_transformation,[],[f19])).
% 2.21/0.67  fof(f19,negated_conjecture,(
% 2.21/0.67    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 2.21/0.67    inference(negated_conjecture,[],[f18])).
% 2.21/0.67  fof(f18,conjecture,(
% 2.21/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 2.21/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).
% 2.21/0.67  fof(f1557,plain,(
% 2.21/0.67    ~l1_pre_topc(sK0) | (spl2_2 | ~spl2_8)),
% 2.21/0.67    inference(subsumption_resolution,[],[f1556,f49])).
% 2.21/0.67  fof(f49,plain,(
% 2.21/0.67    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.21/0.67    inference(cnf_transformation,[],[f43])).
% 2.21/0.67  fof(f1556,plain,(
% 2.21/0.67    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl2_2 | ~spl2_8)),
% 2.21/0.67    inference(subsumption_resolution,[],[f1551,f81])).
% 2.21/0.67  fof(f81,plain,(
% 2.21/0.67    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | spl2_2),
% 2.21/0.67    inference(avatar_component_clause,[],[f79])).
% 2.21/0.67  fof(f79,plain,(
% 2.21/0.67    spl2_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 2.21/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 2.21/0.67  fof(f1551,plain,(
% 2.21/0.67    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_8),
% 2.21/0.67    inference(superposition,[],[f55,f173])).
% 2.21/0.67  fof(f173,plain,(
% 2.21/0.67    sK1 = k1_tops_1(sK0,sK1) | ~spl2_8),
% 2.21/0.67    inference(avatar_component_clause,[],[f171])).
% 2.21/0.67  fof(f171,plain,(
% 2.21/0.67    spl2_8 <=> sK1 = k1_tops_1(sK0,sK1)),
% 2.21/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 2.21/0.67  fof(f55,plain,(
% 2.21/0.67    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.21/0.67    inference(cnf_transformation,[],[f26])).
% 2.21/0.67  fof(f26,plain,(
% 2.21/0.67    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.21/0.67    inference(ennf_transformation,[],[f14])).
% 2.21/0.67  fof(f14,axiom,(
% 2.21/0.67    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 2.21/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 2.21/0.67  fof(f1546,plain,(
% 2.21/0.67    spl2_8 | ~spl2_7),
% 2.21/0.67    inference(avatar_split_clause,[],[f1545,f167,f171])).
% 2.21/0.67  fof(f167,plain,(
% 2.21/0.67    spl2_7 <=> r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 2.21/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 2.21/0.67  fof(f1545,plain,(
% 2.21/0.67    sK1 = k1_tops_1(sK0,sK1) | ~spl2_7),
% 2.21/0.67    inference(subsumption_resolution,[],[f1544,f164])).
% 2.21/0.67  fof(f164,plain,(
% 2.21/0.67    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 2.21/0.67    inference(subsumption_resolution,[],[f163,f48])).
% 2.21/0.67  fof(f163,plain,(
% 2.21/0.67    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0)),
% 2.21/0.67    inference(resolution,[],[f53,f49])).
% 2.21/0.67  fof(f53,plain,(
% 2.21/0.67    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 2.21/0.67    inference(cnf_transformation,[],[f24])).
% 2.21/0.67  fof(f24,plain,(
% 2.21/0.67    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.21/0.67    inference(ennf_transformation,[],[f15])).
% 2.21/0.67  fof(f15,axiom,(
% 2.21/0.67    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 2.21/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 2.21/0.67  fof(f1544,plain,(
% 2.21/0.67    sK1 = k1_tops_1(sK0,sK1) | ~r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl2_7),
% 2.21/0.67    inference(resolution,[],[f168,f66])).
% 2.21/0.67  fof(f66,plain,(
% 2.21/0.67    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.21/0.67    inference(cnf_transformation,[],[f45])).
% 2.21/0.67  fof(f45,plain,(
% 2.21/0.67    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.21/0.67    inference(flattening,[],[f44])).
% 2.21/0.67  fof(f44,plain,(
% 2.21/0.67    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.21/0.67    inference(nnf_transformation,[],[f2])).
% 2.21/0.67  fof(f2,axiom,(
% 2.21/0.67    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.21/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.21/0.67  fof(f168,plain,(
% 2.21/0.67    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~spl2_7),
% 2.21/0.67    inference(avatar_component_clause,[],[f167])).
% 2.21/0.67  fof(f1524,plain,(
% 2.21/0.67    spl2_7 | ~spl2_1),
% 2.21/0.67    inference(avatar_split_clause,[],[f1523,f75,f167])).
% 2.21/0.67  fof(f75,plain,(
% 2.21/0.67    spl2_1 <=> v3_pre_topc(sK1,sK0)),
% 2.21/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 2.21/0.67  fof(f1523,plain,(
% 2.21/0.67    ~v3_pre_topc(sK1,sK0) | r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 2.21/0.67    inference(subsumption_resolution,[],[f375,f72])).
% 2.21/0.67  fof(f72,plain,(
% 2.21/0.67    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.21/0.67    inference(equality_resolution,[],[f65])).
% 2.21/0.67  fof(f65,plain,(
% 2.21/0.67    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.21/0.67    inference(cnf_transformation,[],[f45])).
% 2.21/0.67  fof(f375,plain,(
% 2.21/0.67    ~v3_pre_topc(sK1,sK0) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~r1_tarski(sK1,sK1)),
% 2.21/0.67    inference(resolution,[],[f357,f49])).
% 2.21/0.67  fof(f357,plain,(
% 2.21/0.67    ( ! [X13] : (~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X13,sK0) | r1_tarski(X13,k1_tops_1(sK0,sK1)) | ~r1_tarski(X13,sK1)) )),
% 2.21/0.67    inference(subsumption_resolution,[],[f354,f48])).
% 2.21/0.67  fof(f354,plain,(
% 2.21/0.67    ( ! [X13] : (~r1_tarski(X13,sK1) | ~v3_pre_topc(X13,sK0) | r1_tarski(X13,k1_tops_1(sK0,sK1)) | ~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 2.21/0.67    inference(resolution,[],[f56,f49])).
% 2.21/0.67  fof(f56,plain,(
% 2.21/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.21/0.67    inference(cnf_transformation,[],[f28])).
% 2.21/0.67  fof(f28,plain,(
% 2.21/0.67    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.21/0.67    inference(flattening,[],[f27])).
% 2.21/0.67  fof(f27,plain,(
% 2.21/0.67    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.21/0.67    inference(ennf_transformation,[],[f16])).
% 2.21/0.67  fof(f16,axiom,(
% 2.21/0.67    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 2.21/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).
% 2.21/0.67  fof(f1512,plain,(
% 2.21/0.67    spl2_1 | ~spl2_8),
% 2.21/0.67    inference(avatar_contradiction_clause,[],[f1511])).
% 2.21/0.67  fof(f1511,plain,(
% 2.21/0.67    $false | (spl2_1 | ~spl2_8)),
% 2.21/0.67    inference(subsumption_resolution,[],[f1510,f47])).
% 2.21/0.67  fof(f47,plain,(
% 2.21/0.67    v2_pre_topc(sK0)),
% 2.21/0.67    inference(cnf_transformation,[],[f43])).
% 2.21/0.67  fof(f1510,plain,(
% 2.21/0.67    ~v2_pre_topc(sK0) | (spl2_1 | ~spl2_8)),
% 2.21/0.67    inference(subsumption_resolution,[],[f1509,f48])).
% 2.21/0.67  fof(f1509,plain,(
% 2.21/0.67    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl2_1 | ~spl2_8)),
% 2.21/0.67    inference(subsumption_resolution,[],[f1508,f49])).
% 2.21/0.67  fof(f1508,plain,(
% 2.21/0.67    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl2_1 | ~spl2_8)),
% 2.21/0.67    inference(subsumption_resolution,[],[f1502,f77])).
% 2.21/0.67  fof(f77,plain,(
% 2.21/0.67    ~v3_pre_topc(sK1,sK0) | spl2_1),
% 2.21/0.67    inference(avatar_component_clause,[],[f75])).
% 2.21/0.67  fof(f1502,plain,(
% 2.21/0.67    v3_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl2_8),
% 2.21/0.67    inference(superposition,[],[f62,f173])).
% 2.21/0.67  fof(f62,plain,(
% 2.21/0.67    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.21/0.67    inference(cnf_transformation,[],[f33])).
% 2.21/0.67  fof(f33,plain,(
% 2.21/0.67    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.21/0.67    inference(flattening,[],[f32])).
% 2.21/0.67  fof(f32,plain,(
% 2.21/0.67    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.21/0.67    inference(ennf_transformation,[],[f13])).
% 2.21/0.67  fof(f13,axiom,(
% 2.21/0.67    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 2.21/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 2.21/0.67  fof(f1449,plain,(
% 2.21/0.67    spl2_8 | ~spl2_10 | ~spl2_13 | ~spl2_14),
% 2.21/0.67    inference(avatar_split_clause,[],[f1448,f282,f278,f197,f171])).
% 2.21/0.67  fof(f197,plain,(
% 2.21/0.67    spl2_10 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 2.21/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 2.21/0.67  fof(f278,plain,(
% 2.21/0.67    spl2_13 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 2.21/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 2.21/0.67  fof(f282,plain,(
% 2.21/0.67    spl2_14 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 2.21/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 2.21/0.67  fof(f1448,plain,(
% 2.21/0.67    sK1 = k1_tops_1(sK0,sK1) | (~spl2_10 | ~spl2_13 | ~spl2_14)),
% 2.21/0.67    inference(subsumption_resolution,[],[f1447,f48])).
% 2.21/0.67  fof(f1447,plain,(
% 2.21/0.67    sK1 = k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0) | (~spl2_10 | ~spl2_13 | ~spl2_14)),
% 2.21/0.67    inference(subsumption_resolution,[],[f1435,f49])).
% 2.21/0.67  fof(f1435,plain,(
% 2.21/0.67    sK1 = k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl2_10 | ~spl2_13 | ~spl2_14)),
% 2.21/0.67    inference(superposition,[],[f301,f1374])).
% 2.21/0.67  fof(f1374,plain,(
% 2.21/0.67    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_10 | ~spl2_13 | ~spl2_14)),
% 2.21/0.67    inference(forward_demodulation,[],[f1360,f448])).
% 2.21/0.67  fof(f448,plain,(
% 2.21/0.67    sK1 = k4_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | (~spl2_10 | ~spl2_13 | ~spl2_14)),
% 2.21/0.67    inference(subsumption_resolution,[],[f443,f284])).
% 2.21/0.67  fof(f284,plain,(
% 2.21/0.67    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl2_14),
% 2.21/0.67    inference(avatar_component_clause,[],[f282])).
% 2.21/0.67  fof(f443,plain,(
% 2.21/0.67    sK1 = k4_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | (~spl2_10 | ~spl2_13)),
% 2.21/0.67    inference(superposition,[],[f440,f60])).
% 2.21/0.67  fof(f60,plain,(
% 2.21/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.21/0.67    inference(cnf_transformation,[],[f30])).
% 2.21/0.67  fof(f30,plain,(
% 2.21/0.67    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.21/0.67    inference(ennf_transformation,[],[f6])).
% 2.21/0.67  fof(f6,axiom,(
% 2.21/0.67    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.21/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 2.21/0.67  fof(f440,plain,(
% 2.21/0.67    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | (~spl2_10 | ~spl2_13)),
% 2.21/0.67    inference(subsumption_resolution,[],[f431,f279])).
% 2.21/0.67  fof(f279,plain,(
% 2.21/0.67    m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl2_13),
% 2.21/0.67    inference(avatar_component_clause,[],[f278])).
% 2.21/0.67  fof(f431,plain,(
% 2.21/0.67    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl2_10),
% 2.21/0.67    inference(superposition,[],[f127,f199])).
% 2.21/0.67  fof(f199,plain,(
% 2.21/0.67    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~spl2_10),
% 2.21/0.67    inference(avatar_component_clause,[],[f197])).
% 2.21/0.67  fof(f127,plain,(
% 2.21/0.67    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.21/0.67    inference(duplicate_literal_removal,[],[f122])).
% 2.21/0.67  fof(f122,plain,(
% 2.21/0.67    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.21/0.67    inference(superposition,[],[f61,f60])).
% 2.21/0.67  fof(f61,plain,(
% 2.21/0.67    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.21/0.67    inference(cnf_transformation,[],[f31])).
% 2.21/0.67  fof(f31,plain,(
% 2.21/0.67    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.21/0.67    inference(ennf_transformation,[],[f8])).
% 2.21/0.67  fof(f8,axiom,(
% 2.21/0.67    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.21/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 2.21/0.67  fof(f1360,plain,(
% 2.21/0.67    k4_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_10 | ~spl2_13 | ~spl2_14)),
% 2.21/0.67    inference(superposition,[],[f454,f57])).
% 2.21/0.67  fof(f57,plain,(
% 2.21/0.67    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.21/0.67    inference(cnf_transformation,[],[f20])).
% 2.21/0.67  fof(f20,plain,(
% 2.21/0.67    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 2.21/0.67    inference(rectify,[],[f1])).
% 2.21/0.67  fof(f1,axiom,(
% 2.21/0.67    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 2.21/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 2.21/0.67  fof(f454,plain,(
% 2.21/0.67    ( ! [X1] : (k4_xboole_0(k2_pre_topc(sK0,sK1),k2_xboole_0(k2_tops_1(sK0,sK1),X1)) = k4_xboole_0(sK1,X1)) ) | (~spl2_10 | ~spl2_13 | ~spl2_14)),
% 2.21/0.67    inference(superposition,[],[f69,f448])).
% 2.21/0.67  fof(f69,plain,(
% 2.21/0.67    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.21/0.67    inference(cnf_transformation,[],[f5])).
% 2.21/0.67  fof(f5,axiom,(
% 2.21/0.67    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.21/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.21/0.67  fof(f301,plain,(
% 2.21/0.67    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.21/0.67    inference(duplicate_literal_removal,[],[f300])).
% 2.21/0.67  fof(f300,plain,(
% 2.21/0.67    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.21/0.67    inference(superposition,[],[f70,f54])).
% 2.21/0.67  fof(f54,plain,(
% 2.21/0.67    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.21/0.67    inference(cnf_transformation,[],[f25])).
% 2.21/0.67  fof(f25,plain,(
% 2.21/0.67    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.21/0.67    inference(ennf_transformation,[],[f17])).
% 2.21/0.67  fof(f17,axiom,(
% 2.21/0.67    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.21/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 2.21/0.67  fof(f70,plain,(
% 2.21/0.67    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.21/0.67    inference(cnf_transformation,[],[f36])).
% 2.21/0.67  fof(f36,plain,(
% 2.21/0.67    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.21/0.67    inference(ennf_transformation,[],[f9])).
% 2.21/0.67  fof(f9,axiom,(
% 2.21/0.67    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.21/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.21/0.67  fof(f297,plain,(
% 2.21/0.67    spl2_13),
% 2.21/0.67    inference(avatar_contradiction_clause,[],[f296])).
% 2.21/0.67  fof(f296,plain,(
% 2.21/0.67    $false | spl2_13),
% 2.21/0.67    inference(subsumption_resolution,[],[f295,f140])).
% 2.21/0.67  fof(f140,plain,(
% 2.21/0.67    r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 2.21/0.67    inference(subsumption_resolution,[],[f139,f48])).
% 2.21/0.67  fof(f139,plain,(
% 2.21/0.67    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 2.21/0.67    inference(resolution,[],[f52,f49])).
% 2.21/0.67  fof(f52,plain,(
% 2.21/0.67    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k2_pre_topc(X0,X1)) | ~l1_pre_topc(X0)) )),
% 2.21/0.67    inference(cnf_transformation,[],[f23])).
% 2.21/0.67  fof(f23,plain,(
% 2.21/0.67    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.21/0.67    inference(ennf_transformation,[],[f12])).
% 2.21/0.67  fof(f12,axiom,(
% 2.21/0.67    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 2.21/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).
% 2.21/0.67  fof(f295,plain,(
% 2.21/0.67    ~r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | spl2_13),
% 2.21/0.67    inference(resolution,[],[f280,f68])).
% 2.21/0.67  fof(f68,plain,(
% 2.21/0.67    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.21/0.67    inference(cnf_transformation,[],[f46])).
% 2.21/0.67  fof(f46,plain,(
% 2.21/0.67    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.21/0.67    inference(nnf_transformation,[],[f10])).
% 2.21/0.67  fof(f10,axiom,(
% 2.21/0.67    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.21/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.21/0.67  fof(f280,plain,(
% 2.21/0.67    ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | spl2_13),
% 2.21/0.67    inference(avatar_component_clause,[],[f278])).
% 2.21/0.67  fof(f285,plain,(
% 2.21/0.67    ~spl2_13 | spl2_14 | ~spl2_10),
% 2.21/0.67    inference(avatar_split_clause,[],[f274,f197,f282,f278])).
% 2.21/0.67  fof(f274,plain,(
% 2.21/0.67    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl2_10),
% 2.21/0.67    inference(superposition,[],[f114,f199])).
% 2.21/0.67  fof(f114,plain,(
% 2.21/0.67    ( ! [X2,X3] : (m1_subset_1(k4_xboole_0(X2,X3),k1_zfmisc_1(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X2))) )),
% 2.21/0.67    inference(duplicate_literal_removal,[],[f113])).
% 2.21/0.67  fof(f113,plain,(
% 2.21/0.67    ( ! [X2,X3] : (m1_subset_1(k4_xboole_0(X2,X3),k1_zfmisc_1(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X2))) )),
% 2.21/0.67    inference(superposition,[],[f59,f60])).
% 2.21/0.67  fof(f59,plain,(
% 2.21/0.67    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.21/0.67    inference(cnf_transformation,[],[f29])).
% 2.21/0.67  fof(f29,plain,(
% 2.21/0.67    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.21/0.67    inference(ennf_transformation,[],[f7])).
% 2.21/0.67  fof(f7,axiom,(
% 2.21/0.67    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.21/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 2.21/0.67  fof(f252,plain,(
% 2.21/0.67    spl2_9),
% 2.21/0.67    inference(avatar_contradiction_clause,[],[f251])).
% 2.21/0.67  fof(f251,plain,(
% 2.21/0.67    $false | spl2_9),
% 2.21/0.67    inference(subsumption_resolution,[],[f250,f48])).
% 2.21/0.67  fof(f250,plain,(
% 2.21/0.67    ~l1_pre_topc(sK0) | spl2_9),
% 2.21/0.67    inference(subsumption_resolution,[],[f244,f49])).
% 2.21/0.67  fof(f244,plain,(
% 2.21/0.67    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_9),
% 2.21/0.67    inference(resolution,[],[f63,f195])).
% 2.21/0.67  fof(f195,plain,(
% 2.21/0.67    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_9),
% 2.21/0.67    inference(avatar_component_clause,[],[f193])).
% 2.21/0.67  fof(f193,plain,(
% 2.21/0.67    spl2_9 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.21/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 2.21/0.67  fof(f63,plain,(
% 2.21/0.67    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.21/0.67    inference(cnf_transformation,[],[f35])).
% 2.21/0.67  fof(f35,plain,(
% 2.21/0.67    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.21/0.67    inference(flattening,[],[f34])).
% 2.21/0.67  fof(f34,plain,(
% 2.21/0.67    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.21/0.67    inference(ennf_transformation,[],[f11])).
% 2.21/0.67  fof(f11,axiom,(
% 2.21/0.67    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.21/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 2.21/0.67  fof(f201,plain,(
% 2.21/0.67    ~spl2_9 | spl2_10 | ~spl2_2),
% 2.21/0.67    inference(avatar_split_clause,[],[f191,f79,f197,f193])).
% 2.21/0.67  fof(f191,plain,(
% 2.21/0.67    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 2.21/0.67    inference(superposition,[],[f80,f70])).
% 2.21/0.67  fof(f80,plain,(
% 2.21/0.67    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl2_2),
% 2.21/0.67    inference(avatar_component_clause,[],[f79])).
% 2.21/0.67  fof(f83,plain,(
% 2.21/0.67    spl2_1 | spl2_2),
% 2.21/0.67    inference(avatar_split_clause,[],[f50,f79,f75])).
% 2.21/0.67  fof(f50,plain,(
% 2.21/0.67    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 2.21/0.67    inference(cnf_transformation,[],[f43])).
% 2.21/0.67  fof(f82,plain,(
% 2.21/0.67    ~spl2_1 | ~spl2_2),
% 2.21/0.67    inference(avatar_split_clause,[],[f51,f79,f75])).
% 2.21/0.67  fof(f51,plain,(
% 2.21/0.67    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 2.21/0.67    inference(cnf_transformation,[],[f43])).
% 2.21/0.67  % SZS output end Proof for theBenchmark
% 2.21/0.67  % (20365)------------------------------
% 2.21/0.67  % (20365)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.21/0.67  % (20365)Termination reason: Refutation
% 2.21/0.67  
% 2.21/0.67  % (20365)Memory used [KB]: 7036
% 2.21/0.67  % (20365)Time elapsed: 0.260 s
% 2.21/0.67  % (20365)------------------------------
% 2.21/0.67  % (20365)------------------------------
% 2.21/0.67  % (20358)Success in time 0.307 s
%------------------------------------------------------------------------------
