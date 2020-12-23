%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:08 EST 2020

% Result     : Theorem 2.33s
% Output     : Refutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 267 expanded)
%              Number of leaves         :   19 (  96 expanded)
%              Depth                    :   11
%              Number of atoms          :  292 ( 932 expanded)
%              Number of equality atoms :   10 (  22 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1723,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f157,f168,f211,f449,f981,f1258,f1722])).

fof(f1722,plain,
    ( ~ spl3_20
    | spl3_36 ),
    inference(avatar_contradiction_clause,[],[f1721])).

fof(f1721,plain,
    ( $false
    | ~ spl3_20
    | spl3_36 ),
    inference(subsumption_resolution,[],[f1717,f46])).

fof(f46,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f1717,plain,
    ( ~ r1_tarski(sK2,sK2)
    | ~ spl3_20
    | spl3_36 ),
    inference(resolution,[],[f1264,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f1264,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK1,sK2))
    | ~ spl3_20
    | spl3_36 ),
    inference(subsumption_resolution,[],[f1263,f30])).

fof(f30,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f25,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,X2)))
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tops_1)).

fof(f1263,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_20
    | spl3_36 ),
    inference(subsumption_resolution,[],[f1262,f32])).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f1262,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_20
    | spl3_36 ),
    inference(subsumption_resolution,[],[f1260,f432])).

fof(f432,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f431])).

fof(f431,plain,
    ( spl3_20
  <=> m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f1260,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK1,sK2))
    | ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_36 ),
    inference(resolution,[],[f1259,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

fof(f1259,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | spl3_36 ),
    inference(resolution,[],[f976,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f976,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2))))
    | spl3_36 ),
    inference(avatar_component_clause,[],[f974])).

fof(f974,plain,
    ( spl3_36
  <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f1258,plain,
    ( ~ spl3_20
    | spl3_37 ),
    inference(avatar_contradiction_clause,[],[f1257])).

fof(f1257,plain,
    ( $false
    | ~ spl3_20
    | spl3_37 ),
    inference(subsumption_resolution,[],[f1256,f30])).

fof(f1256,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_20
    | spl3_37 ),
    inference(subsumption_resolution,[],[f1255,f31])).

fof(f31,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f1255,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_20
    | spl3_37 ),
    inference(subsumption_resolution,[],[f1254,f432])).

fof(f1254,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_37 ),
    inference(subsumption_resolution,[],[f1252,f36])).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f1252,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK1,sK2))
    | ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_37 ),
    inference(resolution,[],[f1251,f35])).

fof(f1251,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | spl3_37 ),
    inference(resolution,[],[f980,f41])).

fof(f980,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2))))
    | spl3_37 ),
    inference(avatar_component_clause,[],[f978])).

fof(f978,plain,
    ( spl3_37
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f981,plain,
    ( ~ spl3_36
    | ~ spl3_37
    | spl3_11 ),
    inference(avatar_split_clause,[],[f866,f154,f978,f974])).

fof(f154,plain,
    ( spl3_11
  <=> r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f866,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2))))
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2))))
    | spl3_11 ),
    inference(resolution,[],[f416,f251])).

fof(f251,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | spl3_11 ),
    inference(subsumption_resolution,[],[f250,f31])).

fof(f250,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_11 ),
    inference(subsumption_resolution,[],[f249,f32])).

fof(f249,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_11 ),
    inference(superposition,[],[f156,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f156,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | spl3_11 ),
    inference(avatar_component_clause,[],[f154])).

fof(f416,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f415])).

fof(f415,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f121,f45])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_subset_1(X1,X2,X0),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f44,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f449,plain,(
    spl3_20 ),
    inference(avatar_contradiction_clause,[],[f448])).

fof(f448,plain,
    ( $false
    | spl3_20 ),
    inference(subsumption_resolution,[],[f447,f31])).

fof(f447,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_20 ),
    inference(subsumption_resolution,[],[f444,f32])).

fof(f444,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_20 ),
    inference(resolution,[],[f144,f433])).

fof(f433,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_20 ),
    inference(avatar_component_clause,[],[f431])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f143])).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f44,f45])).

fof(f211,plain,(
    spl3_10 ),
    inference(avatar_contradiction_clause,[],[f210])).

fof(f210,plain,
    ( $false
    | spl3_10 ),
    inference(subsumption_resolution,[],[f204,f49])).

fof(f49,plain,(
    r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f40,f32])).

fof(f204,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | spl3_10 ),
    inference(resolution,[],[f191,f94])).

fof(f94,plain,(
    r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(subsumption_resolution,[],[f91,f30])).

fof(f91,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f34,f32])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f191,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_tops_1(sK0,sK2),X0)
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | spl3_10 ),
    inference(resolution,[],[f190,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f190,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | spl3_10 ),
    inference(resolution,[],[f152,f41])).

fof(f152,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl3_10
  <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f168,plain,(
    spl3_9 ),
    inference(avatar_contradiction_clause,[],[f167])).

fof(f167,plain,
    ( $false
    | spl3_9 ),
    inference(subsumption_resolution,[],[f162,f48])).

fof(f48,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f40,f31])).

fof(f162,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | spl3_9 ),
    inference(resolution,[],[f161,f93])).

fof(f93,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f90,f30])).

fof(f90,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f34,f31])).

fof(f161,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_tops_1(sK0,sK1),X0)
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | spl3_9 ),
    inference(resolution,[],[f160,f43])).

fof(f160,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | spl3_9 ),
    inference(resolution,[],[f148,f41])).

fof(f148,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl3_9
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f157,plain,
    ( ~ spl3_9
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f141,f154,f150,f146])).

fof(f141,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f33,f45])).

fof(f33,plain,(
    ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:23:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (12902)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (12901)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (12904)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (12911)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (12921)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (12916)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.51  % (12905)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (12913)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (12899)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (12915)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.52  % (12922)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.52  % (12912)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (12903)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.52  % (12907)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.52  % (12914)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (12917)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.52  % (12908)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.52  % (12924)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.52  % (12906)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.53  % (12923)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.53  % (12900)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (12919)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.53  % (12910)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.53  % (12920)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.53  % (12909)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.34/0.54  % (12918)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 2.33/0.69  % (12903)Refutation found. Thanks to Tanya!
% 2.33/0.69  % SZS status Theorem for theBenchmark
% 2.33/0.69  % SZS output start Proof for theBenchmark
% 2.33/0.69  fof(f1723,plain,(
% 2.33/0.69    $false),
% 2.33/0.69    inference(avatar_sat_refutation,[],[f157,f168,f211,f449,f981,f1258,f1722])).
% 2.33/0.69  fof(f1722,plain,(
% 2.33/0.69    ~spl3_20 | spl3_36),
% 2.33/0.69    inference(avatar_contradiction_clause,[],[f1721])).
% 2.33/0.69  fof(f1721,plain,(
% 2.33/0.69    $false | (~spl3_20 | spl3_36)),
% 2.33/0.69    inference(subsumption_resolution,[],[f1717,f46])).
% 2.33/0.69  fof(f46,plain,(
% 2.33/0.69    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.33/0.69    inference(equality_resolution,[],[f38])).
% 2.33/0.69  fof(f38,plain,(
% 2.33/0.69    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.33/0.69    inference(cnf_transformation,[],[f28])).
% 2.33/0.69  fof(f28,plain,(
% 2.33/0.69    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.33/0.69    inference(flattening,[],[f27])).
% 2.33/0.69  fof(f27,plain,(
% 2.33/0.69    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.33/0.69    inference(nnf_transformation,[],[f1])).
% 2.33/0.69  fof(f1,axiom,(
% 2.33/0.69    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.33/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.33/0.69  fof(f1717,plain,(
% 2.33/0.69    ~r1_tarski(sK2,sK2) | (~spl3_20 | spl3_36)),
% 2.33/0.69    inference(resolution,[],[f1264,f42])).
% 2.33/0.69  fof(f42,plain,(
% 2.33/0.69    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 2.33/0.69    inference(cnf_transformation,[],[f16])).
% 2.33/0.69  fof(f16,plain,(
% 2.33/0.69    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 2.33/0.69    inference(ennf_transformation,[],[f2])).
% 2.33/0.69  fof(f2,axiom,(
% 2.33/0.69    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 2.33/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 2.33/0.69  fof(f1264,plain,(
% 2.33/0.69    ~r1_tarski(sK2,k2_xboole_0(sK1,sK2)) | (~spl3_20 | spl3_36)),
% 2.33/0.69    inference(subsumption_resolution,[],[f1263,f30])).
% 2.33/0.69  fof(f30,plain,(
% 2.33/0.69    l1_pre_topc(sK0)),
% 2.33/0.69    inference(cnf_transformation,[],[f26])).
% 2.33/0.69  fof(f26,plain,(
% 2.33/0.69    ((~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 2.33/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f25,f24,f23])).
% 2.33/0.69  fof(f23,plain,(
% 2.33/0.69    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 2.33/0.69    introduced(choice_axiom,[])).
% 2.33/0.69  fof(f24,plain,(
% 2.33/0.69    ? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.33/0.69    introduced(choice_axiom,[])).
% 2.33/0.69  fof(f25,plain,(
% 2.33/0.69    ? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.33/0.69    introduced(choice_axiom,[])).
% 2.33/0.69  fof(f12,plain,(
% 2.33/0.69    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.33/0.69    inference(ennf_transformation,[],[f11])).
% 2.33/0.69  fof(f11,negated_conjecture,(
% 2.33/0.69    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 2.33/0.69    inference(negated_conjecture,[],[f10])).
% 2.33/0.69  fof(f10,conjecture,(
% 2.33/0.69    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 2.33/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tops_1)).
% 2.33/0.69  fof(f1263,plain,(
% 2.33/0.69    ~r1_tarski(sK2,k2_xboole_0(sK1,sK2)) | ~l1_pre_topc(sK0) | (~spl3_20 | spl3_36)),
% 2.33/0.69    inference(subsumption_resolution,[],[f1262,f32])).
% 2.33/0.69  fof(f32,plain,(
% 2.33/0.69    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.33/0.69    inference(cnf_transformation,[],[f26])).
% 2.33/0.69  fof(f1262,plain,(
% 2.33/0.69    ~r1_tarski(sK2,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_20 | spl3_36)),
% 2.33/0.69    inference(subsumption_resolution,[],[f1260,f432])).
% 2.33/0.69  fof(f432,plain,(
% 2.33/0.69    m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_20),
% 2.33/0.69    inference(avatar_component_clause,[],[f431])).
% 2.33/0.69  fof(f431,plain,(
% 2.33/0.69    spl3_20 <=> m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.33/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 2.33/0.69  fof(f1260,plain,(
% 2.33/0.69    ~r1_tarski(sK2,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_36),
% 2.33/0.69    inference(resolution,[],[f1259,f35])).
% 2.33/0.69  fof(f35,plain,(
% 2.33/0.69    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.33/0.69    inference(cnf_transformation,[],[f15])).
% 2.33/0.69  fof(f15,plain,(
% 2.33/0.69    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.33/0.69    inference(flattening,[],[f14])).
% 2.33/0.69  fof(f14,plain,(
% 2.33/0.69    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.33/0.69    inference(ennf_transformation,[],[f9])).
% 2.33/0.69  fof(f9,axiom,(
% 2.33/0.69    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 2.33/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).
% 2.33/0.69  fof(f1259,plain,(
% 2.33/0.69    ~r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | spl3_36),
% 2.33/0.69    inference(resolution,[],[f976,f41])).
% 2.33/0.69  fof(f41,plain,(
% 2.33/0.69    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.33/0.69    inference(cnf_transformation,[],[f29])).
% 2.33/0.69  fof(f29,plain,(
% 2.33/0.69    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.33/0.69    inference(nnf_transformation,[],[f7])).
% 2.33/0.69  fof(f7,axiom,(
% 2.33/0.69    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.33/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.33/0.69  fof(f976,plain,(
% 2.33/0.69    ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))) | spl3_36),
% 2.33/0.69    inference(avatar_component_clause,[],[f974])).
% 2.33/0.69  fof(f974,plain,(
% 2.33/0.69    spl3_36 <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2))))),
% 2.33/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 2.33/0.69  fof(f1258,plain,(
% 2.33/0.69    ~spl3_20 | spl3_37),
% 2.33/0.69    inference(avatar_contradiction_clause,[],[f1257])).
% 2.33/0.69  fof(f1257,plain,(
% 2.33/0.69    $false | (~spl3_20 | spl3_37)),
% 2.33/0.69    inference(subsumption_resolution,[],[f1256,f30])).
% 2.33/0.69  fof(f1256,plain,(
% 2.33/0.69    ~l1_pre_topc(sK0) | (~spl3_20 | spl3_37)),
% 2.33/0.69    inference(subsumption_resolution,[],[f1255,f31])).
% 2.33/0.69  fof(f31,plain,(
% 2.33/0.69    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.33/0.69    inference(cnf_transformation,[],[f26])).
% 2.33/0.69  fof(f1255,plain,(
% 2.33/0.69    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_20 | spl3_37)),
% 2.33/0.69    inference(subsumption_resolution,[],[f1254,f432])).
% 2.33/0.69  fof(f1254,plain,(
% 2.33/0.69    ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_37),
% 2.33/0.69    inference(subsumption_resolution,[],[f1252,f36])).
% 2.33/0.69  fof(f36,plain,(
% 2.33/0.69    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.33/0.69    inference(cnf_transformation,[],[f4])).
% 2.33/0.69  fof(f4,axiom,(
% 2.33/0.69    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.33/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.33/0.69  fof(f1252,plain,(
% 2.33/0.69    ~r1_tarski(sK1,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_37),
% 2.33/0.69    inference(resolution,[],[f1251,f35])).
% 2.33/0.69  fof(f1251,plain,(
% 2.33/0.69    ~r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | spl3_37),
% 2.33/0.69    inference(resolution,[],[f980,f41])).
% 2.33/0.69  fof(f980,plain,(
% 2.33/0.69    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))) | spl3_37),
% 2.33/0.69    inference(avatar_component_clause,[],[f978])).
% 2.33/0.69  fof(f978,plain,(
% 2.33/0.69    spl3_37 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2))))),
% 2.33/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 2.33/0.69  fof(f981,plain,(
% 2.33/0.69    ~spl3_36 | ~spl3_37 | spl3_11),
% 2.33/0.69    inference(avatar_split_clause,[],[f866,f154,f978,f974])).
% 2.33/0.69  fof(f154,plain,(
% 2.33/0.69    spl3_11 <=> r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 2.33/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 2.33/0.69  fof(f866,plain,(
% 2.33/0.69    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))) | ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))) | spl3_11),
% 2.33/0.69    inference(resolution,[],[f416,f251])).
% 2.33/0.69  fof(f251,plain,(
% 2.33/0.69    ~r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | spl3_11),
% 2.33/0.69    inference(subsumption_resolution,[],[f250,f31])).
% 2.33/0.69  fof(f250,plain,(
% 2.33/0.69    ~r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_11),
% 2.33/0.69    inference(subsumption_resolution,[],[f249,f32])).
% 2.33/0.69  fof(f249,plain,(
% 2.33/0.69    ~r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_11),
% 2.33/0.69    inference(superposition,[],[f156,f45])).
% 2.33/0.69  fof(f45,plain,(
% 2.33/0.69    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.33/0.69    inference(cnf_transformation,[],[f22])).
% 2.33/0.69  fof(f22,plain,(
% 2.33/0.69    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.33/0.69    inference(flattening,[],[f21])).
% 2.33/0.69  fof(f21,plain,(
% 2.33/0.69    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.33/0.69    inference(ennf_transformation,[],[f6])).
% 2.33/0.69  fof(f6,axiom,(
% 2.33/0.69    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 2.33/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.33/0.69  fof(f156,plain,(
% 2.33/0.69    ~r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | spl3_11),
% 2.33/0.69    inference(avatar_component_clause,[],[f154])).
% 2.33/0.69  fof(f416,plain,(
% 2.33/0.69    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.33/0.69    inference(duplicate_literal_removal,[],[f415])).
% 2.33/0.69  fof(f415,plain,(
% 2.33/0.69    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.33/0.69    inference(superposition,[],[f121,f45])).
% 2.33/0.69  fof(f121,plain,(
% 2.33/0.69    ( ! [X2,X0,X1] : (r1_tarski(k4_subset_1(X1,X2,X0),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.33/0.69    inference(resolution,[],[f44,f40])).
% 2.33/0.69  fof(f40,plain,(
% 2.33/0.69    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.33/0.69    inference(cnf_transformation,[],[f29])).
% 2.33/0.69  fof(f44,plain,(
% 2.33/0.69    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.33/0.69    inference(cnf_transformation,[],[f20])).
% 2.33/0.69  fof(f20,plain,(
% 2.33/0.69    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.33/0.69    inference(flattening,[],[f19])).
% 2.33/0.69  fof(f19,plain,(
% 2.33/0.69    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.33/0.69    inference(ennf_transformation,[],[f5])).
% 2.33/0.69  fof(f5,axiom,(
% 2.33/0.69    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.33/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 2.33/0.69  fof(f449,plain,(
% 2.33/0.69    spl3_20),
% 2.33/0.69    inference(avatar_contradiction_clause,[],[f448])).
% 2.33/0.69  fof(f448,plain,(
% 2.33/0.69    $false | spl3_20),
% 2.33/0.69    inference(subsumption_resolution,[],[f447,f31])).
% 2.33/0.69  fof(f447,plain,(
% 2.33/0.69    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_20),
% 2.33/0.69    inference(subsumption_resolution,[],[f444,f32])).
% 2.33/0.69  fof(f444,plain,(
% 2.33/0.69    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_20),
% 2.33/0.69    inference(resolution,[],[f144,f433])).
% 2.33/0.69  fof(f433,plain,(
% 2.33/0.69    ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_20),
% 2.33/0.69    inference(avatar_component_clause,[],[f431])).
% 2.33/0.69  fof(f144,plain,(
% 2.33/0.69    ( ! [X2,X0,X1] : (m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.33/0.69    inference(duplicate_literal_removal,[],[f143])).
% 2.33/0.69  fof(f143,plain,(
% 2.33/0.69    ( ! [X2,X0,X1] : (m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.33/0.69    inference(superposition,[],[f44,f45])).
% 2.33/0.69  fof(f211,plain,(
% 2.33/0.69    spl3_10),
% 2.33/0.69    inference(avatar_contradiction_clause,[],[f210])).
% 2.33/0.69  fof(f210,plain,(
% 2.33/0.69    $false | spl3_10),
% 2.33/0.69    inference(subsumption_resolution,[],[f204,f49])).
% 2.33/0.69  fof(f49,plain,(
% 2.33/0.69    r1_tarski(sK2,u1_struct_0(sK0))),
% 2.33/0.69    inference(resolution,[],[f40,f32])).
% 2.33/0.69  fof(f204,plain,(
% 2.33/0.69    ~r1_tarski(sK2,u1_struct_0(sK0)) | spl3_10),
% 2.33/0.69    inference(resolution,[],[f191,f94])).
% 2.33/0.69  fof(f94,plain,(
% 2.33/0.69    r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 2.33/0.69    inference(subsumption_resolution,[],[f91,f30])).
% 2.33/0.69  fof(f91,plain,(
% 2.33/0.69    r1_tarski(k1_tops_1(sK0,sK2),sK2) | ~l1_pre_topc(sK0)),
% 2.33/0.69    inference(resolution,[],[f34,f32])).
% 2.33/0.69  fof(f34,plain,(
% 2.33/0.69    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 2.33/0.69    inference(cnf_transformation,[],[f13])).
% 2.33/0.69  fof(f13,plain,(
% 2.33/0.69    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.33/0.69    inference(ennf_transformation,[],[f8])).
% 2.33/0.69  fof(f8,axiom,(
% 2.33/0.69    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 2.33/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 2.33/0.69  fof(f191,plain,(
% 2.33/0.69    ( ! [X0] : (~r1_tarski(k1_tops_1(sK0,sK2),X0) | ~r1_tarski(X0,u1_struct_0(sK0))) ) | spl3_10),
% 2.33/0.69    inference(resolution,[],[f190,f43])).
% 2.33/0.69  fof(f43,plain,(
% 2.33/0.69    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.33/0.69    inference(cnf_transformation,[],[f18])).
% 2.33/0.69  fof(f18,plain,(
% 2.33/0.69    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.33/0.69    inference(flattening,[],[f17])).
% 2.33/0.69  fof(f17,plain,(
% 2.33/0.69    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.33/0.69    inference(ennf_transformation,[],[f3])).
% 2.33/0.69  fof(f3,axiom,(
% 2.33/0.69    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.33/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.33/0.69  fof(f190,plain,(
% 2.33/0.69    ~r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) | spl3_10),
% 2.33/0.69    inference(resolution,[],[f152,f41])).
% 2.33/0.69  fof(f152,plain,(
% 2.33/0.69    ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_10),
% 2.33/0.69    inference(avatar_component_clause,[],[f150])).
% 2.33/0.69  fof(f150,plain,(
% 2.33/0.69    spl3_10 <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.33/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 2.33/0.69  fof(f168,plain,(
% 2.33/0.69    spl3_9),
% 2.33/0.69    inference(avatar_contradiction_clause,[],[f167])).
% 2.33/0.69  fof(f167,plain,(
% 2.33/0.69    $false | spl3_9),
% 2.33/0.69    inference(subsumption_resolution,[],[f162,f48])).
% 2.33/0.69  fof(f48,plain,(
% 2.33/0.69    r1_tarski(sK1,u1_struct_0(sK0))),
% 2.33/0.69    inference(resolution,[],[f40,f31])).
% 2.33/0.69  fof(f162,plain,(
% 2.33/0.69    ~r1_tarski(sK1,u1_struct_0(sK0)) | spl3_9),
% 2.33/0.69    inference(resolution,[],[f161,f93])).
% 2.33/0.69  fof(f93,plain,(
% 2.33/0.69    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 2.33/0.69    inference(subsumption_resolution,[],[f90,f30])).
% 2.33/0.69  fof(f90,plain,(
% 2.33/0.69    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0)),
% 2.33/0.69    inference(resolution,[],[f34,f31])).
% 2.33/0.69  fof(f161,plain,(
% 2.33/0.69    ( ! [X0] : (~r1_tarski(k1_tops_1(sK0,sK1),X0) | ~r1_tarski(X0,u1_struct_0(sK0))) ) | spl3_9),
% 2.33/0.69    inference(resolution,[],[f160,f43])).
% 2.33/0.69  fof(f160,plain,(
% 2.33/0.69    ~r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | spl3_9),
% 2.33/0.69    inference(resolution,[],[f148,f41])).
% 2.33/0.69  fof(f148,plain,(
% 2.33/0.69    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_9),
% 2.33/0.69    inference(avatar_component_clause,[],[f146])).
% 2.33/0.69  fof(f146,plain,(
% 2.33/0.69    spl3_9 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.33/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 2.33/0.69  fof(f157,plain,(
% 2.33/0.69    ~spl3_9 | ~spl3_10 | ~spl3_11),
% 2.33/0.69    inference(avatar_split_clause,[],[f141,f154,f150,f146])).
% 2.33/0.69  fof(f141,plain,(
% 2.33/0.69    ~r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.33/0.69    inference(superposition,[],[f33,f45])).
% 2.33/0.69  fof(f33,plain,(
% 2.33/0.69    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 2.33/0.69    inference(cnf_transformation,[],[f26])).
% 2.33/0.69  % SZS output end Proof for theBenchmark
% 2.33/0.69  % (12903)------------------------------
% 2.33/0.69  % (12903)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.33/0.69  % (12903)Termination reason: Refutation
% 2.33/0.69  
% 2.33/0.69  % (12903)Memory used [KB]: 7164
% 2.33/0.69  % (12903)Time elapsed: 0.272 s
% 2.33/0.69  % (12903)------------------------------
% 2.33/0.69  % (12903)------------------------------
% 2.33/0.69  % (12898)Success in time 0.322 s
%------------------------------------------------------------------------------
