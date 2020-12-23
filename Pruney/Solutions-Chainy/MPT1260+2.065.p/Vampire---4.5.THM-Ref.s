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
% DateTime   : Thu Dec  3 13:11:44 EST 2020

% Result     : Theorem 1.73s
% Output     : Refutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :  176 ( 471 expanded)
%              Number of leaves         :   39 ( 162 expanded)
%              Depth                    :   17
%              Number of atoms          :  608 (1602 expanded)
%              Number of equality atoms :  113 ( 401 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1079,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f116,f121,f126,f135,f138,f221,f233,f326,f488,f509,f515,f549,f700,f741,f764,f765,f891,f941,f1078])).

fof(f1078,plain,
    ( ~ spl4_2
    | ~ spl4_3
    | spl4_26
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f942,f938,f546,f123,f118])).

fof(f118,plain,
    ( spl4_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f123,plain,
    ( spl4_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f546,plain,
    ( spl4_26
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f938,plain,
    ( spl4_37
  <=> sK1 = k6_subset_1(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f942,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_37 ),
    inference(superposition,[],[f940,f306])).

fof(f306,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k6_subset_1(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f305])).

fof(f305,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k6_subset_1(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f222,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f222,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(forward_demodulation,[],[f94,f101])).

fof(f101,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k6_subset_1(X0,X1) ),
    inference(definition_unfolding,[],[f76,f74])).

fof(f74,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f76,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f61,f74])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f940,plain,
    ( sK1 = k6_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f938])).

fof(f941,plain,
    ( spl4_37
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f936,f888,f938])).

fof(f888,plain,
    ( spl4_36
  <=> k1_xboole_0 = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f936,plain,
    ( sK1 = k6_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl4_36 ),
    inference(forward_demodulation,[],[f928,f177])).

fof(f177,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f103,f102])).

fof(f102,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(definition_unfolding,[],[f77,f74])).

fof(f77,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f103,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(definition_unfolding,[],[f91,f93])).

fof(f93,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f75,f74])).

fof(f75,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f91,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f928,plain,
    ( k6_subset_1(sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_xboole_0)
    | ~ spl4_36 ),
    inference(superposition,[],[f101,f890])).

fof(f890,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f888])).

fof(f891,plain,
    ( spl4_36
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f886,f230,f888])).

fof(f230,plain,
    ( spl4_13
  <=> k2_tops_1(sK0,sK1) = k6_subset_1(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f886,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl4_13 ),
    inference(duplicate_literal_removal,[],[f881])).

fof(f881,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | k1_xboole_0 = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl4_13 ),
    inference(resolution,[],[f754,f247])).

fof(f247,plain,(
    ! [X14,X15] :
      ( r2_hidden(sK3(X14,X15,k1_xboole_0),X14)
      | k1_xboole_0 = k3_xboole_0(X14,X15) ) ),
    inference(resolution,[],[f87,f190])).

fof(f190,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(condensation,[],[f188])).

fof(f188,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f183,f159])).

fof(f159,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(k1_xboole_0,X0) ),
    inference(superposition,[],[f101,f102])).

fof(f183,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k6_subset_1(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(forward_demodulation,[],[f105,f101])).

fof(f105,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f69,f74])).

fof(f69,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f45,f46])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f53,f54])).

fof(f54,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f754,plain,
    ( ! [X7] :
        ( ~ r2_hidden(sK3(X7,k2_tops_1(sK0,sK1),k1_xboole_0),sK1)
        | k1_xboole_0 = k3_xboole_0(X7,k2_tops_1(sK0,sK1)) )
    | ~ spl4_13 ),
    inference(resolution,[],[f746,f275])).

fof(f275,plain,(
    ! [X14,X15] :
      ( r2_hidden(sK3(X14,X15,k1_xboole_0),X15)
      | k1_xboole_0 = k3_xboole_0(X14,X15) ) ),
    inference(resolution,[],[f88,f190])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f746,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k2_tops_1(sK0,sK1))
        | ~ r2_hidden(X2,sK1) )
    | ~ spl4_13 ),
    inference(superposition,[],[f183,f232])).

fof(f232,plain,
    ( k2_tops_1(sK0,sK1) = k6_subset_1(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f230])).

fof(f765,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f764,plain,
    ( spl4_5
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(avatar_contradiction_clause,[],[f762])).

fof(f762,plain,
    ( $false
    | spl4_5
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f227,f761])).

fof(f761,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_5
    | ~ spl4_13 ),
    inference(trivial_inequality_removal,[],[f760])).

fof(f760,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_5
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f358,f232])).

fof(f358,plain,
    ( k2_tops_1(sK0,sK1) != k6_subset_1(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_5 ),
    inference(superposition,[],[f133,f222])).

fof(f133,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl4_5
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f227,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f226])).

fof(f226,plain,
    ( spl4_12
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f741,plain,
    ( ~ spl4_2
    | ~ spl4_3
    | spl4_13
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f714,f546,f230,f123,f118])).

fof(f714,plain,
    ( k2_tops_1(sK0,sK1) = k6_subset_1(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_26 ),
    inference(superposition,[],[f464,f548])).

fof(f548,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f546])).

fof(f464,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k6_subset_1(k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(global_subsumption,[],[f317,f463])).

fof(f463,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k6_subset_1(k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f222,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f317,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(global_subsumption,[],[f65,f316])).

fof(f316,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f315])).

fof(f315,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f78,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f700,plain,
    ( ~ spl4_2
    | ~ spl4_3
    | spl4_25 ),
    inference(avatar_contradiction_clause,[],[f687])).

fof(f687,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_3
    | spl4_25 ),
    inference(unit_resulting_resolution,[],[f120,f544,f125,f653])).

fof(f653,plain,(
    ! [X12,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X12)))
      | r1_tarski(k1_tops_1(X12,X11),X11)
      | ~ l1_pre_topc(X12) ) ),
    inference(superposition,[],[f140,f306])).

fof(f140,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(resolution,[],[f79,f92])).

fof(f92,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f125,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f123])).

fof(f544,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | spl4_25 ),
    inference(avatar_component_clause,[],[f542])).

fof(f542,plain,
    ( spl4_25
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f120,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f118])).

fof(f549,plain,
    ( ~ spl4_25
    | spl4_26
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f540,f502,f546,f542])).

fof(f502,plain,
    ( spl4_23
  <=> r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f540,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl4_23 ),
    inference(resolution,[],[f504,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f504,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f502])).

fof(f515,plain,(
    spl4_24 ),
    inference(avatar_contradiction_clause,[],[f511])).

fof(f511,plain,
    ( $false
    | spl4_24 ),
    inference(unit_resulting_resolution,[],[f298,f508,f79])).

fof(f508,plain,
    ( ~ r1_tarski(sK1,sK1)
    | spl4_24 ),
    inference(avatar_component_clause,[],[f506])).

fof(f506,plain,
    ( spl4_24
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f298,plain,(
    ! [X8] : m1_subset_1(X8,k1_zfmisc_1(X8)) ),
    inference(superposition,[],[f92,f291])).

fof(f291,plain,(
    ! [X2] : k6_subset_1(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f288,f177])).

fof(f288,plain,(
    ! [X2] : k6_subset_1(X2,k1_xboole_0) = k5_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f101,f283])).

fof(f283,plain,(
    ! [X10] : k1_xboole_0 = k3_xboole_0(X10,k1_xboole_0) ),
    inference(resolution,[],[f278,f190])).

fof(f278,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1,X1),X1)
      | k3_xboole_0(X0,X1) = X1 ) ),
    inference(factoring,[],[f88])).

fof(f509,plain,
    ( ~ spl4_4
    | spl4_23
    | ~ spl4_24
    | ~ spl4_3
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f498,f486,f123,f506,f502,f128])).

fof(f128,plain,
    ( spl4_4
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f486,plain,
    ( spl4_22
  <=> ! [X23] :
        ( ~ r1_tarski(X23,sK1)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X23,k1_tops_1(sK0,sK1))
        | ~ v3_pre_topc(X23,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f498,plain,
    ( ~ r1_tarski(sK1,sK1)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl4_3
    | ~ spl4_22 ),
    inference(resolution,[],[f487,f125])).

fof(f487,plain,
    ( ! [X23] :
        ( ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X23,sK1)
        | r1_tarski(X23,k1_tops_1(sK0,sK1))
        | ~ v3_pre_topc(X23,sK0) )
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f486])).

fof(f488,plain,
    ( ~ spl4_2
    | spl4_22
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f480,f123,f486,f118])).

fof(f480,plain,
    ( ! [X23] :
        ( ~ r1_tarski(X23,sK1)
        | ~ v3_pre_topc(X23,sK0)
        | r1_tarski(X23,k1_tops_1(sK0,sK1))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl4_3 ),
    inference(resolution,[],[f67,f125])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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

fof(f326,plain,
    ( ~ spl4_2
    | ~ spl4_3
    | spl4_12 ),
    inference(avatar_contradiction_clause,[],[f321])).

fof(f321,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_3
    | spl4_12 ),
    inference(unit_resulting_resolution,[],[f120,f125,f228,f317])).

fof(f228,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_12 ),
    inference(avatar_component_clause,[],[f226])).

fof(f233,plain,
    ( ~ spl4_12
    | spl4_13
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f223,f132,f230,f226])).

fof(f223,plain,
    ( k2_tops_1(sK0,sK1) = k6_subset_1(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_5 ),
    inference(superposition,[],[f222,f134])).

fof(f134,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f132])).

fof(f221,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | spl4_11
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f215,f123,f218,f118,f113])).

fof(f113,plain,
    ( spl4_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f218,plain,
    ( spl4_11
  <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f215,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f66,f125])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k1_tops_1(X0,X1),X0)
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f138,plain,
    ( ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f137,f132,f128])).

fof(f137,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ spl4_5 ),
    inference(trivial_inequality_removal,[],[f136])).

fof(f136,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f60,f134])).

fof(f60,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f39,f41,f40])).

fof(f40,plain,
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

fof(f41,plain,
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
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

fof(f135,plain,
    ( spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f59,f132,f128])).

fof(f59,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f126,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f58,f123])).

fof(f58,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f121,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f57,f118])).

fof(f57,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f116,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f56,f113])).

fof(f56,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:02:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (11917)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.50  % (11915)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.50  % (11930)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.51  % (11919)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (11916)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.51  % (11918)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (11922)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.51  % (11939)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.52  % (11920)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (11932)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.52  % (11944)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (11923)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (11941)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (11924)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.52  % (11935)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.52  % (11929)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (11938)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (11926)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (11927)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (11936)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.53  % (11921)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (11937)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (11940)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.53  % (11942)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.53  % (11931)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (11925)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.54  % (11943)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (11925)Refutation not found, incomplete strategy% (11925)------------------------------
% 0.21/0.54  % (11925)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (11925)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (11925)Memory used [KB]: 10874
% 0.21/0.54  % (11925)Time elapsed: 0.131 s
% 0.21/0.54  % (11925)------------------------------
% 0.21/0.54  % (11925)------------------------------
% 0.21/0.54  % (11931)Refutation not found, incomplete strategy% (11931)------------------------------
% 0.21/0.54  % (11931)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (11931)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (11931)Memory used [KB]: 10746
% 0.21/0.54  % (11931)Time elapsed: 0.105 s
% 0.21/0.54  % (11931)------------------------------
% 0.21/0.54  % (11931)------------------------------
% 0.21/0.54  % (11943)Refutation not found, incomplete strategy% (11943)------------------------------
% 0.21/0.54  % (11943)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (11943)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (11943)Memory used [KB]: 10874
% 0.21/0.54  % (11943)Time elapsed: 0.133 s
% 0.21/0.54  % (11943)------------------------------
% 0.21/0.54  % (11943)------------------------------
% 0.21/0.54  % (11928)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.55  % (11934)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (11933)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.73/0.59  % (11938)Refutation found. Thanks to Tanya!
% 1.73/0.59  % SZS status Theorem for theBenchmark
% 1.89/0.61  % SZS output start Proof for theBenchmark
% 1.89/0.61  fof(f1079,plain,(
% 1.89/0.61    $false),
% 1.89/0.61    inference(avatar_sat_refutation,[],[f116,f121,f126,f135,f138,f221,f233,f326,f488,f509,f515,f549,f700,f741,f764,f765,f891,f941,f1078])).
% 1.89/0.61  fof(f1078,plain,(
% 1.89/0.61    ~spl4_2 | ~spl4_3 | spl4_26 | ~spl4_37),
% 1.89/0.61    inference(avatar_split_clause,[],[f942,f938,f546,f123,f118])).
% 1.89/0.61  fof(f118,plain,(
% 1.89/0.61    spl4_2 <=> l1_pre_topc(sK0)),
% 1.89/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.89/0.61  fof(f123,plain,(
% 1.89/0.61    spl4_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.89/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.89/0.61  fof(f546,plain,(
% 1.89/0.61    spl4_26 <=> sK1 = k1_tops_1(sK0,sK1)),
% 1.89/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 1.89/0.61  fof(f938,plain,(
% 1.89/0.61    spl4_37 <=> sK1 = k6_subset_1(sK1,k2_tops_1(sK0,sK1))),
% 1.89/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 1.89/0.61  fof(f942,plain,(
% 1.89/0.61    sK1 = k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl4_37),
% 1.89/0.61    inference(superposition,[],[f940,f306])).
% 1.89/0.61  fof(f306,plain,(
% 1.89/0.61    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k6_subset_1(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.89/0.61    inference(duplicate_literal_removal,[],[f305])).
% 1.89/0.61  fof(f305,plain,(
% 1.89/0.61    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k6_subset_1(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.89/0.61    inference(superposition,[],[f222,f63])).
% 1.89/0.61  fof(f63,plain,(
% 1.89/0.61    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.89/0.61    inference(cnf_transformation,[],[f28])).
% 1.89/0.61  fof(f28,plain,(
% 1.89/0.61    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.89/0.61    inference(ennf_transformation,[],[f20])).
% 1.89/0.61  fof(f20,axiom,(
% 1.89/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 1.89/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 1.89/0.61  fof(f222,plain,(
% 1.89/0.61    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.89/0.61    inference(forward_demodulation,[],[f94,f101])).
% 1.89/0.61  fof(f101,plain,(
% 1.89/0.61    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k6_subset_1(X0,X1)) )),
% 1.89/0.61    inference(definition_unfolding,[],[f76,f74])).
% 1.89/0.61  fof(f74,plain,(
% 1.89/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.89/0.61    inference(cnf_transformation,[],[f5])).
% 1.89/0.61  fof(f5,axiom,(
% 1.89/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.89/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.89/0.61  fof(f76,plain,(
% 1.89/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.89/0.61    inference(cnf_transformation,[],[f11])).
% 1.89/0.61  fof(f11,axiom,(
% 1.89/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.89/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.89/0.61  fof(f94,plain,(
% 1.89/0.61    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.89/0.61    inference(definition_unfolding,[],[f61,f74])).
% 1.89/0.61  fof(f61,plain,(
% 1.89/0.61    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.89/0.61    inference(cnf_transformation,[],[f26])).
% 1.89/0.61  fof(f26,plain,(
% 1.89/0.61    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.89/0.61    inference(ennf_transformation,[],[f12])).
% 1.89/0.61  fof(f12,axiom,(
% 1.89/0.61    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 1.89/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.89/0.61  fof(f940,plain,(
% 1.89/0.61    sK1 = k6_subset_1(sK1,k2_tops_1(sK0,sK1)) | ~spl4_37),
% 1.89/0.61    inference(avatar_component_clause,[],[f938])).
% 1.89/0.61  fof(f941,plain,(
% 1.89/0.61    spl4_37 | ~spl4_36),
% 1.89/0.61    inference(avatar_split_clause,[],[f936,f888,f938])).
% 1.89/0.61  fof(f888,plain,(
% 1.89/0.61    spl4_36 <=> k1_xboole_0 = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 1.89/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 1.89/0.61  fof(f936,plain,(
% 1.89/0.61    sK1 = k6_subset_1(sK1,k2_tops_1(sK0,sK1)) | ~spl4_36),
% 1.89/0.61    inference(forward_demodulation,[],[f928,f177])).
% 1.89/0.61  fof(f177,plain,(
% 1.89/0.61    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.89/0.61    inference(forward_demodulation,[],[f103,f102])).
% 1.89/0.61  fof(f102,plain,(
% 1.89/0.61    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) )),
% 1.89/0.61    inference(definition_unfolding,[],[f77,f74])).
% 1.89/0.61  fof(f77,plain,(
% 1.89/0.61    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.89/0.61    inference(cnf_transformation,[],[f7])).
% 1.89/0.61  fof(f7,axiom,(
% 1.89/0.61    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.89/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 1.89/0.61  fof(f103,plain,(
% 1.89/0.61    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0) )),
% 1.89/0.61    inference(definition_unfolding,[],[f91,f93])).
% 1.89/0.61  fof(f93,plain,(
% 1.89/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.89/0.61    inference(definition_unfolding,[],[f75,f74])).
% 1.89/0.61  fof(f75,plain,(
% 1.89/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.89/0.61    inference(cnf_transformation,[],[f8])).
% 1.89/0.61  fof(f8,axiom,(
% 1.89/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.89/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.89/0.61  fof(f91,plain,(
% 1.89/0.61    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.89/0.61    inference(cnf_transformation,[],[f6])).
% 1.89/0.61  fof(f6,axiom,(
% 1.89/0.61    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.89/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.89/0.61  fof(f928,plain,(
% 1.89/0.61    k6_subset_1(sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_xboole_0) | ~spl4_36),
% 1.89/0.61    inference(superposition,[],[f101,f890])).
% 1.89/0.61  fof(f890,plain,(
% 1.89/0.61    k1_xboole_0 = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl4_36),
% 1.89/0.61    inference(avatar_component_clause,[],[f888])).
% 1.89/0.61  fof(f891,plain,(
% 1.89/0.61    spl4_36 | ~spl4_13),
% 1.89/0.61    inference(avatar_split_clause,[],[f886,f230,f888])).
% 1.89/0.61  fof(f230,plain,(
% 1.89/0.61    spl4_13 <=> k2_tops_1(sK0,sK1) = k6_subset_1(k2_pre_topc(sK0,sK1),sK1)),
% 1.89/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.89/0.61  fof(f886,plain,(
% 1.89/0.61    k1_xboole_0 = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl4_13),
% 1.89/0.61    inference(duplicate_literal_removal,[],[f881])).
% 1.89/0.61  fof(f881,plain,(
% 1.89/0.61    k1_xboole_0 = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | k1_xboole_0 = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl4_13),
% 1.89/0.61    inference(resolution,[],[f754,f247])).
% 1.89/0.61  fof(f247,plain,(
% 1.89/0.61    ( ! [X14,X15] : (r2_hidden(sK3(X14,X15,k1_xboole_0),X14) | k1_xboole_0 = k3_xboole_0(X14,X15)) )),
% 1.89/0.61    inference(resolution,[],[f87,f190])).
% 1.89/0.61  fof(f190,plain,(
% 1.89/0.61    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 1.89/0.61    inference(condensation,[],[f188])).
% 1.89/0.61  fof(f188,plain,(
% 1.89/0.61    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,X0)) )),
% 1.89/0.61    inference(superposition,[],[f183,f159])).
% 1.89/0.61  fof(f159,plain,(
% 1.89/0.61    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k1_xboole_0,X0)) )),
% 1.89/0.61    inference(superposition,[],[f101,f102])).
% 1.89/0.61  fof(f183,plain,(
% 1.89/0.61    ( ! [X4,X0,X1] : (~r2_hidden(X4,k6_subset_1(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 1.89/0.61    inference(forward_demodulation,[],[f105,f101])).
% 1.89/0.61  fof(f105,plain,(
% 1.89/0.61    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 1.89/0.61    inference(equality_resolution,[],[f99])).
% 1.89/0.61  fof(f99,plain,(
% 1.89/0.61    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.89/0.61    inference(definition_unfolding,[],[f69,f74])).
% 1.89/0.61  fof(f69,plain,(
% 1.89/0.61    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.89/0.61    inference(cnf_transformation,[],[f47])).
% 1.89/0.61  fof(f47,plain,(
% 1.89/0.61    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.89/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f45,f46])).
% 1.89/0.61  fof(f46,plain,(
% 1.89/0.61    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 1.89/0.61    introduced(choice_axiom,[])).
% 1.89/0.61  fof(f45,plain,(
% 1.89/0.61    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.89/0.61    inference(rectify,[],[f44])).
% 1.89/0.61  fof(f44,plain,(
% 1.89/0.61    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.89/0.61    inference(flattening,[],[f43])).
% 1.89/0.61  fof(f43,plain,(
% 1.89/0.61    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.89/0.61    inference(nnf_transformation,[],[f2])).
% 1.89/0.61  fof(f2,axiom,(
% 1.89/0.61    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.89/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.89/0.61  fof(f87,plain,(
% 1.89/0.61    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X0) | k3_xboole_0(X0,X1) = X2) )),
% 1.89/0.61    inference(cnf_transformation,[],[f55])).
% 1.89/0.61  fof(f55,plain,(
% 1.89/0.61    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.89/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f53,f54])).
% 1.89/0.61  fof(f54,plain,(
% 1.89/0.61    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.89/0.61    introduced(choice_axiom,[])).
% 1.89/0.61  fof(f53,plain,(
% 1.89/0.61    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.89/0.61    inference(rectify,[],[f52])).
% 1.89/0.61  fof(f52,plain,(
% 1.89/0.61    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.89/0.61    inference(flattening,[],[f51])).
% 1.89/0.61  fof(f51,plain,(
% 1.89/0.61    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.89/0.61    inference(nnf_transformation,[],[f1])).
% 1.89/0.61  fof(f1,axiom,(
% 1.89/0.61    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.89/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.89/0.61  fof(f754,plain,(
% 1.89/0.61    ( ! [X7] : (~r2_hidden(sK3(X7,k2_tops_1(sK0,sK1),k1_xboole_0),sK1) | k1_xboole_0 = k3_xboole_0(X7,k2_tops_1(sK0,sK1))) ) | ~spl4_13),
% 1.89/0.61    inference(resolution,[],[f746,f275])).
% 1.89/0.61  fof(f275,plain,(
% 1.89/0.61    ( ! [X14,X15] : (r2_hidden(sK3(X14,X15,k1_xboole_0),X15) | k1_xboole_0 = k3_xboole_0(X14,X15)) )),
% 1.89/0.61    inference(resolution,[],[f88,f190])).
% 1.89/0.61  fof(f88,plain,(
% 1.89/0.61    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X1) | k3_xboole_0(X0,X1) = X2) )),
% 1.89/0.61    inference(cnf_transformation,[],[f55])).
% 1.89/0.61  fof(f746,plain,(
% 1.89/0.61    ( ! [X2] : (~r2_hidden(X2,k2_tops_1(sK0,sK1)) | ~r2_hidden(X2,sK1)) ) | ~spl4_13),
% 1.89/0.61    inference(superposition,[],[f183,f232])).
% 1.89/0.61  fof(f232,plain,(
% 1.89/0.61    k2_tops_1(sK0,sK1) = k6_subset_1(k2_pre_topc(sK0,sK1),sK1) | ~spl4_13),
% 1.89/0.61    inference(avatar_component_clause,[],[f230])).
% 1.89/0.61  fof(f765,plain,(
% 1.89/0.61    sK1 != k1_tops_1(sK0,sK1) | v3_pre_topc(sK1,sK0) | ~v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 1.89/0.61    introduced(theory_tautology_sat_conflict,[])).
% 1.89/0.61  fof(f764,plain,(
% 1.89/0.61    spl4_5 | ~spl4_12 | ~spl4_13),
% 1.89/0.61    inference(avatar_contradiction_clause,[],[f762])).
% 1.89/0.61  fof(f762,plain,(
% 1.89/0.61    $false | (spl4_5 | ~spl4_12 | ~spl4_13)),
% 1.89/0.61    inference(subsumption_resolution,[],[f227,f761])).
% 1.89/0.61  fof(f761,plain,(
% 1.89/0.61    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (spl4_5 | ~spl4_13)),
% 1.89/0.61    inference(trivial_inequality_removal,[],[f760])).
% 1.89/0.61  fof(f760,plain,(
% 1.89/0.61    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (spl4_5 | ~spl4_13)),
% 1.89/0.61    inference(forward_demodulation,[],[f358,f232])).
% 1.89/0.61  fof(f358,plain,(
% 1.89/0.61    k2_tops_1(sK0,sK1) != k6_subset_1(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_5),
% 1.89/0.61    inference(superposition,[],[f133,f222])).
% 1.89/0.61  fof(f133,plain,(
% 1.89/0.61    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | spl4_5),
% 1.89/0.61    inference(avatar_component_clause,[],[f132])).
% 1.89/0.61  fof(f132,plain,(
% 1.89/0.61    spl4_5 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 1.89/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.89/0.61  fof(f227,plain,(
% 1.89/0.61    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_12),
% 1.89/0.61    inference(avatar_component_clause,[],[f226])).
% 1.89/0.61  fof(f226,plain,(
% 1.89/0.61    spl4_12 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.89/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.89/0.61  fof(f741,plain,(
% 1.89/0.61    ~spl4_2 | ~spl4_3 | spl4_13 | ~spl4_26),
% 1.89/0.61    inference(avatar_split_clause,[],[f714,f546,f230,f123,f118])).
% 1.89/0.61  fof(f714,plain,(
% 1.89/0.61    k2_tops_1(sK0,sK1) = k6_subset_1(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl4_26),
% 1.89/0.61    inference(superposition,[],[f464,f548])).
% 1.89/0.61  fof(f548,plain,(
% 1.89/0.61    sK1 = k1_tops_1(sK0,sK1) | ~spl4_26),
% 1.89/0.61    inference(avatar_component_clause,[],[f546])).
% 1.89/0.61  fof(f464,plain,(
% 1.89/0.61    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k6_subset_1(k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.89/0.61    inference(global_subsumption,[],[f317,f463])).
% 1.89/0.61  fof(f463,plain,(
% 1.89/0.61    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k6_subset_1(k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.89/0.61    inference(superposition,[],[f222,f62])).
% 1.89/0.61  fof(f62,plain,(
% 1.89/0.61    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.89/0.61    inference(cnf_transformation,[],[f27])).
% 1.89/0.61  fof(f27,plain,(
% 1.89/0.61    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.89/0.61    inference(ennf_transformation,[],[f17])).
% 1.89/0.61  fof(f17,axiom,(
% 1.89/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 1.89/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 1.89/0.61  fof(f317,plain,(
% 1.89/0.61    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.89/0.61    inference(global_subsumption,[],[f65,f316])).
% 1.89/0.61  fof(f316,plain,(
% 1.89/0.61    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.89/0.61    inference(duplicate_literal_removal,[],[f315])).
% 1.89/0.61  fof(f315,plain,(
% 1.89/0.61    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.89/0.61    inference(superposition,[],[f78,f64])).
% 1.89/0.61  fof(f64,plain,(
% 1.89/0.61    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.89/0.61    inference(cnf_transformation,[],[f29])).
% 1.89/0.61  fof(f29,plain,(
% 1.89/0.61    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.89/0.61    inference(ennf_transformation,[],[f19])).
% 1.89/0.61  fof(f19,axiom,(
% 1.89/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 1.89/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 1.89/0.61  fof(f78,plain,(
% 1.89/0.61    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.89/0.61    inference(cnf_transformation,[],[f37])).
% 1.89/0.61  fof(f37,plain,(
% 1.89/0.61    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.89/0.61    inference(flattening,[],[f36])).
% 1.89/0.61  fof(f36,plain,(
% 1.89/0.61    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.89/0.61    inference(ennf_transformation,[],[f9])).
% 1.89/0.61  fof(f9,axiom,(
% 1.89/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 1.89/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 1.89/0.61  fof(f65,plain,(
% 1.89/0.61    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.89/0.61    inference(cnf_transformation,[],[f31])).
% 1.89/0.61  fof(f31,plain,(
% 1.89/0.61    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.89/0.61    inference(flattening,[],[f30])).
% 1.89/0.61  fof(f30,plain,(
% 1.89/0.61    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.89/0.61    inference(ennf_transformation,[],[f15])).
% 1.89/0.61  fof(f15,axiom,(
% 1.89/0.61    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.89/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 1.89/0.61  fof(f700,plain,(
% 1.89/0.61    ~spl4_2 | ~spl4_3 | spl4_25),
% 1.89/0.61    inference(avatar_contradiction_clause,[],[f687])).
% 1.89/0.61  fof(f687,plain,(
% 1.89/0.61    $false | (~spl4_2 | ~spl4_3 | spl4_25)),
% 1.89/0.61    inference(unit_resulting_resolution,[],[f120,f544,f125,f653])).
% 1.89/0.61  fof(f653,plain,(
% 1.89/0.61    ( ! [X12,X11] : (~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X12))) | r1_tarski(k1_tops_1(X12,X11),X11) | ~l1_pre_topc(X12)) )),
% 1.89/0.61    inference(superposition,[],[f140,f306])).
% 1.89/0.61  fof(f140,plain,(
% 1.89/0.61    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 1.89/0.61    inference(resolution,[],[f79,f92])).
% 1.89/0.61  fof(f92,plain,(
% 1.89/0.61    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 1.89/0.61    inference(cnf_transformation,[],[f10])).
% 1.89/0.62  fof(f10,axiom,(
% 1.89/0.62    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 1.89/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 1.89/0.62  fof(f79,plain,(
% 1.89/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f48])).
% 1.89/0.62  fof(f48,plain,(
% 1.89/0.62    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.89/0.62    inference(nnf_transformation,[],[f14])).
% 1.89/0.62  fof(f14,axiom,(
% 1.89/0.62    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.89/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.89/0.62  fof(f125,plain,(
% 1.89/0.62    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_3),
% 1.89/0.62    inference(avatar_component_clause,[],[f123])).
% 1.89/0.62  fof(f544,plain,(
% 1.89/0.62    ~r1_tarski(k1_tops_1(sK0,sK1),sK1) | spl4_25),
% 1.89/0.62    inference(avatar_component_clause,[],[f542])).
% 1.89/0.62  fof(f542,plain,(
% 1.89/0.62    spl4_25 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 1.89/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 1.89/0.62  fof(f120,plain,(
% 1.89/0.62    l1_pre_topc(sK0) | ~spl4_2),
% 1.89/0.62    inference(avatar_component_clause,[],[f118])).
% 1.89/0.62  fof(f549,plain,(
% 1.89/0.62    ~spl4_25 | spl4_26 | ~spl4_23),
% 1.89/0.62    inference(avatar_split_clause,[],[f540,f502,f546,f542])).
% 1.89/0.62  fof(f502,plain,(
% 1.89/0.62    spl4_23 <=> r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 1.89/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 1.89/0.62  fof(f540,plain,(
% 1.89/0.62    sK1 = k1_tops_1(sK0,sK1) | ~r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl4_23),
% 1.89/0.62    inference(resolution,[],[f504,f83])).
% 1.89/0.62  fof(f83,plain,(
% 1.89/0.62    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f50])).
% 1.89/0.62  fof(f50,plain,(
% 1.89/0.62    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.89/0.62    inference(flattening,[],[f49])).
% 1.89/0.62  fof(f49,plain,(
% 1.89/0.62    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.89/0.62    inference(nnf_transformation,[],[f4])).
% 1.89/0.62  fof(f4,axiom,(
% 1.89/0.62    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.89/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.89/0.62  fof(f504,plain,(
% 1.89/0.62    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~spl4_23),
% 1.89/0.62    inference(avatar_component_clause,[],[f502])).
% 1.89/0.62  fof(f515,plain,(
% 1.89/0.62    spl4_24),
% 1.89/0.62    inference(avatar_contradiction_clause,[],[f511])).
% 1.89/0.62  fof(f511,plain,(
% 1.89/0.62    $false | spl4_24),
% 1.89/0.62    inference(unit_resulting_resolution,[],[f298,f508,f79])).
% 1.89/0.62  fof(f508,plain,(
% 1.89/0.62    ~r1_tarski(sK1,sK1) | spl4_24),
% 1.89/0.62    inference(avatar_component_clause,[],[f506])).
% 1.89/0.62  fof(f506,plain,(
% 1.89/0.62    spl4_24 <=> r1_tarski(sK1,sK1)),
% 1.89/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 1.89/0.62  fof(f298,plain,(
% 1.89/0.62    ( ! [X8] : (m1_subset_1(X8,k1_zfmisc_1(X8))) )),
% 1.89/0.62    inference(superposition,[],[f92,f291])).
% 1.89/0.62  fof(f291,plain,(
% 1.89/0.62    ( ! [X2] : (k6_subset_1(X2,k1_xboole_0) = X2) )),
% 1.89/0.62    inference(forward_demodulation,[],[f288,f177])).
% 1.89/0.62  fof(f288,plain,(
% 1.89/0.62    ( ! [X2] : (k6_subset_1(X2,k1_xboole_0) = k5_xboole_0(X2,k1_xboole_0)) )),
% 1.89/0.62    inference(superposition,[],[f101,f283])).
% 1.89/0.62  fof(f283,plain,(
% 1.89/0.62    ( ! [X10] : (k1_xboole_0 = k3_xboole_0(X10,k1_xboole_0)) )),
% 1.89/0.62    inference(resolution,[],[f278,f190])).
% 1.89/0.62  fof(f278,plain,(
% 1.89/0.62    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,X1),X1) | k3_xboole_0(X0,X1) = X1) )),
% 1.89/0.62    inference(factoring,[],[f88])).
% 1.89/0.62  fof(f509,plain,(
% 1.89/0.62    ~spl4_4 | spl4_23 | ~spl4_24 | ~spl4_3 | ~spl4_22),
% 1.89/0.62    inference(avatar_split_clause,[],[f498,f486,f123,f506,f502,f128])).
% 1.89/0.62  fof(f128,plain,(
% 1.89/0.62    spl4_4 <=> v3_pre_topc(sK1,sK0)),
% 1.89/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.89/0.62  fof(f486,plain,(
% 1.89/0.62    spl4_22 <=> ! [X23] : (~r1_tarski(X23,sK1) | ~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X23,k1_tops_1(sK0,sK1)) | ~v3_pre_topc(X23,sK0))),
% 1.89/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 1.89/0.62  fof(f498,plain,(
% 1.89/0.62    ~r1_tarski(sK1,sK1) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~v3_pre_topc(sK1,sK0) | (~spl4_3 | ~spl4_22)),
% 1.89/0.62    inference(resolution,[],[f487,f125])).
% 1.89/0.62  fof(f487,plain,(
% 1.89/0.62    ( ! [X23] : (~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X23,sK1) | r1_tarski(X23,k1_tops_1(sK0,sK1)) | ~v3_pre_topc(X23,sK0)) ) | ~spl4_22),
% 1.89/0.62    inference(avatar_component_clause,[],[f486])).
% 1.89/0.62  fof(f488,plain,(
% 1.89/0.62    ~spl4_2 | spl4_22 | ~spl4_3),
% 1.89/0.62    inference(avatar_split_clause,[],[f480,f123,f486,f118])).
% 1.89/0.62  fof(f480,plain,(
% 1.89/0.62    ( ! [X23] : (~r1_tarski(X23,sK1) | ~v3_pre_topc(X23,sK0) | r1_tarski(X23,k1_tops_1(sK0,sK1)) | ~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl4_3),
% 1.89/0.62    inference(resolution,[],[f67,f125])).
% 1.89/0.62  fof(f67,plain,(
% 1.89/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f35])).
% 1.89/0.62  fof(f35,plain,(
% 1.89/0.62    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.89/0.62    inference(flattening,[],[f34])).
% 1.89/0.62  fof(f34,plain,(
% 1.89/0.62    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.89/0.62    inference(ennf_transformation,[],[f18])).
% 1.89/0.62  fof(f18,axiom,(
% 1.89/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 1.89/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).
% 1.89/0.62  fof(f326,plain,(
% 1.89/0.62    ~spl4_2 | ~spl4_3 | spl4_12),
% 1.89/0.62    inference(avatar_contradiction_clause,[],[f321])).
% 1.89/0.62  fof(f321,plain,(
% 1.89/0.62    $false | (~spl4_2 | ~spl4_3 | spl4_12)),
% 1.89/0.62    inference(unit_resulting_resolution,[],[f120,f125,f228,f317])).
% 1.89/0.62  fof(f228,plain,(
% 1.89/0.62    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_12),
% 1.89/0.62    inference(avatar_component_clause,[],[f226])).
% 1.89/0.62  fof(f233,plain,(
% 1.89/0.62    ~spl4_12 | spl4_13 | ~spl4_5),
% 1.89/0.62    inference(avatar_split_clause,[],[f223,f132,f230,f226])).
% 1.89/0.62  fof(f223,plain,(
% 1.89/0.62    k2_tops_1(sK0,sK1) = k6_subset_1(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_5),
% 1.89/0.62    inference(superposition,[],[f222,f134])).
% 1.89/0.62  fof(f134,plain,(
% 1.89/0.62    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl4_5),
% 1.89/0.62    inference(avatar_component_clause,[],[f132])).
% 1.89/0.62  fof(f221,plain,(
% 1.89/0.62    ~spl4_1 | ~spl4_2 | spl4_11 | ~spl4_3),
% 1.89/0.62    inference(avatar_split_clause,[],[f215,f123,f218,f118,f113])).
% 1.89/0.62  fof(f113,plain,(
% 1.89/0.62    spl4_1 <=> v2_pre_topc(sK0)),
% 1.89/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.89/0.62  fof(f218,plain,(
% 1.89/0.62    spl4_11 <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 1.89/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.89/0.62  fof(f215,plain,(
% 1.89/0.62    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl4_3),
% 1.89/0.62    inference(resolution,[],[f66,f125])).
% 1.89/0.62  fof(f66,plain,(
% 1.89/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k1_tops_1(X0,X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f33])).
% 1.89/0.62  fof(f33,plain,(
% 1.89/0.62    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.89/0.62    inference(flattening,[],[f32])).
% 1.89/0.62  fof(f32,plain,(
% 1.89/0.62    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.89/0.62    inference(ennf_transformation,[],[f16])).
% 1.89/0.62  fof(f16,axiom,(
% 1.89/0.62    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 1.89/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 1.89/0.62  fof(f138,plain,(
% 1.89/0.62    ~spl4_4 | ~spl4_5),
% 1.89/0.62    inference(avatar_split_clause,[],[f137,f132,f128])).
% 1.89/0.62  fof(f137,plain,(
% 1.89/0.62    ~v3_pre_topc(sK1,sK0) | ~spl4_5),
% 1.89/0.62    inference(trivial_inequality_removal,[],[f136])).
% 1.89/0.62  fof(f136,plain,(
% 1.89/0.62    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0) | ~spl4_5),
% 1.89/0.62    inference(forward_demodulation,[],[f60,f134])).
% 1.89/0.62  fof(f60,plain,(
% 1.89/0.62    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 1.89/0.62    inference(cnf_transformation,[],[f42])).
% 1.89/0.62  fof(f42,plain,(
% 1.89/0.62    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 1.89/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f39,f41,f40])).
% 1.89/0.62  fof(f40,plain,(
% 1.89/0.62    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 1.89/0.62    introduced(choice_axiom,[])).
% 1.89/0.62  fof(f41,plain,(
% 1.89/0.62    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.89/0.62    introduced(choice_axiom,[])).
% 1.89/0.62  fof(f39,plain,(
% 1.89/0.62    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.89/0.62    inference(flattening,[],[f38])).
% 1.89/0.62  fof(f38,plain,(
% 1.89/0.62    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.89/0.62    inference(nnf_transformation,[],[f25])).
% 1.89/0.62  fof(f25,plain,(
% 1.89/0.62    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.89/0.62    inference(flattening,[],[f24])).
% 1.89/0.62  fof(f24,plain,(
% 1.89/0.62    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.89/0.62    inference(ennf_transformation,[],[f22])).
% 1.89/0.62  fof(f22,negated_conjecture,(
% 1.89/0.62    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 1.89/0.62    inference(negated_conjecture,[],[f21])).
% 1.89/0.62  fof(f21,conjecture,(
% 1.89/0.62    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 1.89/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).
% 1.89/0.62  fof(f135,plain,(
% 1.89/0.62    spl4_4 | spl4_5),
% 1.89/0.62    inference(avatar_split_clause,[],[f59,f132,f128])).
% 1.89/0.62  fof(f59,plain,(
% 1.89/0.62    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 1.89/0.62    inference(cnf_transformation,[],[f42])).
% 1.89/0.62  fof(f126,plain,(
% 1.89/0.62    spl4_3),
% 1.89/0.62    inference(avatar_split_clause,[],[f58,f123])).
% 1.89/0.62  fof(f58,plain,(
% 1.89/0.62    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.89/0.62    inference(cnf_transformation,[],[f42])).
% 1.89/0.62  fof(f121,plain,(
% 1.89/0.62    spl4_2),
% 1.89/0.62    inference(avatar_split_clause,[],[f57,f118])).
% 1.89/0.62  fof(f57,plain,(
% 1.89/0.62    l1_pre_topc(sK0)),
% 1.89/0.62    inference(cnf_transformation,[],[f42])).
% 1.89/0.62  fof(f116,plain,(
% 1.89/0.62    spl4_1),
% 1.89/0.62    inference(avatar_split_clause,[],[f56,f113])).
% 1.89/0.62  fof(f56,plain,(
% 1.89/0.62    v2_pre_topc(sK0)),
% 1.89/0.62    inference(cnf_transformation,[],[f42])).
% 1.89/0.62  % SZS output end Proof for theBenchmark
% 1.89/0.62  % (11938)------------------------------
% 1.89/0.62  % (11938)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.89/0.62  % (11938)Termination reason: Refutation
% 1.89/0.62  
% 1.89/0.62  % (11938)Memory used [KB]: 11641
% 1.89/0.62  % (11938)Time elapsed: 0.185 s
% 1.89/0.62  % (11938)------------------------------
% 1.89/0.62  % (11938)------------------------------
% 1.89/0.62  % (11914)Success in time 0.261 s
%------------------------------------------------------------------------------
