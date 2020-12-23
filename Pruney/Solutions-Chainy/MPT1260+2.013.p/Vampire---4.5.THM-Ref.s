%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:34 EST 2020

% Result     : Theorem 9.99s
% Output     : Refutation 9.99s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 286 expanded)
%              Number of leaves         :   27 (  99 expanded)
%              Depth                    :   14
%              Number of atoms          :  521 (1262 expanded)
%              Number of equality atoms :   83 ( 228 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12922,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f115,f116,f121,f126,f131,f217,f229,f1218,f1630,f1767,f1772,f1773,f1780,f9705,f12843,f12921])).

fof(f12921,plain,
    ( ~ spl4_3
    | ~ spl4_4
    | spl4_51
    | ~ spl4_194 ),
    inference(avatar_contradiction_clause,[],[f12920])).

fof(f12920,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_4
    | spl4_51
    | ~ spl4_194 ),
    inference(subsumption_resolution,[],[f12919,f125])).

fof(f125,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl4_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f12919,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_3
    | spl4_51
    | ~ spl4_194 ),
    inference(subsumption_resolution,[],[f12918,f120])).

fof(f120,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl4_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f12918,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl4_51
    | ~ spl4_194 ),
    inference(subsumption_resolution,[],[f12856,f1213])).

fof(f1213,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | spl4_51 ),
    inference(avatar_component_clause,[],[f1212])).

fof(f1212,plain,
    ( spl4_51
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).

fof(f12856,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_194 ),
    inference(superposition,[],[f282,f12842])).

fof(f12842,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl4_194 ),
    inference(avatar_component_clause,[],[f12840])).

fof(f12840,plain,
    ( spl4_194
  <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_194])])).

fof(f282,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f281])).

fof(f281,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f64,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f12843,plain,
    ( spl4_194
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f12838,f200,f12840])).

fof(f200,plain,
    ( spl4_10
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f12838,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl4_10 ),
    inference(duplicate_literal_removal,[],[f12812])).

fof(f12812,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl4_10 ),
    inference(resolution,[],[f1817,f238])).

fof(f238,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1,X0),X0)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(factoring,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f51,f52])).

fof(f52,plain,(
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

fof(f51,plain,(
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
    inference(rectify,[],[f50])).

fof(f50,plain,(
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
    inference(flattening,[],[f49])).

fof(f49,plain,(
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

fof(f1817,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK2(X1,k2_tops_1(sK0,sK1),X1),sK1)
        | k4_xboole_0(X1,k2_tops_1(sK0,sK1)) = X1 )
    | ~ spl4_10 ),
    inference(resolution,[],[f1786,f448])).

fof(f448,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK2(X1,X2,X1),X2)
      | k4_xboole_0(X1,X2) = X1 ) ),
    inference(subsumption_resolution,[],[f446,f83])).

fof(f446,plain,(
    ! [X2,X1] :
      ( k4_xboole_0(X1,X2) = X1
      | r2_hidden(sK2(X1,X2,X1),X2)
      | ~ r2_hidden(sK2(X1,X2,X1),X1) ) ),
    inference(duplicate_literal_removal,[],[f439])).

fof(f439,plain,(
    ! [X2,X1] :
      ( k4_xboole_0(X1,X2) = X1
      | r2_hidden(sK2(X1,X2,X1),X2)
      | ~ r2_hidden(sK2(X1,X2,X1),X1)
      | k4_xboole_0(X1,X2) = X1 ) ),
    inference(resolution,[],[f238,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f1786,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_tops_1(sK0,sK1))
        | ~ r2_hidden(X1,sK1) )
    | ~ spl4_10 ),
    inference(superposition,[],[f102,f202])).

fof(f202,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f200])).

fof(f102,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f9705,plain,
    ( spl4_6
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f9697,f118,f135])).

fof(f135,plain,
    ( spl4_6
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f9697,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl4_3 ),
    inference(resolution,[],[f120,f77])).

% (31229)Time limit reached!
% (31229)------------------------------
% (31229)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

% (31229)Termination reason: Time limit
fof(f48,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f16])).

% (31229)Termination phase: Saturation

% (31229)Memory used [KB]: 3326
fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

% (31229)Time elapsed: 1.200 s
% (31229)------------------------------
% (31229)------------------------------
fof(f1780,plain,
    ( spl4_10
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f1779,f196,f112,f200])).

fof(f112,plain,
    ( spl4_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f196,plain,
    ( spl4_9
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f1779,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f1776,f197])).

fof(f197,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f196])).

fof(f1776,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_2 ),
    inference(superposition,[],[f64,f113])).

fof(f113,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f112])).

fof(f1773,plain,
    ( ~ spl4_1
    | spl4_51
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_50 ),
    inference(avatar_split_clause,[],[f1640,f1208,f135,f123,f118,f1212,f108])).

fof(f108,plain,
    ( spl4_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f1208,plain,
    ( spl4_50
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f1640,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_50 ),
    inference(subsumption_resolution,[],[f1639,f137])).

fof(f137,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f135])).

fof(f1639,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | sK1 = k1_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_50 ),
    inference(subsumption_resolution,[],[f1636,f99])).

fof(f99,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1636,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ r1_tarski(sK1,u1_struct_0(sK0))
    | sK1 = k1_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_50 ),
    inference(resolution,[],[f1209,f507])).

fof(f507,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k1_tops_1(sK0,sK1),X2)
        | ~ r1_tarski(X2,sK1)
        | ~ r1_tarski(X2,u1_struct_0(sK0))
        | k1_tops_1(sK0,sK1) = X2
        | ~ v3_pre_topc(X2,sK0) )
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(resolution,[],[f333,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f333,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k1_tops_1(sK0,sK1))
        | ~ v3_pre_topc(X0,sK0)
        | ~ r1_tarski(X0,sK1)
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(resolution,[],[f297,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f297,plain,
    ( ! [X10] :
        ( ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X10,sK0)
        | r1_tarski(X10,k1_tops_1(sK0,sK1))
        | ~ r1_tarski(X10,sK1) )
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f294,f125])).

fof(f294,plain,
    ( ! [X10] :
        ( ~ r1_tarski(X10,sK1)
        | ~ v3_pre_topc(X10,sK0)
        | r1_tarski(X10,k1_tops_1(sK0,sK1))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl4_3 ),
    inference(resolution,[],[f76,f120])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
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

fof(f1209,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl4_50 ),
    inference(avatar_component_clause,[],[f1208])).

fof(f1772,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1767,plain,
    ( ~ spl4_3
    | ~ spl4_4
    | spl4_10
    | ~ spl4_51 ),
    inference(avatar_contradiction_clause,[],[f1766])).

fof(f1766,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_4
    | spl4_10
    | ~ spl4_51 ),
    inference(subsumption_resolution,[],[f1765,f125])).

fof(f1765,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_3
    | spl4_10
    | ~ spl4_51 ),
    inference(subsumption_resolution,[],[f1764,f120])).

fof(f1764,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl4_10
    | ~ spl4_51 ),
    inference(subsumption_resolution,[],[f1760,f201])).

fof(f201,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f200])).

fof(f1760,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_51 ),
    inference(superposition,[],[f288,f1214])).

fof(f1214,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl4_51 ),
    inference(avatar_component_clause,[],[f1212])).

fof(f288,plain,(
    ! [X2,X3] :
      ( k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f286,f74])).

fof(f74,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f286,plain,(
    ! [X2,X3] :
      ( k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f73,f64])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f1630,plain,
    ( spl4_50
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f1629,f123,f118,f1208])).

fof(f1629,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f1620,f125])).

fof(f1620,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f485,f120])).

fof(f485,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
      | r1_tarski(k1_tops_1(X3,X2),X2)
      | ~ l1_pre_topc(X3) ) ),
    inference(superposition,[],[f88,f282])).

fof(f88,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f1218,plain,
    ( ~ spl4_10
    | spl4_2
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f1217,f196,f112,f200])).

fof(f1217,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | spl4_2
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f1216,f197])).

fof(f1216,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_2 ),
    inference(superposition,[],[f114,f64])).

fof(f114,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f112])).

fof(f229,plain,
    ( spl4_12
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f224,f128,f123,f118,f226])).

fof(f226,plain,
    ( spl4_12
  <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f128,plain,
    ( spl4_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f224,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f223,f130])).

fof(f130,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f128])).

fof(f223,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f221,f125])).

fof(f221,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f75,f120])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f217,plain,
    ( ~ spl4_3
    | ~ spl4_4
    | spl4_9 ),
    inference(avatar_contradiction_clause,[],[f216])).

fof(f216,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_4
    | spl4_9 ),
    inference(subsumption_resolution,[],[f215,f125])).

fof(f215,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_3
    | spl4_9 ),
    inference(subsumption_resolution,[],[f212,f120])).

fof(f212,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl4_9 ),
    inference(resolution,[],[f74,f198])).

fof(f198,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f196])).

fof(f131,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f59,f128])).

fof(f59,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f42,f44,f43])).

fof(f43,plain,
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

fof(f44,plain,
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

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

fof(f126,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f60,f123])).

fof(f60,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f121,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f61,f118])).

fof(f61,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f116,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f62,f112,f108])).

fof(f62,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f115,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f63,f112,f108])).

fof(f63,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:46:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (31248)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.51  % (31231)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (31240)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.51  % (31238)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.51  % (31241)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (31232)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (31237)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (31239)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % (31246)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.53  % (31239)Refutation not found, incomplete strategy% (31239)------------------------------
% 0.21/0.53  % (31239)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (31233)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (31258)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (31250)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.53  % (31252)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (31229)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (31244)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (31242)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.54  % (31234)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.55  % (31254)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (31239)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (31239)Memory used [KB]: 10874
% 0.21/0.55  % (31239)Time elapsed: 0.118 s
% 0.21/0.55  % (31239)------------------------------
% 0.21/0.55  % (31239)------------------------------
% 0.21/0.55  % (31230)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.55  % (31257)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.48/0.55  % (31253)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.48/0.55  % (31249)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.48/0.56  % (31245)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.48/0.56  % (31243)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.48/0.56  % (31245)Refutation not found, incomplete strategy% (31245)------------------------------
% 1.48/0.56  % (31245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.56  % (31245)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.56  
% 1.48/0.56  % (31245)Memory used [KB]: 10746
% 1.48/0.56  % (31245)Time elapsed: 0.160 s
% 1.48/0.56  % (31245)------------------------------
% 1.48/0.56  % (31245)------------------------------
% 1.48/0.56  % (31247)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.48/0.56  % (31235)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.48/0.56  % (31256)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.48/0.56  % (31255)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.62/0.57  % (31236)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.62/0.57  % (31257)Refutation not found, incomplete strategy% (31257)------------------------------
% 1.62/0.57  % (31257)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.57  % (31257)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.57  
% 1.62/0.57  % (31257)Memory used [KB]: 10746
% 1.62/0.57  % (31257)Time elapsed: 0.170 s
% 1.62/0.57  % (31257)------------------------------
% 1.62/0.57  % (31257)------------------------------
% 1.62/0.57  % (31251)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 2.24/0.68  % (31259)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.24/0.70  % (31260)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 3.03/0.80  % (31261)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 3.03/0.80  % (31253)Time limit reached!
% 3.03/0.80  % (31253)------------------------------
% 3.03/0.80  % (31253)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.03/0.82  % (31253)Termination reason: Time limit
% 3.03/0.82  % (31253)Termination phase: Saturation
% 3.03/0.82  
% 3.03/0.82  % (31253)Memory used [KB]: 13176
% 3.03/0.82  % (31253)Time elapsed: 0.400 s
% 3.03/0.82  % (31253)------------------------------
% 3.03/0.82  % (31253)------------------------------
% 3.03/0.84  % (31231)Time limit reached!
% 3.03/0.84  % (31231)------------------------------
% 3.03/0.84  % (31231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.03/0.84  % (31231)Termination reason: Time limit
% 3.03/0.84  
% 3.03/0.84  % (31231)Memory used [KB]: 6780
% 3.03/0.84  % (31231)Time elapsed: 0.413 s
% 3.03/0.84  % (31231)------------------------------
% 3.03/0.84  % (31231)------------------------------
% 3.73/0.90  % (31235)Time limit reached!
% 3.73/0.90  % (31235)------------------------------
% 3.73/0.90  % (31235)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.73/0.90  % (31235)Termination reason: Time limit
% 3.73/0.90  % (31235)Termination phase: Saturation
% 3.73/0.90  
% 3.73/0.90  % (31235)Memory used [KB]: 14072
% 3.73/0.90  % (31235)Time elapsed: 0.500 s
% 3.73/0.90  % (31235)------------------------------
% 3.73/0.90  % (31235)------------------------------
% 3.73/0.91  % (31243)Time limit reached!
% 3.73/0.91  % (31243)------------------------------
% 3.73/0.91  % (31243)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.73/0.91  % (31243)Termination reason: Time limit
% 3.73/0.91  % (31243)Termination phase: Saturation
% 3.73/0.91  
% 3.73/0.91  % (31243)Memory used [KB]: 4605
% 3.73/0.91  % (31243)Time elapsed: 0.500 s
% 3.73/0.91  % (31243)------------------------------
% 3.73/0.91  % (31243)------------------------------
% 4.11/0.94  % (31258)Time limit reached!
% 4.11/0.94  % (31258)------------------------------
% 4.11/0.94  % (31258)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.11/0.94  % (31258)Termination reason: Time limit
% 4.11/0.94  
% 4.11/0.94  % (31258)Memory used [KB]: 5756
% 4.11/0.94  % (31258)Time elapsed: 0.502 s
% 4.11/0.94  % (31258)------------------------------
% 4.11/0.94  % (31258)------------------------------
% 4.32/0.96  % (31262)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 4.32/0.96  % (31263)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 4.74/1.03  % (31236)Time limit reached!
% 4.74/1.03  % (31236)------------------------------
% 4.74/1.03  % (31236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.74/1.03  % (31236)Termination reason: Time limit
% 4.74/1.03  
% 4.74/1.03  % (31236)Memory used [KB]: 4221
% 4.74/1.03  % (31236)Time elapsed: 0.620 s
% 4.74/1.03  % (31236)------------------------------
% 4.74/1.03  % (31236)------------------------------
% 4.74/1.04  % (31265)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 4.74/1.06  % (31264)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 4.74/1.07  % (31266)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 6.18/1.15  % (31267)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 6.37/1.22  % (31230)Time limit reached!
% 6.37/1.22  % (31230)------------------------------
% 6.37/1.22  % (31230)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.37/1.22  % (31230)Termination reason: Time limit
% 6.37/1.22  % (31230)Termination phase: Saturation
% 6.37/1.22  
% 6.37/1.22  % (31230)Memory used [KB]: 5245
% 6.37/1.22  % (31230)Time elapsed: 0.800 s
% 6.37/1.22  % (31230)------------------------------
% 6.37/1.22  % (31230)------------------------------
% 7.52/1.32  % (31232)Time limit reached!
% 7.52/1.32  % (31232)------------------------------
% 7.52/1.32  % (31232)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.52/1.32  % (31232)Termination reason: Time limit
% 7.52/1.32  % (31232)Termination phase: Saturation
% 7.52/1.32  
% 7.52/1.32  % (31232)Memory used [KB]: 7419
% 7.52/1.32  % (31232)Time elapsed: 0.900 s
% 7.52/1.32  % (31232)------------------------------
% 7.52/1.32  % (31232)------------------------------
% 7.52/1.34  % (31268)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 7.91/1.41  % (31241)Time limit reached!
% 7.91/1.41  % (31241)------------------------------
% 7.91/1.41  % (31241)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.91/1.41  % (31241)Termination reason: Time limit
% 7.91/1.41  % (31241)Termination phase: Saturation
% 7.91/1.41  
% 7.91/1.41  % (31241)Memory used [KB]: 17910
% 7.91/1.41  % (31241)Time elapsed: 1.0000 s
% 7.91/1.41  % (31241)------------------------------
% 7.91/1.41  % (31241)------------------------------
% 7.91/1.44  % (31256)Time limit reached!
% 7.91/1.44  % (31256)------------------------------
% 7.91/1.44  % (31256)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.91/1.44  % (31269)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 7.91/1.44  % (31261)Time limit reached!
% 7.91/1.44  % (31261)------------------------------
% 7.91/1.44  % (31261)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.91/1.44  % (31261)Termination reason: Time limit
% 7.91/1.44  % (31261)Termination phase: Saturation
% 7.91/1.44  
% 7.91/1.44  % (31261)Memory used [KB]: 8827
% 7.91/1.44  % (31261)Time elapsed: 0.800 s
% 7.91/1.44  % (31261)------------------------------
% 7.91/1.44  % (31261)------------------------------
% 7.91/1.45  % (31256)Termination reason: Time limit
% 7.91/1.45  
% 7.91/1.45  % (31256)Memory used [KB]: 36587
% 7.91/1.45  % (31256)Time elapsed: 1.013 s
% 7.91/1.45  % (31256)------------------------------
% 7.91/1.45  % (31256)------------------------------
% 9.04/1.53  % (31265)Time limit reached!
% 9.04/1.53  % (31265)------------------------------
% 9.04/1.53  % (31265)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.04/1.53  % (31265)Termination reason: Time limit
% 9.04/1.53  % (31265)Termination phase: Saturation
% 9.04/1.53  
% 9.04/1.53  % (31265)Memory used [KB]: 15863
% 9.04/1.53  % (31265)Time elapsed: 0.600 s
% 9.04/1.53  % (31265)------------------------------
% 9.04/1.53  % (31265)------------------------------
% 9.17/1.55  % (31276)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 9.17/1.55  % (31291)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 9.17/1.59  % (31296)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 9.99/1.63  % (31250)Refutation found. Thanks to Tanya!
% 9.99/1.63  % SZS status Theorem for theBenchmark
% 9.99/1.63  % SZS output start Proof for theBenchmark
% 9.99/1.63  fof(f12922,plain,(
% 9.99/1.63    $false),
% 9.99/1.63    inference(avatar_sat_refutation,[],[f115,f116,f121,f126,f131,f217,f229,f1218,f1630,f1767,f1772,f1773,f1780,f9705,f12843,f12921])).
% 9.99/1.63  fof(f12921,plain,(
% 9.99/1.63    ~spl4_3 | ~spl4_4 | spl4_51 | ~spl4_194),
% 9.99/1.63    inference(avatar_contradiction_clause,[],[f12920])).
% 9.99/1.63  fof(f12920,plain,(
% 9.99/1.63    $false | (~spl4_3 | ~spl4_4 | spl4_51 | ~spl4_194)),
% 9.99/1.63    inference(subsumption_resolution,[],[f12919,f125])).
% 9.99/1.63  fof(f125,plain,(
% 9.99/1.63    l1_pre_topc(sK0) | ~spl4_4),
% 9.99/1.63    inference(avatar_component_clause,[],[f123])).
% 9.99/1.63  fof(f123,plain,(
% 9.99/1.63    spl4_4 <=> l1_pre_topc(sK0)),
% 9.99/1.63    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 9.99/1.63  fof(f12919,plain,(
% 9.99/1.63    ~l1_pre_topc(sK0) | (~spl4_3 | spl4_51 | ~spl4_194)),
% 9.99/1.63    inference(subsumption_resolution,[],[f12918,f120])).
% 9.99/1.63  fof(f120,plain,(
% 9.99/1.63    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_3),
% 9.99/1.63    inference(avatar_component_clause,[],[f118])).
% 9.99/1.63  fof(f118,plain,(
% 9.99/1.63    spl4_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 9.99/1.63    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 9.99/1.63  fof(f12918,plain,(
% 9.99/1.63    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl4_51 | ~spl4_194)),
% 9.99/1.63    inference(subsumption_resolution,[],[f12856,f1213])).
% 9.99/1.63  fof(f1213,plain,(
% 9.99/1.63    sK1 != k1_tops_1(sK0,sK1) | spl4_51),
% 9.99/1.63    inference(avatar_component_clause,[],[f1212])).
% 9.99/1.63  fof(f1212,plain,(
% 9.99/1.63    spl4_51 <=> sK1 = k1_tops_1(sK0,sK1)),
% 9.99/1.63    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).
% 9.99/1.63  fof(f12856,plain,(
% 9.99/1.63    sK1 = k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl4_194),
% 9.99/1.63    inference(superposition,[],[f282,f12842])).
% 9.99/1.63  fof(f12842,plain,(
% 9.99/1.63    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl4_194),
% 9.99/1.63    inference(avatar_component_clause,[],[f12840])).
% 9.99/1.63  fof(f12840,plain,(
% 9.99/1.63    spl4_194 <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 9.99/1.63    introduced(avatar_definition,[new_symbols(naming,[spl4_194])])).
% 9.99/1.63  fof(f282,plain,(
% 9.99/1.63    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 9.99/1.63    inference(duplicate_literal_removal,[],[f281])).
% 9.99/1.63  fof(f281,plain,(
% 9.99/1.63    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 9.99/1.63    inference(superposition,[],[f64,f71])).
% 9.99/1.63  fof(f71,plain,(
% 9.99/1.63    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 9.99/1.63    inference(cnf_transformation,[],[f31])).
% 9.99/1.63  fof(f31,plain,(
% 9.99/1.63    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 9.99/1.63    inference(ennf_transformation,[],[f22])).
% 9.99/1.63  fof(f22,axiom,(
% 9.99/1.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 9.99/1.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 9.99/1.63  fof(f64,plain,(
% 9.99/1.63    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 9.99/1.63    inference(cnf_transformation,[],[f27])).
% 9.99/1.63  fof(f27,plain,(
% 9.99/1.63    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 9.99/1.63    inference(ennf_transformation,[],[f14])).
% 9.99/1.63  fof(f14,axiom,(
% 9.99/1.63    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 9.99/1.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 9.99/1.63  fof(f12843,plain,(
% 9.99/1.63    spl4_194 | ~spl4_10),
% 9.99/1.63    inference(avatar_split_clause,[],[f12838,f200,f12840])).
% 9.99/1.63  fof(f200,plain,(
% 9.99/1.63    spl4_10 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 9.99/1.63    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 9.99/1.63  fof(f12838,plain,(
% 9.99/1.63    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl4_10),
% 9.99/1.63    inference(duplicate_literal_removal,[],[f12812])).
% 9.99/1.63  fof(f12812,plain,(
% 9.99/1.63    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl4_10),
% 9.99/1.63    inference(resolution,[],[f1817,f238])).
% 9.99/1.63  fof(f238,plain,(
% 9.99/1.63    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1,X0),X0) | k4_xboole_0(X0,X1) = X0) )),
% 9.99/1.63    inference(factoring,[],[f83])).
% 9.99/1.63  fof(f83,plain,(
% 9.99/1.63    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 9.99/1.63    inference(cnf_transformation,[],[f53])).
% 9.99/1.63  fof(f53,plain,(
% 9.99/1.63    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 9.99/1.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f51,f52])).
% 9.99/1.63  fof(f52,plain,(
% 9.99/1.63    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 9.99/1.63    introduced(choice_axiom,[])).
% 9.99/1.63  fof(f51,plain,(
% 9.99/1.63    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 9.99/1.63    inference(rectify,[],[f50])).
% 9.99/1.63  fof(f50,plain,(
% 9.99/1.63    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 9.99/1.63    inference(flattening,[],[f49])).
% 9.99/1.63  fof(f49,plain,(
% 9.99/1.63    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 9.99/1.63    inference(nnf_transformation,[],[f2])).
% 9.99/1.63  fof(f2,axiom,(
% 9.99/1.63    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 9.99/1.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 9.99/1.63  fof(f1817,plain,(
% 9.99/1.63    ( ! [X1] : (~r2_hidden(sK2(X1,k2_tops_1(sK0,sK1),X1),sK1) | k4_xboole_0(X1,k2_tops_1(sK0,sK1)) = X1) ) | ~spl4_10),
% 9.99/1.63    inference(resolution,[],[f1786,f448])).
% 9.99/1.63  fof(f448,plain,(
% 9.99/1.63    ( ! [X2,X1] : (r2_hidden(sK2(X1,X2,X1),X2) | k4_xboole_0(X1,X2) = X1) )),
% 9.99/1.63    inference(subsumption_resolution,[],[f446,f83])).
% 9.99/1.63  fof(f446,plain,(
% 9.99/1.63    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = X1 | r2_hidden(sK2(X1,X2,X1),X2) | ~r2_hidden(sK2(X1,X2,X1),X1)) )),
% 9.99/1.63    inference(duplicate_literal_removal,[],[f439])).
% 9.99/1.63  fof(f439,plain,(
% 9.99/1.63    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = X1 | r2_hidden(sK2(X1,X2,X1),X2) | ~r2_hidden(sK2(X1,X2,X1),X1) | k4_xboole_0(X1,X2) = X1) )),
% 9.99/1.63    inference(resolution,[],[f238,f85])).
% 9.99/1.63  fof(f85,plain,(
% 9.99/1.63    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 9.99/1.63    inference(cnf_transformation,[],[f53])).
% 9.99/1.63  fof(f1786,plain,(
% 9.99/1.63    ( ! [X1] : (~r2_hidden(X1,k2_tops_1(sK0,sK1)) | ~r2_hidden(X1,sK1)) ) | ~spl4_10),
% 9.99/1.63    inference(superposition,[],[f102,f202])).
% 9.99/1.63  fof(f202,plain,(
% 9.99/1.63    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~spl4_10),
% 9.99/1.63    inference(avatar_component_clause,[],[f200])).
% 9.99/1.63  fof(f102,plain,(
% 9.99/1.63    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 9.99/1.63    inference(equality_resolution,[],[f81])).
% 9.99/1.63  fof(f81,plain,(
% 9.99/1.63    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 9.99/1.63    inference(cnf_transformation,[],[f53])).
% 9.99/1.63  fof(f9705,plain,(
% 9.99/1.63    spl4_6 | ~spl4_3),
% 9.99/1.63    inference(avatar_split_clause,[],[f9697,f118,f135])).
% 9.99/1.63  fof(f135,plain,(
% 9.99/1.63    spl4_6 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 9.99/1.63    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 9.99/1.63  fof(f9697,plain,(
% 9.99/1.63    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl4_3),
% 9.99/1.63    inference(resolution,[],[f120,f77])).
% 9.99/1.63  % (31229)Time limit reached!
% 9.99/1.63  % (31229)------------------------------
% 9.99/1.63  % (31229)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.99/1.63  fof(f77,plain,(
% 9.99/1.63    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 9.99/1.63    inference(cnf_transformation,[],[f48])).
% 9.99/1.63  % (31229)Termination reason: Time limit
% 9.99/1.63  fof(f48,plain,(
% 9.99/1.63    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 9.99/1.63    inference(nnf_transformation,[],[f16])).
% 9.99/1.63  % (31229)Termination phase: Saturation
% 9.99/1.63  
% 9.99/1.63  % (31229)Memory used [KB]: 3326
% 9.99/1.63  fof(f16,axiom,(
% 9.99/1.63    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 9.99/1.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 9.99/1.63  % (31229)Time elapsed: 1.200 s
% 9.99/1.63  % (31229)------------------------------
% 9.99/1.63  % (31229)------------------------------
% 9.99/1.63  fof(f1780,plain,(
% 9.99/1.63    spl4_10 | ~spl4_2 | ~spl4_9),
% 9.99/1.63    inference(avatar_split_clause,[],[f1779,f196,f112,f200])).
% 9.99/1.63  fof(f112,plain,(
% 9.99/1.63    spl4_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 9.99/1.63    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 9.99/1.63  fof(f196,plain,(
% 9.99/1.63    spl4_9 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 9.99/1.63    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 9.99/1.63  fof(f1779,plain,(
% 9.99/1.63    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (~spl4_2 | ~spl4_9)),
% 9.99/1.63    inference(subsumption_resolution,[],[f1776,f197])).
% 9.99/1.63  fof(f197,plain,(
% 9.99/1.63    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_9),
% 9.99/1.63    inference(avatar_component_clause,[],[f196])).
% 9.99/1.63  fof(f1776,plain,(
% 9.99/1.63    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_2),
% 9.99/1.63    inference(superposition,[],[f64,f113])).
% 9.99/1.63  fof(f113,plain,(
% 9.99/1.63    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl4_2),
% 9.99/1.63    inference(avatar_component_clause,[],[f112])).
% 9.99/1.63  fof(f1773,plain,(
% 9.99/1.63    ~spl4_1 | spl4_51 | ~spl4_3 | ~spl4_4 | ~spl4_6 | ~spl4_50),
% 9.99/1.63    inference(avatar_split_clause,[],[f1640,f1208,f135,f123,f118,f1212,f108])).
% 9.99/1.63  fof(f108,plain,(
% 9.99/1.63    spl4_1 <=> v3_pre_topc(sK1,sK0)),
% 9.99/1.63    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 9.99/1.63  fof(f1208,plain,(
% 9.99/1.63    spl4_50 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 9.99/1.63    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).
% 9.99/1.63  fof(f1640,plain,(
% 9.99/1.63    sK1 = k1_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0) | (~spl4_3 | ~spl4_4 | ~spl4_6 | ~spl4_50)),
% 9.99/1.63    inference(subsumption_resolution,[],[f1639,f137])).
% 9.99/1.63  fof(f137,plain,(
% 9.99/1.63    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl4_6),
% 9.99/1.63    inference(avatar_component_clause,[],[f135])).
% 9.99/1.63  fof(f1639,plain,(
% 9.99/1.63    ~r1_tarski(sK1,u1_struct_0(sK0)) | sK1 = k1_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0) | (~spl4_3 | ~spl4_4 | ~spl4_50)),
% 9.99/1.63    inference(subsumption_resolution,[],[f1636,f99])).
% 9.99/1.63  fof(f99,plain,(
% 9.99/1.63    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 9.99/1.63    inference(equality_resolution,[],[f66])).
% 9.99/1.63  fof(f66,plain,(
% 9.99/1.63    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 9.99/1.63    inference(cnf_transformation,[],[f47])).
% 9.99/1.63  fof(f47,plain,(
% 9.99/1.63    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 9.99/1.63    inference(flattening,[],[f46])).
% 9.99/1.63  fof(f46,plain,(
% 9.99/1.63    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 9.99/1.63    inference(nnf_transformation,[],[f3])).
% 9.99/1.63  fof(f3,axiom,(
% 9.99/1.63    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 9.99/1.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 9.99/1.63  fof(f1636,plain,(
% 9.99/1.63    ~r1_tarski(sK1,sK1) | ~r1_tarski(sK1,u1_struct_0(sK0)) | sK1 = k1_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0) | (~spl4_3 | ~spl4_4 | ~spl4_50)),
% 9.99/1.63    inference(resolution,[],[f1209,f507])).
% 9.99/1.63  fof(f507,plain,(
% 9.99/1.63    ( ! [X2] : (~r1_tarski(k1_tops_1(sK0,sK1),X2) | ~r1_tarski(X2,sK1) | ~r1_tarski(X2,u1_struct_0(sK0)) | k1_tops_1(sK0,sK1) = X2 | ~v3_pre_topc(X2,sK0)) ) | (~spl4_3 | ~spl4_4)),
% 9.99/1.63    inference(resolution,[],[f333,f67])).
% 9.99/1.63  fof(f67,plain,(
% 9.99/1.63    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 9.99/1.63    inference(cnf_transformation,[],[f47])).
% 9.99/1.63  fof(f333,plain,(
% 9.99/1.63    ( ! [X0] : (r1_tarski(X0,k1_tops_1(sK0,sK1)) | ~v3_pre_topc(X0,sK0) | ~r1_tarski(X0,sK1) | ~r1_tarski(X0,u1_struct_0(sK0))) ) | (~spl4_3 | ~spl4_4)),
% 9.99/1.63    inference(resolution,[],[f297,f78])).
% 9.99/1.63  fof(f78,plain,(
% 9.99/1.63    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 9.99/1.63    inference(cnf_transformation,[],[f48])).
% 9.99/1.63  fof(f297,plain,(
% 9.99/1.63    ( ! [X10] : (~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X10,sK0) | r1_tarski(X10,k1_tops_1(sK0,sK1)) | ~r1_tarski(X10,sK1)) ) | (~spl4_3 | ~spl4_4)),
% 9.99/1.63    inference(subsumption_resolution,[],[f294,f125])).
% 9.99/1.63  fof(f294,plain,(
% 9.99/1.63    ( ! [X10] : (~r1_tarski(X10,sK1) | ~v3_pre_topc(X10,sK0) | r1_tarski(X10,k1_tops_1(sK0,sK1)) | ~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl4_3),
% 9.99/1.63    inference(resolution,[],[f76,f120])).
% 9.99/1.63  fof(f76,plain,(
% 9.99/1.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 9.99/1.63    inference(cnf_transformation,[],[f39])).
% 9.99/1.63  fof(f39,plain,(
% 9.99/1.63    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 9.99/1.63    inference(flattening,[],[f38])).
% 9.99/1.63  fof(f38,plain,(
% 9.99/1.63    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 9.99/1.63    inference(ennf_transformation,[],[f20])).
% 9.99/1.63  fof(f20,axiom,(
% 9.99/1.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 9.99/1.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).
% 9.99/1.63  fof(f1209,plain,(
% 9.99/1.63    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl4_50),
% 9.99/1.63    inference(avatar_component_clause,[],[f1208])).
% 9.99/1.63  fof(f1772,plain,(
% 9.99/1.63    sK1 != k1_tops_1(sK0,sK1) | v3_pre_topc(sK1,sK0) | ~v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 9.99/1.63    introduced(theory_tautology_sat_conflict,[])).
% 9.99/1.63  fof(f1767,plain,(
% 9.99/1.63    ~spl4_3 | ~spl4_4 | spl4_10 | ~spl4_51),
% 9.99/1.63    inference(avatar_contradiction_clause,[],[f1766])).
% 9.99/1.63  fof(f1766,plain,(
% 9.99/1.63    $false | (~spl4_3 | ~spl4_4 | spl4_10 | ~spl4_51)),
% 9.99/1.63    inference(subsumption_resolution,[],[f1765,f125])).
% 9.99/1.63  fof(f1765,plain,(
% 9.99/1.63    ~l1_pre_topc(sK0) | (~spl4_3 | spl4_10 | ~spl4_51)),
% 9.99/1.63    inference(subsumption_resolution,[],[f1764,f120])).
% 9.99/1.63  fof(f1764,plain,(
% 9.99/1.63    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl4_10 | ~spl4_51)),
% 9.99/1.63    inference(subsumption_resolution,[],[f1760,f201])).
% 9.99/1.64  fof(f201,plain,(
% 9.99/1.64    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | spl4_10),
% 9.99/1.64    inference(avatar_component_clause,[],[f200])).
% 9.99/1.64  fof(f1760,plain,(
% 9.99/1.64    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl4_51),
% 9.99/1.64    inference(superposition,[],[f288,f1214])).
% 9.99/1.64  fof(f1214,plain,(
% 9.99/1.64    sK1 = k1_tops_1(sK0,sK1) | ~spl4_51),
% 9.99/1.64    inference(avatar_component_clause,[],[f1212])).
% 9.99/1.64  fof(f288,plain,(
% 9.99/1.64    ( ! [X2,X3] : (k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 9.99/1.64    inference(subsumption_resolution,[],[f286,f74])).
% 9.99/1.64  fof(f74,plain,(
% 9.99/1.64    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 9.99/1.64    inference(cnf_transformation,[],[f35])).
% 9.99/1.64  fof(f35,plain,(
% 9.99/1.64    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 9.99/1.64    inference(flattening,[],[f34])).
% 9.99/1.64  fof(f34,plain,(
% 9.99/1.64    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 9.99/1.64    inference(ennf_transformation,[],[f17])).
% 9.99/1.64  fof(f17,axiom,(
% 9.99/1.64    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 9.99/1.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 9.99/1.64  fof(f286,plain,(
% 9.99/1.64    ( ! [X2,X3] : (k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))) )),
% 9.99/1.64    inference(superposition,[],[f73,f64])).
% 9.99/1.64  fof(f73,plain,(
% 9.99/1.64    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 9.99/1.64    inference(cnf_transformation,[],[f33])).
% 9.99/1.64  fof(f33,plain,(
% 9.99/1.64    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 9.99/1.64    inference(ennf_transformation,[],[f19])).
% 9.99/1.64  fof(f19,axiom,(
% 9.99/1.64    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 9.99/1.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 9.99/1.64  fof(f1630,plain,(
% 9.99/1.64    spl4_50 | ~spl4_3 | ~spl4_4),
% 9.99/1.64    inference(avatar_split_clause,[],[f1629,f123,f118,f1208])).
% 9.99/1.64  fof(f1629,plain,(
% 9.99/1.64    r1_tarski(k1_tops_1(sK0,sK1),sK1) | (~spl4_3 | ~spl4_4)),
% 9.99/1.64    inference(subsumption_resolution,[],[f1620,f125])).
% 9.99/1.64  fof(f1620,plain,(
% 9.99/1.64    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0) | ~spl4_3),
% 9.99/1.64    inference(resolution,[],[f485,f120])).
% 9.99/1.64  fof(f485,plain,(
% 9.99/1.64    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3))) | r1_tarski(k1_tops_1(X3,X2),X2) | ~l1_pre_topc(X3)) )),
% 9.99/1.64    inference(superposition,[],[f88,f282])).
% 9.99/1.64  fof(f88,plain,(
% 9.99/1.64    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 9.99/1.64    inference(cnf_transformation,[],[f7])).
% 9.99/1.64  fof(f7,axiom,(
% 9.99/1.64    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 9.99/1.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 9.99/1.64  fof(f1218,plain,(
% 9.99/1.64    ~spl4_10 | spl4_2 | ~spl4_9),
% 9.99/1.64    inference(avatar_split_clause,[],[f1217,f196,f112,f200])).
% 9.99/1.64  fof(f1217,plain,(
% 9.99/1.64    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (spl4_2 | ~spl4_9)),
% 9.99/1.64    inference(subsumption_resolution,[],[f1216,f197])).
% 9.99/1.64  fof(f1216,plain,(
% 9.99/1.64    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_2),
% 9.99/1.64    inference(superposition,[],[f114,f64])).
% 9.99/1.64  fof(f114,plain,(
% 9.99/1.64    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | spl4_2),
% 9.99/1.64    inference(avatar_component_clause,[],[f112])).
% 9.99/1.64  fof(f229,plain,(
% 9.99/1.64    spl4_12 | ~spl4_3 | ~spl4_4 | ~spl4_5),
% 9.99/1.64    inference(avatar_split_clause,[],[f224,f128,f123,f118,f226])).
% 9.99/1.64  fof(f226,plain,(
% 9.99/1.64    spl4_12 <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 9.99/1.64    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 9.99/1.64  fof(f128,plain,(
% 9.99/1.64    spl4_5 <=> v2_pre_topc(sK0)),
% 9.99/1.64    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 9.99/1.64  fof(f224,plain,(
% 9.99/1.64    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | (~spl4_3 | ~spl4_4 | ~spl4_5)),
% 9.99/1.64    inference(subsumption_resolution,[],[f223,f130])).
% 9.99/1.64  fof(f130,plain,(
% 9.99/1.64    v2_pre_topc(sK0) | ~spl4_5),
% 9.99/1.64    inference(avatar_component_clause,[],[f128])).
% 9.99/1.64  fof(f223,plain,(
% 9.99/1.64    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~v2_pre_topc(sK0) | (~spl4_3 | ~spl4_4)),
% 9.99/1.64    inference(subsumption_resolution,[],[f221,f125])).
% 9.99/1.64  fof(f221,plain,(
% 9.99/1.64    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl4_3),
% 9.99/1.64    inference(resolution,[],[f75,f120])).
% 9.99/1.64  fof(f75,plain,(
% 9.99/1.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k1_tops_1(X0,X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 9.99/1.64    inference(cnf_transformation,[],[f37])).
% 9.99/1.64  fof(f37,plain,(
% 9.99/1.64    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 9.99/1.64    inference(flattening,[],[f36])).
% 9.99/1.64  fof(f36,plain,(
% 9.99/1.64    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 9.99/1.64    inference(ennf_transformation,[],[f18])).
% 9.99/1.64  fof(f18,axiom,(
% 9.99/1.64    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 9.99/1.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 9.99/1.64  fof(f217,plain,(
% 9.99/1.64    ~spl4_3 | ~spl4_4 | spl4_9),
% 9.99/1.64    inference(avatar_contradiction_clause,[],[f216])).
% 9.99/1.64  fof(f216,plain,(
% 9.99/1.64    $false | (~spl4_3 | ~spl4_4 | spl4_9)),
% 9.99/1.64    inference(subsumption_resolution,[],[f215,f125])).
% 9.99/1.64  fof(f215,plain,(
% 9.99/1.64    ~l1_pre_topc(sK0) | (~spl4_3 | spl4_9)),
% 9.99/1.64    inference(subsumption_resolution,[],[f212,f120])).
% 9.99/1.64  fof(f212,plain,(
% 9.99/1.64    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl4_9),
% 9.99/1.64    inference(resolution,[],[f74,f198])).
% 9.99/1.64  fof(f198,plain,(
% 9.99/1.64    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_9),
% 9.99/1.64    inference(avatar_component_clause,[],[f196])).
% 9.99/1.64  fof(f131,plain,(
% 9.99/1.64    spl4_5),
% 9.99/1.64    inference(avatar_split_clause,[],[f59,f128])).
% 9.99/1.64  fof(f59,plain,(
% 9.99/1.64    v2_pre_topc(sK0)),
% 9.99/1.64    inference(cnf_transformation,[],[f45])).
% 9.99/1.64  fof(f45,plain,(
% 9.99/1.64    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 9.99/1.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f42,f44,f43])).
% 9.99/1.64  fof(f43,plain,(
% 9.99/1.64    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 9.99/1.64    introduced(choice_axiom,[])).
% 9.99/1.64  fof(f44,plain,(
% 9.99/1.64    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 9.99/1.64    introduced(choice_axiom,[])).
% 9.99/1.64  fof(f42,plain,(
% 9.99/1.64    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 9.99/1.64    inference(flattening,[],[f41])).
% 9.99/1.64  fof(f41,plain,(
% 9.99/1.64    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 9.99/1.64    inference(nnf_transformation,[],[f26])).
% 9.99/1.64  fof(f26,plain,(
% 9.99/1.64    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 9.99/1.64    inference(flattening,[],[f25])).
% 9.99/1.64  fof(f25,plain,(
% 9.99/1.64    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 9.99/1.64    inference(ennf_transformation,[],[f24])).
% 9.99/1.64  fof(f24,negated_conjecture,(
% 9.99/1.64    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 9.99/1.64    inference(negated_conjecture,[],[f23])).
% 9.99/1.64  fof(f23,conjecture,(
% 9.99/1.64    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 9.99/1.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).
% 9.99/1.64  fof(f126,plain,(
% 9.99/1.64    spl4_4),
% 9.99/1.64    inference(avatar_split_clause,[],[f60,f123])).
% 9.99/1.64  fof(f60,plain,(
% 9.99/1.64    l1_pre_topc(sK0)),
% 9.99/1.64    inference(cnf_transformation,[],[f45])).
% 9.99/1.64  fof(f121,plain,(
% 9.99/1.64    spl4_3),
% 9.99/1.64    inference(avatar_split_clause,[],[f61,f118])).
% 9.99/1.64  fof(f61,plain,(
% 9.99/1.64    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 9.99/1.64    inference(cnf_transformation,[],[f45])).
% 9.99/1.64  fof(f116,plain,(
% 9.99/1.64    spl4_1 | spl4_2),
% 9.99/1.64    inference(avatar_split_clause,[],[f62,f112,f108])).
% 9.99/1.64  fof(f62,plain,(
% 9.99/1.64    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 9.99/1.64    inference(cnf_transformation,[],[f45])).
% 9.99/1.64  fof(f115,plain,(
% 9.99/1.64    ~spl4_1 | ~spl4_2),
% 9.99/1.64    inference(avatar_split_clause,[],[f63,f112,f108])).
% 9.99/1.64  fof(f63,plain,(
% 9.99/1.64    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 9.99/1.64    inference(cnf_transformation,[],[f45])).
% 9.99/1.64  % SZS output end Proof for theBenchmark
% 9.99/1.64  % (31250)------------------------------
% 9.99/1.64  % (31250)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.99/1.64  % (31250)Termination reason: Refutation
% 9.99/1.64  
% 9.99/1.64  % (31250)Memory used [KB]: 15223
% 9.99/1.64  % (31250)Time elapsed: 1.168 s
% 9.99/1.64  % (31250)------------------------------
% 9.99/1.64  % (31250)------------------------------
% 9.99/1.64  % (31228)Success in time 1.271 s
%------------------------------------------------------------------------------
