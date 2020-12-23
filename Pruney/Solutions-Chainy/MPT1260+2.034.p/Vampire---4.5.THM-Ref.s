%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:38 EST 2020

% Result     : Theorem 24.99s
% Output     : Refutation 24.99s
% Verified   : 
% Statistics : Number of formulae       :  376 ( 831 expanded)
%              Number of leaves         :   82 ( 360 expanded)
%              Depth                    :   13
%              Number of atoms          : 1184 (2455 expanded)
%              Number of equality atoms :  257 ( 564 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18860,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f126,f131,f149,f183,f192,f202,f279,f295,f300,f325,f387,f397,f439,f485,f503,f535,f540,f599,f628,f686,f730,f1368,f1372,f1382,f1670,f1723,f1767,f1961,f2101,f2339,f2401,f2415,f2416,f2995,f3310,f3784,f3925,f3968,f4146,f4539,f4618,f5341,f5471,f5517,f5649,f5695,f12204,f12506,f12510,f12941,f13030,f13065,f13404,f13500,f17402,f18044,f18579])).

fof(f18579,plain,
    ( ~ spl4_33
    | ~ spl4_94
    | spl4_137
    | ~ spl4_167
    | ~ spl4_323
    | ~ spl4_409 ),
    inference(avatar_contradiction_clause,[],[f18578])).

fof(f18578,plain,
    ( $false
    | ~ spl4_33
    | ~ spl4_94
    | spl4_137
    | ~ spl4_167
    | ~ spl4_323
    | ~ spl4_409 ),
    inference(subsumption_resolution,[],[f18191,f2399])).

fof(f2399,plain,
    ( k4_xboole_0(u1_struct_0(sK0),sK1) != k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))
    | spl4_137 ),
    inference(avatar_component_clause,[],[f2398])).

fof(f2398,plain,
    ( spl4_137
  <=> k4_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_137])])).

fof(f18191,plain,
    ( k4_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl4_33
    | ~ spl4_94
    | ~ spl4_167
    | ~ spl4_323
    | ~ spl4_409 ),
    inference(backward_demodulation,[],[f4145,f18080])).

fof(f18080,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl4_33
    | ~ spl4_94
    | ~ spl4_323
    | ~ spl4_409 ),
    inference(backward_demodulation,[],[f598,f18079])).

fof(f18079,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl4_94
    | ~ spl4_323
    | ~ spl4_409 ),
    inference(forward_demodulation,[],[f18051,f1722])).

fof(f1722,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl4_94 ),
    inference(avatar_component_clause,[],[f1720])).

fof(f1720,plain,
    ( spl4_94
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_94])])).

fof(f18051,plain,
    ( sK1 = k4_xboole_0(sK1,k4_xboole_0(k2_pre_topc(sK0,sK1),sK1))
    | ~ spl4_323
    | ~ spl4_409 ),
    inference(superposition,[],[f13064,f18043])).

fof(f18043,plain,
    ( sK1 = k3_xboole_0(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl4_409 ),
    inference(avatar_component_clause,[],[f18041])).

fof(f18041,plain,
    ( spl4_409
  <=> sK1 = k3_xboole_0(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_409])])).

fof(f13064,plain,
    ( ! [X49] : sK1 = k4_xboole_0(sK1,k4_xboole_0(X49,k3_xboole_0(sK1,X49)))
    | ~ spl4_323 ),
    inference(avatar_component_clause,[],[f13063])).

fof(f13063,plain,
    ( spl4_323
  <=> ! [X49] : sK1 = k4_xboole_0(sK1,k4_xboole_0(X49,k3_xboole_0(sK1,X49))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_323])])).

fof(f598,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f596])).

fof(f596,plain,
    ( spl4_33
  <=> k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f4145,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1))
    | ~ spl4_167 ),
    inference(avatar_component_clause,[],[f4143])).

fof(f4143,plain,
    ( spl4_167
  <=> k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_167])])).

fof(f18044,plain,
    ( spl4_409
    | ~ spl4_27
    | ~ spl4_117
    | ~ spl4_335
    | ~ spl4_392 ),
    inference(avatar_split_clause,[],[f17997,f17399,f13498,f1958,f501,f18041])).

fof(f501,plain,
    ( spl4_27
  <=> ! [X0] : k4_xboole_0(sK1,X0) = k3_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f1958,plain,
    ( spl4_117
  <=> k2_pre_topc(sK0,sK1) = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_117])])).

fof(f13498,plain,
    ( spl4_335
  <=> ! [X0] : sK1 = k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_335])])).

fof(f17399,plain,
    ( spl4_392
  <=> k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_392])])).

fof(f17997,plain,
    ( sK1 = k3_xboole_0(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl4_27
    | ~ spl4_117
    | ~ spl4_335
    | ~ spl4_392 ),
    inference(backward_demodulation,[],[f3635,f17986])).

fof(f17986,plain,
    ( sK1 = k4_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))
    | ~ spl4_335
    | ~ spl4_392 ),
    inference(superposition,[],[f13499,f17401])).

fof(f17401,plain,
    ( k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))
    | ~ spl4_392 ),
    inference(avatar_component_clause,[],[f17399])).

fof(f13499,plain,
    ( ! [X0] : sK1 = k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),X0))
    | ~ spl4_335 ),
    inference(avatar_component_clause,[],[f13498])).

fof(f3635,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k3_xboole_0(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl4_27
    | ~ spl4_117 ),
    inference(superposition,[],[f502,f1960])).

fof(f1960,plain,
    ( k2_pre_topc(sK0,sK1) = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))
    | ~ spl4_117 ),
    inference(avatar_component_clause,[],[f1958])).

fof(f502,plain,
    ( ! [X0] : k4_xboole_0(sK1,X0) = k3_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),X0))
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f501])).

fof(f17402,plain,
    ( spl4_392
    | ~ spl4_123
    | ~ spl4_153 ),
    inference(avatar_split_clause,[],[f5164,f3781,f2099,f17399])).

fof(f2099,plain,
    ( spl4_123
  <=> ! [X0] : k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),X0) = k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_123])])).

fof(f3781,plain,
    ( spl4_153
  <=> k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_153])])).

fof(f5164,plain,
    ( k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))
    | ~ spl4_123
    | ~ spl4_153 ),
    inference(superposition,[],[f3783,f2100])).

fof(f2100,plain,
    ( ! [X0] : k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),X0) = k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),X0)
    | ~ spl4_123 ),
    inference(avatar_component_clause,[],[f2099])).

fof(f3783,plain,
    ( k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))
    | ~ spl4_153 ),
    inference(avatar_component_clause,[],[f3781])).

fof(f13500,plain,
    ( spl4_335
    | ~ spl4_323
    | ~ spl4_333 ),
    inference(avatar_split_clause,[],[f13439,f13402,f13063,f13498])).

fof(f13402,plain,
    ( spl4_333
  <=> ! [X1] : k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_333])])).

fof(f13439,plain,
    ( ! [X0] : sK1 = k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),X0))
    | ~ spl4_323
    | ~ spl4_333 ),
    inference(forward_demodulation,[],[f13421,f76])).

fof(f76,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f13421,plain,
    ( ! [X0] : sK1 = k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),X0),k1_xboole_0))
    | ~ spl4_323
    | ~ spl4_333 ),
    inference(superposition,[],[f13064,f13403])).

fof(f13403,plain,
    ( ! [X1] : k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),X1))
    | ~ spl4_333 ),
    inference(avatar_component_clause,[],[f13402])).

fof(f13404,plain,
    ( spl4_333
    | ~ spl4_301
    | ~ spl4_322 ),
    inference(avatar_split_clause,[],[f13058,f13027,f12504,f13402])).

fof(f12504,plain,
    ( spl4_301
  <=> ! [X68] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X68) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_301])])).

fof(f13027,plain,
    ( spl4_322
  <=> k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_322])])).

fof(f13058,plain,
    ( ! [X1] : k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),X1))
    | ~ spl4_301
    | ~ spl4_322 ),
    inference(forward_demodulation,[],[f13045,f12505])).

fof(f12505,plain,
    ( ! [X68] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X68)
    | ~ spl4_301 ),
    inference(avatar_component_clause,[],[f12504])).

fof(f13045,plain,
    ( ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k3_xboole_0(sK1,k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),X1))
    | ~ spl4_322 ),
    inference(superposition,[],[f99,f13029])).

fof(f13029,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl4_322 ),
    inference(avatar_component_clause,[],[f13027])).

fof(f99,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f13065,plain,
    ( spl4_323
    | ~ spl4_221
    | ~ spl4_321 ),
    inference(avatar_split_clause,[],[f13025,f12939,f5515,f13063])).

fof(f5515,plain,
    ( spl4_221
  <=> ! [X6] : k4_xboole_0(sK1,X6) = k4_xboole_0(sK1,k3_xboole_0(sK1,X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_221])])).

fof(f12939,plain,
    ( spl4_321
  <=> ! [X7,X8] : k1_xboole_0 = k3_xboole_0(X7,k4_xboole_0(X8,k3_xboole_0(X7,X8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_321])])).

fof(f13025,plain,
    ( ! [X49] : sK1 = k4_xboole_0(sK1,k4_xboole_0(X49,k3_xboole_0(sK1,X49)))
    | ~ spl4_221
    | ~ spl4_321 ),
    inference(forward_demodulation,[],[f13003,f76])).

fof(f13003,plain,
    ( ! [X49] : k4_xboole_0(sK1,k1_xboole_0) = k4_xboole_0(sK1,k4_xboole_0(X49,k3_xboole_0(sK1,X49)))
    | ~ spl4_221
    | ~ spl4_321 ),
    inference(superposition,[],[f5516,f12940])).

fof(f12940,plain,
    ( ! [X8,X7] : k1_xboole_0 = k3_xboole_0(X7,k4_xboole_0(X8,k3_xboole_0(X7,X8)))
    | ~ spl4_321 ),
    inference(avatar_component_clause,[],[f12939])).

fof(f5516,plain,
    ( ! [X6] : k4_xboole_0(sK1,X6) = k4_xboole_0(sK1,k3_xboole_0(sK1,X6))
    | ~ spl4_221 ),
    inference(avatar_component_clause,[],[f5515])).

fof(f13030,plain,
    ( spl4_322
    | ~ spl4_7
    | ~ spl4_321 ),
    inference(avatar_split_clause,[],[f12966,f12939,f199,f13027])).

fof(f199,plain,
    ( spl4_7
  <=> sK1 = k3_xboole_0(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f12966,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl4_7
    | ~ spl4_321 ),
    inference(superposition,[],[f12940,f201])).

fof(f201,plain,
    ( sK1 = k3_xboole_0(sK1,u1_struct_0(sK0))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f199])).

fof(f12941,plain,
    ( spl4_321
    | ~ spl4_302 ),
    inference(avatar_split_clause,[],[f12524,f12508,f12939])).

fof(f12508,plain,
    ( spl4_302
  <=> ! [X3] : k1_xboole_0 = k4_xboole_0(X3,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_302])])).

fof(f12524,plain,
    ( ! [X8,X7] : k1_xboole_0 = k3_xboole_0(X7,k4_xboole_0(X8,k3_xboole_0(X7,X8)))
    | ~ spl4_302 ),
    inference(superposition,[],[f12509,f99])).

fof(f12509,plain,
    ( ! [X3] : k1_xboole_0 = k4_xboole_0(X3,X3)
    | ~ spl4_302 ),
    inference(avatar_component_clause,[],[f12508])).

fof(f12510,plain,
    ( spl4_302
    | ~ spl4_227
    | ~ spl4_295 ),
    inference(avatar_split_clause,[],[f12278,f12202,f5693,f12508])).

fof(f5693,plain,
    ( spl4_227
  <=> ! [X13] : ~ r2_hidden(X13,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_227])])).

fof(f12202,plain,
    ( spl4_295
  <=> ! [X3,X2] :
        ( k1_xboole_0 = k4_xboole_0(X2,X3)
        | r2_hidden(sK2(X2,X3,k1_xboole_0),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_295])])).

fof(f12278,plain,
    ( ! [X3] : k1_xboole_0 = k4_xboole_0(X3,X3)
    | ~ spl4_227
    | ~ spl4_295 ),
    inference(subsumption_resolution,[],[f12275,f5694])).

fof(f5694,plain,
    ( ! [X13] : ~ r2_hidden(X13,k1_xboole_0)
    | ~ spl4_227 ),
    inference(avatar_component_clause,[],[f5693])).

fof(f12275,plain,
    ( ! [X3] :
        ( k1_xboole_0 = k4_xboole_0(X3,X3)
        | r2_hidden(sK2(X3,X3,k1_xboole_0),k1_xboole_0) )
    | ~ spl4_295 ),
    inference(duplicate_literal_removal,[],[f12233])).

fof(f12233,plain,
    ( ! [X3] :
        ( k1_xboole_0 = k4_xboole_0(X3,X3)
        | k1_xboole_0 = k4_xboole_0(X3,X3)
        | r2_hidden(sK2(X3,X3,k1_xboole_0),k1_xboole_0) )
    | ~ spl4_295 ),
    inference(resolution,[],[f12203,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f62,f63])).

fof(f63,plain,(
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

fof(f62,plain,(
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
    inference(rectify,[],[f61])).

fof(f61,plain,(
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
    inference(flattening,[],[f60])).

fof(f60,plain,(
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

fof(f12203,plain,
    ( ! [X2,X3] :
        ( r2_hidden(sK2(X2,X3,k1_xboole_0),X2)
        | k1_xboole_0 = k4_xboole_0(X2,X3) )
    | ~ spl4_295 ),
    inference(avatar_component_clause,[],[f12202])).

fof(f12506,plain,
    ( spl4_301
    | ~ spl4_227
    | ~ spl4_295 ),
    inference(avatar_split_clause,[],[f12264,f12202,f5693,f12504])).

fof(f12264,plain,
    ( ! [X68] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X68)
    | ~ spl4_227
    | ~ spl4_295 ),
    inference(resolution,[],[f12203,f5694])).

fof(f12204,plain,
    ( spl4_295
    | ~ spl4_227 ),
    inference(avatar_split_clause,[],[f5697,f5693,f12202])).

fof(f5697,plain,
    ( ! [X2,X3] :
        ( k1_xboole_0 = k4_xboole_0(X2,X3)
        | r2_hidden(sK2(X2,X3,k1_xboole_0),X2) )
    | ~ spl4_227 ),
    inference(resolution,[],[f5694,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f5695,plain,
    ( spl4_227
    | ~ spl4_226 ),
    inference(avatar_split_clause,[],[f5688,f5647,f5693])).

fof(f5647,plain,
    ( spl4_226
  <=> ! [X27,X26] :
        ( ~ r2_hidden(X27,k4_xboole_0(sK1,X26))
        | ~ r2_hidden(X27,k3_xboole_0(sK1,X26)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_226])])).

fof(f5688,plain,
    ( ! [X13] : ~ r2_hidden(X13,k1_xboole_0)
    | ~ spl4_226 ),
    inference(forward_demodulation,[],[f5687,f75])).

fof(f75,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f5687,plain,
    ( ! [X13] : ~ r2_hidden(X13,k3_xboole_0(sK1,k1_xboole_0))
    | ~ spl4_226 ),
    inference(subsumption_resolution,[],[f5673,f121])).

fof(f121,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f110])).

fof(f110,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f67,f68])).

fof(f68,plain,(
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

fof(f67,plain,(
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
    inference(rectify,[],[f66])).

fof(f66,plain,(
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
    inference(flattening,[],[f65])).

fof(f65,plain,(
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

fof(f5673,plain,
    ( ! [X13] :
        ( ~ r2_hidden(X13,sK1)
        | ~ r2_hidden(X13,k3_xboole_0(sK1,k1_xboole_0)) )
    | ~ spl4_226 ),
    inference(superposition,[],[f5648,f76])).

fof(f5648,plain,
    ( ! [X26,X27] :
        ( ~ r2_hidden(X27,k4_xboole_0(sK1,X26))
        | ~ r2_hidden(X27,k3_xboole_0(sK1,X26)) )
    | ~ spl4_226 ),
    inference(avatar_component_clause,[],[f5647])).

fof(f5649,plain,
    ( spl4_226
    | ~ spl4_221 ),
    inference(avatar_split_clause,[],[f5546,f5515,f5647])).

fof(f5546,plain,
    ( ! [X26,X27] :
        ( ~ r2_hidden(X27,k4_xboole_0(sK1,X26))
        | ~ r2_hidden(X27,k3_xboole_0(sK1,X26)) )
    | ~ spl4_221 ),
    inference(superposition,[],[f117,f5516])).

fof(f117,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f105])).

fof(f105,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f5517,plain,
    ( spl4_221
    | ~ spl4_219 ),
    inference(avatar_split_clause,[],[f5504,f5469,f5515])).

fof(f5469,plain,
    ( spl4_219
  <=> ! [X3] : k3_xboole_0(sK1,X3) = k3_xboole_0(sK1,k3_xboole_0(sK1,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_219])])).

fof(f5504,plain,
    ( ! [X6] : k4_xboole_0(sK1,X6) = k4_xboole_0(sK1,k3_xboole_0(sK1,X6))
    | ~ spl4_219 ),
    inference(forward_demodulation,[],[f5492,f90])).

fof(f90,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f5492,plain,
    ( ! [X6] : k4_xboole_0(sK1,k3_xboole_0(sK1,X6)) = k5_xboole_0(sK1,k3_xboole_0(sK1,X6))
    | ~ spl4_219 ),
    inference(superposition,[],[f90,f5470])).

fof(f5470,plain,
    ( ! [X3] : k3_xboole_0(sK1,X3) = k3_xboole_0(sK1,k3_xboole_0(sK1,X3))
    | ~ spl4_219 ),
    inference(avatar_component_clause,[],[f5469])).

fof(f5471,plain,
    ( spl4_219
    | ~ spl4_29
    | ~ spl4_215 ),
    inference(avatar_split_clause,[],[f5424,f5339,f532,f5469])).

fof(f532,plain,
    ( spl4_29
  <=> sK1 = k4_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f5339,plain,
    ( spl4_215
  <=> ! [X11,X10] : k3_xboole_0(k4_xboole_0(sK1,X10),X11) = k3_xboole_0(sK1,k3_xboole_0(k4_xboole_0(sK1,X10),X11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_215])])).

fof(f5424,plain,
    ( ! [X3] : k3_xboole_0(sK1,X3) = k3_xboole_0(sK1,k3_xboole_0(sK1,X3))
    | ~ spl4_29
    | ~ spl4_215 ),
    inference(superposition,[],[f5340,f534])).

fof(f534,plain,
    ( sK1 = k4_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f532])).

fof(f5340,plain,
    ( ! [X10,X11] : k3_xboole_0(k4_xboole_0(sK1,X10),X11) = k3_xboole_0(sK1,k3_xboole_0(k4_xboole_0(sK1,X10),X11))
    | ~ spl4_215 ),
    inference(avatar_component_clause,[],[f5339])).

fof(f5341,plain,
    ( spl4_215
    | ~ spl4_192 ),
    inference(avatar_split_clause,[],[f4636,f4616,f5339])).

fof(f4616,plain,
    ( spl4_192
  <=> ! [X3] : k4_xboole_0(sK1,X3) = k3_xboole_0(sK1,k4_xboole_0(sK1,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_192])])).

fof(f4636,plain,
    ( ! [X10,X11] : k3_xboole_0(k4_xboole_0(sK1,X10),X11) = k3_xboole_0(sK1,k3_xboole_0(k4_xboole_0(sK1,X10),X11))
    | ~ spl4_192 ),
    inference(superposition,[],[f100,f4617])).

fof(f4617,plain,
    ( ! [X3] : k4_xboole_0(sK1,X3) = k3_xboole_0(sK1,k4_xboole_0(sK1,X3))
    | ~ spl4_192 ),
    inference(avatar_component_clause,[],[f4616])).

fof(f100,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f4618,plain,
    ( spl4_192
    | ~ spl4_21
    | ~ spl4_29
    | ~ spl4_187 ),
    inference(avatar_split_clause,[],[f4602,f4537,f532,f394,f4616])).

fof(f394,plain,
    ( spl4_21
  <=> sK1 = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f4537,plain,
    ( spl4_187
  <=> ! [X3,X2] : k3_xboole_0(sK1,k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),X2),X3)) = k4_xboole_0(k4_xboole_0(sK1,X2),X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_187])])).

fof(f4602,plain,
    ( ! [X3] : k4_xboole_0(sK1,X3) = k3_xboole_0(sK1,k4_xboole_0(sK1,X3))
    | ~ spl4_21
    | ~ spl4_29
    | ~ spl4_187 ),
    inference(forward_demodulation,[],[f4565,f534])).

fof(f4565,plain,
    ( ! [X3] : k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1)),X3) = k3_xboole_0(sK1,k4_xboole_0(sK1,X3))
    | ~ spl4_21
    | ~ spl4_187 ),
    inference(superposition,[],[f4538,f396])).

fof(f396,plain,
    ( sK1 = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f394])).

fof(f4538,plain,
    ( ! [X2,X3] : k3_xboole_0(sK1,k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),X2),X3)) = k4_xboole_0(k4_xboole_0(sK1,X2),X3)
    | ~ spl4_187 ),
    inference(avatar_component_clause,[],[f4537])).

fof(f4539,plain,
    ( spl4_187
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f519,f501,f4537])).

fof(f519,plain,
    ( ! [X2,X3] : k3_xboole_0(sK1,k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),X2),X3)) = k4_xboole_0(k4_xboole_0(sK1,X2),X3)
    | ~ spl4_27 ),
    inference(superposition,[],[f99,f502])).

fof(f4146,plain,
    ( spl4_167
    | ~ spl4_42
    | ~ spl4_50
    | ~ spl4_51 ),
    inference(avatar_split_clause,[],[f4011,f911,f907,f727,f4143])).

fof(f727,plain,
    ( spl4_42
  <=> k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f907,plain,
    ( spl4_50
  <=> m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f911,plain,
    ( spl4_51
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).

fof(f4011,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1))
    | ~ spl4_42
    | ~ spl4_50
    | ~ spl4_51 ),
    inference(forward_demodulation,[],[f4010,f3938])).

fof(f3938,plain,
    ( k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) = k4_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1))
    | ~ spl4_51 ),
    inference(resolution,[],[f913,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f913,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_51 ),
    inference(avatar_component_clause,[],[f911])).

fof(f4010,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))
    | ~ spl4_42
    | ~ spl4_50 ),
    inference(forward_demodulation,[],[f3983,f729])).

fof(f729,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)))
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f727])).

fof(f3983,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))))
    | ~ spl4_50 ),
    inference(resolution,[],[f908,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f908,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_50 ),
    inference(avatar_component_clause,[],[f907])).

fof(f3968,plain,
    ( spl4_50
    | ~ spl4_18
    | ~ spl4_23
    | ~ spl4_134 ),
    inference(avatar_split_clause,[],[f3912,f2336,f436,f322,f907])).

fof(f322,plain,
    ( spl4_18
  <=> m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f436,plain,
    ( spl4_23
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f2336,plain,
    ( spl4_134
  <=> k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_134])])).

fof(f3912,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_18
    | ~ spl4_23
    | ~ spl4_134 ),
    inference(subsumption_resolution,[],[f3911,f324])).

fof(f324,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f322])).

fof(f3911,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_23
    | ~ spl4_134 ),
    inference(subsumption_resolution,[],[f3906,f438])).

fof(f438,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f436])).

fof(f3906,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_134 ),
    inference(superposition,[],[f103,f2338])).

fof(f2338,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1))
    | ~ spl4_134 ),
    inference(avatar_component_clause,[],[f2336])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f3925,plain,
    ( spl4_51
    | ~ spl4_18
    | ~ spl4_23
    | ~ spl4_42
    | ~ spl4_134 ),
    inference(avatar_split_clause,[],[f3913,f2336,f727,f436,f322,f911])).

fof(f3913,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_18
    | ~ spl4_23
    | ~ spl4_42
    | ~ spl4_134 ),
    inference(subsumption_resolution,[],[f3158,f3912])).

fof(f3158,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_42 ),
    inference(superposition,[],[f92,f729])).

fof(f92,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f3784,plain,
    ( spl4_153
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_16
    | ~ spl4_18
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f659,f625,f322,f297,f146,f128,f3781])).

fof(f128,plain,
    ( spl4_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f146,plain,
    ( spl4_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f297,plain,
    ( spl4_16
  <=> sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f625,plain,
    ( spl4_36
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f659,plain,
    ( k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_16
    | ~ spl4_18
    | ~ spl4_36 ),
    inference(backward_demodulation,[],[f355,f641])).

fof(f641,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))
    | ~ spl4_36 ),
    inference(resolution,[],[f627,f93])).

fof(f627,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f625])).

fof(f355,plain,
    ( k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_16
    | ~ spl4_18 ),
    inference(backward_demodulation,[],[f350,f354])).

fof(f354,plain,
    ( k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_16
    | ~ spl4_18 ),
    inference(forward_demodulation,[],[f353,f299])).

fof(f299,plain,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f297])).

fof(f353,plain,
    ( k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))))
    | ~ spl4_2
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f329,f130])).

fof(f130,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f128])).

fof(f329,plain,
    ( k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_18 ),
    inference(resolution,[],[f324,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

fof(f350,plain,
    ( k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_18 ),
    inference(forward_demodulation,[],[f349,f177])).

fof(f177,plain,
    ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(backward_demodulation,[],[f168,f162])).

fof(f162,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1)
    | ~ spl4_3 ),
    inference(resolution,[],[f148,f93])).

fof(f148,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f146])).

fof(f168,plain,
    ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f150,f130])).

fof(f150,plain,
    ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f148,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).

fof(f349,plain,
    ( k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)))
    | ~ spl4_2
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f327,f130])).

fof(f327,plain,
    ( k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_18 ),
    inference(resolution,[],[f324,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f3310,plain,
    ( ~ spl4_137
    | spl4_19
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f361,f322,f128,f123,f379,f2398])).

fof(f379,plain,
    ( spl4_19
  <=> v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f123,plain,
    ( spl4_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f361,plain,
    ( v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | k4_xboole_0(u1_struct_0(sK0),sK1) != k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f360,f130])).

fof(f360,plain,
    ( v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | k4_xboole_0(u1_struct_0(sK0),sK1) != k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_1
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f332,f125])).

fof(f125,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f123])).

fof(f332,plain,
    ( v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | k4_xboole_0(u1_struct_0(sK0),sK1) != k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_18 ),
    inference(resolution,[],[f324,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f2995,plain,
    ( ~ spl4_5
    | ~ spl4_16
    | ~ spl4_42
    | ~ spl4_81
    | ~ spl4_96
    | ~ spl4_137 ),
    inference(avatar_contradiction_clause,[],[f2994])).

fof(f2994,plain,
    ( $false
    | ~ spl4_5
    | ~ spl4_16
    | ~ spl4_42
    | ~ spl4_81
    | ~ spl4_96
    | ~ spl4_137 ),
    inference(subsumption_resolution,[],[f187,f2735])).

fof(f2735,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ spl4_16
    | ~ spl4_42
    | ~ spl4_81
    | ~ spl4_96
    | ~ spl4_137 ),
    inference(trivial_inequality_removal,[],[f2734])).

fof(f2734,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl4_16
    | ~ spl4_42
    | ~ spl4_81
    | ~ spl4_96
    | ~ spl4_137 ),
    inference(backward_demodulation,[],[f2406,f2503])).

fof(f2503,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl4_16
    | ~ spl4_42
    | ~ spl4_96
    | ~ spl4_137 ),
    inference(backward_demodulation,[],[f1766,f2444])).

fof(f2444,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl4_16
    | ~ spl4_42
    | ~ spl4_137 ),
    inference(forward_demodulation,[],[f2439,f299])).

fof(f2439,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl4_42
    | ~ spl4_137 ),
    inference(backward_demodulation,[],[f729,f2400])).

fof(f2400,plain,
    ( k4_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl4_137 ),
    inference(avatar_component_clause,[],[f2398])).

fof(f1766,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl4_96 ),
    inference(avatar_component_clause,[],[f1764])).

fof(f1764,plain,
    ( spl4_96
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_96])])).

fof(f2406,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl4_81 ),
    inference(forward_demodulation,[],[f74,f1371])).

fof(f1371,plain,
    ( ! [X0] : k4_xboole_0(k2_pre_topc(sK0,sK1),X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0)
    | ~ spl4_81 ),
    inference(avatar_component_clause,[],[f1370])).

fof(f1370,plain,
    ( spl4_81
  <=> ! [X0] : k4_xboole_0(k2_pre_topc(sK0,sK1),X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_81])])).

fof(f74,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f54,f56,f55])).

fof(f55,plain,
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

fof(f56,plain,
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

fof(f54,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f29])).

fof(f29,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

fof(f187,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl4_5
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f2416,plain,
    ( ~ spl4_19
    | spl4_5
    | ~ spl4_2
    | ~ spl4_16
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f2405,f322,f297,f128,f185,f379])).

fof(f2405,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ spl4_2
    | ~ spl4_16
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f2404,f130])).

fof(f2404,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_16
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f368,f324])).

fof(f368,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_16 ),
    inference(superposition,[],[f84,f299])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

fof(f2415,plain,
    ( spl4_19
    | ~ spl4_5
    | ~ spl4_2
    | ~ spl4_16
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f2403,f322,f297,f128,f185,f379])).

fof(f2403,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ spl4_2
    | ~ spl4_16
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f2402,f130])).

fof(f2402,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_16
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f369,f324])).

fof(f369,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_16 ),
    inference(superposition,[],[f85,f299])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f2401,plain,
    ( ~ spl4_19
    | spl4_137
    | ~ spl4_2
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f359,f322,f128,f2398,f379])).

fof(f359,plain,
    ( k4_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ spl4_2
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f331,f130])).

fof(f331,plain,
    ( k4_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_18 ),
    inference(resolution,[],[f324,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f2339,plain,
    ( spl4_134
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f352,f322,f146,f128,f2336])).

fof(f352,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_18 ),
    inference(forward_demodulation,[],[f351,f177])).

fof(f351,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)))
    | ~ spl4_2
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f328,f130])).

fof(f328,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_18 ),
    inference(resolution,[],[f324,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f2101,plain,
    ( spl4_123
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f341,f322,f2099])).

fof(f341,plain,
    ( ! [X0] : k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),X0) = k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),X0)
    | ~ spl4_18 ),
    inference(resolution,[],[f324,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f1961,plain,
    ( spl4_117
    | ~ spl4_83
    | ~ spl4_93 ),
    inference(avatar_split_clause,[],[f1708,f1667,f1379,f1958])).

fof(f1379,plain,
    ( spl4_83
  <=> k2_pre_topc(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_83])])).

fof(f1667,plain,
    ( spl4_93
  <=> m1_subset_1(k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_93])])).

fof(f1708,plain,
    ( k2_pre_topc(sK0,sK1) = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))
    | ~ spl4_83
    | ~ spl4_93 ),
    inference(forward_demodulation,[],[f1683,f1381])).

fof(f1381,plain,
    ( k2_pre_topc(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))
    | ~ spl4_83 ),
    inference(avatar_component_clause,[],[f1379])).

fof(f1683,plain,
    ( k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))
    | ~ spl4_93 ),
    inference(resolution,[],[f1669,f93])).

fof(f1669,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_93 ),
    inference(avatar_component_clause,[],[f1667])).

fof(f1767,plain,
    ( spl4_96
    | ~ spl4_38
    | ~ spl4_81 ),
    inference(avatar_split_clause,[],[f1712,f1370,f683,f1764])).

fof(f683,plain,
    ( spl4_38
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f1712,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl4_38
    | ~ spl4_81 ),
    inference(superposition,[],[f1371,f685])).

fof(f685,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f683])).

fof(f1723,plain,
    ( spl4_94
    | ~ spl4_6
    | ~ spl4_81 ),
    inference(avatar_split_clause,[],[f1711,f1370,f189,f1720])).

fof(f189,plain,
    ( spl4_6
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f1711,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl4_6
    | ~ spl4_81 ),
    inference(superposition,[],[f1371,f191])).

fof(f191,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f189])).

fof(f1670,plain,
    ( spl4_93
    | ~ spl4_36
    | ~ spl4_80 ),
    inference(avatar_split_clause,[],[f1665,f1365,f625,f1667])).

fof(f1365,plain,
    ( spl4_80
  <=> k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_80])])).

fof(f1665,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_36
    | ~ spl4_80 ),
    inference(subsumption_resolution,[],[f1660,f627])).

fof(f1660,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_80 ),
    inference(superposition,[],[f92,f1367])).

fof(f1367,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))
    | ~ spl4_80 ),
    inference(avatar_component_clause,[],[f1365])).

fof(f1382,plain,
    ( spl4_83
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f661,f625,f1379])).

fof(f661,plain,
    ( k2_pre_topc(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))
    | ~ spl4_36 ),
    inference(forward_demodulation,[],[f642,f641])).

fof(f642,plain,
    ( k2_pre_topc(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))
    | ~ spl4_36 ),
    inference(resolution,[],[f627,f94])).

fof(f1372,plain,
    ( spl4_81
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f644,f625,f1370])).

fof(f644,plain,
    ( ! [X0] : k4_xboole_0(k2_pre_topc(sK0,sK1),X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0)
    | ~ spl4_36 ),
    inference(resolution,[],[f627,f102])).

fof(f1368,plain,
    ( spl4_80
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f641,f625,f1365])).

fof(f730,plain,
    ( spl4_42
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f176,f146,f128,f727])).

fof(f176,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)))
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(backward_demodulation,[],[f171,f162])).

fof(f171,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f153,f130])).

fof(f153,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f148,f80])).

fof(f686,plain,
    ( spl4_38
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f172,f146,f128,f683])).

fof(f172,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f154,f130])).

fof(f154,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f148,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f628,plain,
    ( spl4_36
    | ~ spl4_3
    | ~ spl4_23
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f623,f537,f436,f146,f625])).

fof(f537,plain,
    ( spl4_30
  <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f623,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_3
    | ~ spl4_23
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f622,f148])).

fof(f622,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_23
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f621,f438])).

fof(f621,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_30 ),
    inference(superposition,[],[f103,f539])).

fof(f539,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f537])).

fof(f599,plain,
    ( spl4_33
    | ~ spl4_15
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f591,f482,f293,f596])).

fof(f293,plain,
    ( spl4_15
  <=> ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f482,plain,
    ( spl4_26
  <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f591,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl4_15
    | ~ spl4_26 ),
    inference(superposition,[],[f484,f294])).

fof(f294,plain,
    ( ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f293])).

fof(f484,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f482])).

fof(f540,plain,
    ( spl4_30
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f170,f146,f128,f537])).

fof(f170,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f152,f130])).

fof(f152,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f148,f79])).

fof(f535,plain,
    ( spl4_29
    | ~ spl4_21
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f529,f501,f394,f532])).

fof(f529,plain,
    ( sK1 = k4_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl4_21
    | ~ spl4_27 ),
    inference(forward_demodulation,[],[f508,f86])).

fof(f86,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f508,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1)) = k3_xboole_0(sK1,sK1)
    | ~ spl4_21
    | ~ spl4_27 ),
    inference(superposition,[],[f502,f396])).

fof(f503,plain,
    ( spl4_27
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f207,f199,f501])).

fof(f207,plain,
    ( ! [X0] : k4_xboole_0(sK1,X0) = k3_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),X0))
    | ~ spl4_7 ),
    inference(superposition,[],[f99,f201])).

fof(f485,plain,
    ( spl4_26
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f169,f146,f128,f482])).

fof(f169,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f151,f130])).

fof(f151,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f148,f78])).

fof(f439,plain,
    ( spl4_23
    | ~ spl4_2
    | ~ spl4_18
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f434,f384,f322,f128,f436])).

fof(f384,plain,
    ( spl4_20
  <=> k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f434,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_2
    | ~ spl4_18
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f433,f130])).

fof(f433,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_18
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f430,f324])).

fof(f430,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_20 ),
    inference(superposition,[],[f96,f386])).

fof(f386,plain,
    ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f384])).

fof(f96,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f397,plain,
    ( spl4_21
    | ~ spl4_16
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f362,f322,f297,f394])).

fof(f362,plain,
    ( sK1 = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl4_16
    | ~ spl4_18 ),
    inference(forward_demodulation,[],[f338,f299])).

fof(f338,plain,
    ( k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl4_18 ),
    inference(resolution,[],[f324,f93])).

fof(f387,plain,
    ( spl4_20
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f177,f146,f128,f384])).

fof(f325,plain,
    ( spl4_18
    | ~ spl4_3
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f310,f276,f146,f322])).

fof(f276,plain,
    ( spl4_14
  <=> k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f310,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_3
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f306,f148])).

fof(f306,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_14 ),
    inference(superposition,[],[f92,f278])).

fof(f278,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f276])).

fof(f300,plain,
    ( spl4_16
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f178,f146,f297])).

fof(f178,plain,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f163,f162])).

fof(f163,plain,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl4_3 ),
    inference(resolution,[],[f148,f94])).

fof(f295,plain,
    ( spl4_15
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f165,f146,f293])).

fof(f165,plain,
    ( ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)
    | ~ spl4_3 ),
    inference(resolution,[],[f148,f102])).

fof(f279,plain,
    ( spl4_14
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f162,f146,f276])).

fof(f202,plain,
    ( spl4_7
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f197,f180,f199])).

fof(f180,plain,
    ( spl4_4
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f197,plain,
    ( sK1 = k3_xboole_0(sK1,u1_struct_0(sK0))
    | ~ spl4_4 ),
    inference(resolution,[],[f182,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f182,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f180])).

fof(f192,plain,
    ( spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f73,f189,f185])).

fof(f73,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f183,plain,
    ( spl4_4
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f164,f146,f180])).

fof(f164,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl4_3 ),
    inference(resolution,[],[f148,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f149,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f72,f146])).

fof(f72,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f57])).

fof(f131,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f71,f128])).

fof(f71,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f126,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f70,f123])).

fof(f70,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f57])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:55:29 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.51  % (13854)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.52  % (13854)Refutation not found, incomplete strategy% (13854)------------------------------
% 0.19/0.52  % (13854)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (13844)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.53  % (13833)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.55  % (13832)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.55  % (13854)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.55  
% 0.19/0.55  % (13854)Memory used [KB]: 10746
% 0.19/0.55  % (13854)Time elapsed: 0.110 s
% 0.19/0.55  % (13854)------------------------------
% 0.19/0.55  % (13854)------------------------------
% 0.19/0.55  % (13846)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.55  % (13852)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.19/0.55  % (13834)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.55  % (13835)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.56  % (13843)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.56  % (13837)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.56  % (13838)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.56  % (13849)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.19/0.57  % (13860)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.19/0.57  % (13841)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.57  % (13848)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.57  % (13857)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.19/0.58  % (13836)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.58  % (13840)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.59  % (13849)Refutation not found, incomplete strategy% (13849)------------------------------
% 0.19/0.59  % (13849)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.59  % (13849)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.59  
% 0.19/0.59  % (13849)Memory used [KB]: 10618
% 0.19/0.59  % (13849)Time elapsed: 0.187 s
% 0.19/0.59  % (13849)------------------------------
% 0.19/0.59  % (13849)------------------------------
% 0.19/0.59  % (13858)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.19/0.59  % (13839)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.59  % (13861)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.19/0.59  % (13850)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.19/0.59  % (13859)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.19/0.60  % (13851)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.19/0.60  % (13842)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.60  % (13856)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.19/0.61  % (13847)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.61  % (13853)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.62  % (13855)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.89/0.62  % (13845)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 3.13/0.79  % (13886)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 3.13/0.81  % (13837)Time limit reached!
% 3.13/0.81  % (13837)------------------------------
% 3.13/0.81  % (13837)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.13/0.81  % (13837)Termination reason: Time limit
% 3.13/0.81  
% 3.13/0.81  % (13837)Memory used [KB]: 7931
% 3.13/0.81  % (13837)Time elapsed: 0.402 s
% 3.13/0.81  % (13837)------------------------------
% 3.13/0.81  % (13837)------------------------------
% 3.64/0.83  % (13887)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 3.95/0.91  % (13842)Time limit reached!
% 3.95/0.91  % (13842)------------------------------
% 3.95/0.91  % (13842)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.95/0.93  % (13842)Termination reason: Time limit
% 3.95/0.93  
% 3.95/0.93  % (13842)Memory used [KB]: 11897
% 3.95/0.93  % (13842)Time elapsed: 0.503 s
% 3.95/0.93  % (13842)------------------------------
% 3.95/0.93  % (13842)------------------------------
% 3.95/0.93  % (13844)Time limit reached!
% 3.95/0.93  % (13844)------------------------------
% 3.95/0.93  % (13844)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.95/0.93  % (13844)Termination reason: Time limit
% 3.95/0.93  
% 3.95/0.93  % (13844)Memory used [KB]: 8827
% 3.95/0.93  % (13844)Time elapsed: 0.531 s
% 3.95/0.93  % (13844)------------------------------
% 3.95/0.93  % (13844)------------------------------
% 4.49/0.94  % (13833)Time limit reached!
% 4.49/0.94  % (13833)------------------------------
% 4.49/0.94  % (13833)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.49/0.96  % (13833)Termination reason: Time limit
% 4.49/0.96  
% 4.49/0.96  % (13833)Memory used [KB]: 7036
% 4.49/0.96  % (13833)Time elapsed: 0.529 s
% 4.49/0.96  % (13833)------------------------------
% 4.49/0.96  % (13833)------------------------------
% 4.73/0.99  % (13832)Time limit reached!
% 4.73/0.99  % (13832)------------------------------
% 4.73/0.99  % (13832)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.73/0.99  % (13832)Termination reason: Time limit
% 4.73/0.99  
% 4.73/0.99  % (13832)Memory used [KB]: 4605
% 4.73/0.99  % (13832)Time elapsed: 0.533 s
% 4.73/0.99  % (13832)------------------------------
% 4.73/0.99  % (13832)------------------------------
% 4.73/1.01  % (13839)Time limit reached!
% 4.73/1.01  % (13839)------------------------------
% 4.73/1.01  % (13839)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.73/1.01  % (13839)Termination reason: Time limit
% 4.73/1.01  % (13839)Termination phase: Saturation
% 4.73/1.01  
% 4.73/1.01  % (13839)Memory used [KB]: 9083
% 4.73/1.01  % (13839)Time elapsed: 0.600 s
% 4.73/1.01  % (13839)------------------------------
% 4.73/1.01  % (13839)------------------------------
% 4.73/1.02  % (13888)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 5.14/1.03  % (13860)Time limit reached!
% 5.14/1.03  % (13860)------------------------------
% 5.14/1.03  % (13860)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.14/1.03  % (13860)Termination reason: Time limit
% 5.14/1.03  
% 5.14/1.03  % (13860)Memory used [KB]: 7547
% 5.14/1.03  % (13860)Time elapsed: 0.629 s
% 5.14/1.03  % (13860)------------------------------
% 5.14/1.03  % (13860)------------------------------
% 5.14/1.03  % (13848)Time limit reached!
% 5.14/1.03  % (13848)------------------------------
% 5.14/1.03  % (13848)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.14/1.04  % (13848)Termination reason: Time limit
% 5.14/1.04  
% 5.14/1.04  % (13848)Memory used [KB]: 14711
% 5.14/1.04  % (13848)Time elapsed: 0.617 s
% 5.14/1.04  % (13848)------------------------------
% 5.14/1.04  % (13848)------------------------------
% 5.31/1.15  % (13889)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 5.31/1.15  % (13890)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 6.60/1.19  % (13891)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 6.60/1.21  % (13892)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 6.60/1.21  % (13895)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 6.60/1.22  % (13853)Time limit reached!
% 6.60/1.22  % (13853)------------------------------
% 6.60/1.22  % (13853)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.60/1.22  % (13853)Termination reason: Time limit
% 6.60/1.22  % (13853)Termination phase: Saturation
% 6.60/1.22  
% 6.60/1.22  % (13853)Memory used [KB]: 4861
% 6.60/1.22  % (13853)Time elapsed: 0.800 s
% 6.60/1.22  % (13853)------------------------------
% 6.60/1.22  % (13853)------------------------------
% 6.60/1.23  % (13893)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 6.60/1.25  % (13894)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 7.67/1.37  % (13890)Time limit reached!
% 7.67/1.37  % (13890)------------------------------
% 7.67/1.37  % (13890)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.67/1.37  % (13890)Termination reason: Time limit
% 7.67/1.37  % (13890)Termination phase: Saturation
% 7.67/1.37  
% 7.67/1.37  % (13890)Memory used [KB]: 12537
% 7.67/1.37  % (13890)Time elapsed: 0.400 s
% 7.67/1.37  % (13890)------------------------------
% 7.67/1.37  % (13890)------------------------------
% 7.67/1.38  % (13889)Time limit reached!
% 7.67/1.38  % (13889)------------------------------
% 7.67/1.38  % (13889)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.67/1.38  % (13889)Termination reason: Time limit
% 7.67/1.38  
% 7.67/1.38  % (13889)Memory used [KB]: 6268
% 7.67/1.38  % (13889)Time elapsed: 0.411 s
% 7.67/1.38  % (13889)------------------------------
% 7.67/1.38  % (13889)------------------------------
% 7.67/1.41  % (13834)Time limit reached!
% 7.67/1.41  % (13834)------------------------------
% 7.67/1.41  % (13834)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.67/1.41  % (13834)Termination reason: Time limit
% 7.67/1.41  
% 7.67/1.41  % (13834)Memory used [KB]: 18421
% 7.67/1.41  % (13834)Time elapsed: 1.010 s
% 7.67/1.41  % (13834)------------------------------
% 7.67/1.41  % (13834)------------------------------
% 8.40/1.44  % (13896)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 9.42/1.59  % (13897)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 9.67/1.62  % (13898)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 9.67/1.63  % (13899)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 10.25/1.67  % (13858)Time limit reached!
% 10.25/1.67  % (13858)------------------------------
% 10.25/1.67  % (13858)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.25/1.67  % (13858)Termination reason: Time limit
% 10.25/1.67  
% 10.25/1.67  % (13858)Memory used [KB]: 18038
% 10.25/1.67  % (13858)Time elapsed: 1.237 s
% 10.25/1.67  % (13858)------------------------------
% 10.25/1.67  % (13858)------------------------------
% 10.25/1.73  % (13847)Time limit reached!
% 10.25/1.73  % (13847)------------------------------
% 10.25/1.73  % (13847)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.25/1.73  % (13847)Termination reason: Time limit
% 10.25/1.73  % (13847)Termination phase: Saturation
% 10.25/1.73  
% 10.25/1.73  % (13847)Memory used [KB]: 14839
% 10.25/1.73  % (13847)Time elapsed: 1.300 s
% 10.25/1.73  % (13847)------------------------------
% 10.25/1.73  % (13847)------------------------------
% 10.25/1.74  % (13856)Time limit reached!
% 10.25/1.74  % (13856)------------------------------
% 10.25/1.74  % (13856)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.25/1.75  % (13856)Termination reason: Time limit
% 10.25/1.75  
% 10.25/1.75  % (13856)Memory used [KB]: 17526
% 10.25/1.75  % (13856)Time elapsed: 1.313 s
% 10.25/1.75  % (13856)------------------------------
% 10.25/1.75  % (13856)------------------------------
% 11.86/1.89  % (13900)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 11.86/1.93  % (13902)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 12.37/1.94  % (13836)Time limit reached!
% 12.37/1.94  % (13836)------------------------------
% 12.37/1.94  % (13836)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.37/1.95  % (13901)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 12.37/1.95  % (13859)Time limit reached!
% 12.37/1.95  % (13859)------------------------------
% 12.37/1.95  % (13859)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.37/1.95  % (13836)Termination reason: Time limit
% 12.37/1.96  
% 12.37/1.96  % (13836)Memory used [KB]: 9466
% 12.37/1.96  % (13836)Time elapsed: 1.537 s
% 12.37/1.96  % (13836)------------------------------
% 12.37/1.96  % (13836)------------------------------
% 12.37/1.96  % (13859)Termination reason: Time limit
% 12.37/1.96  % (13859)Termination phase: Saturation
% 12.37/1.96  
% 12.37/1.96  % (13859)Memory used [KB]: 13048
% 12.37/1.96  % (13859)Time elapsed: 1.542 s
% 12.37/1.96  % (13859)------------------------------
% 12.37/1.96  % (13859)------------------------------
% 12.65/1.98  % (13898)Time limit reached!
% 12.65/1.98  % (13898)------------------------------
% 12.65/1.98  % (13898)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.65/1.98  % (13898)Termination reason: Time limit
% 12.65/1.98  
% 12.65/1.98  % (13898)Memory used [KB]: 2174
% 12.65/1.98  % (13898)Time elapsed: 0.523 s
% 12.65/1.98  % (13898)------------------------------
% 12.65/1.98  % (13898)------------------------------
% 13.01/2.04  % (13843)Time limit reached!
% 13.01/2.04  % (13843)------------------------------
% 13.01/2.04  % (13843)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.01/2.04  % (13843)Termination reason: Time limit
% 13.01/2.04  
% 13.01/2.04  % (13843)Memory used [KB]: 14456
% 13.01/2.04  % (13843)Time elapsed: 1.629 s
% 13.01/2.04  % (13843)------------------------------
% 13.01/2.04  % (13843)------------------------------
% 13.62/2.13  % (13905)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 13.84/2.18  % (13904)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 13.84/2.19  % (13906)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 13.84/2.22  % (13907)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 14.26/2.25  % (13892)Time limit reached!
% 14.26/2.25  % (13892)------------------------------
% 14.26/2.25  % (13892)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.26/2.25  % (13892)Termination reason: Time limit
% 14.26/2.25  
% 14.26/2.25  % (13892)Memory used [KB]: 7547
% 14.26/2.25  % (13892)Time elapsed: 1.220 s
% 14.26/2.25  % (13892)------------------------------
% 14.26/2.25  % (13892)------------------------------
% 14.26/2.27  % (13902)Time limit reached!
% 14.26/2.27  % (13902)------------------------------
% 14.26/2.27  % (13902)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.26/2.27  % (13902)Termination reason: Time limit
% 14.26/2.27  
% 14.26/2.27  % (13902)Memory used [KB]: 4093
% 14.26/2.27  % (13902)Time elapsed: 0.419 s
% 14.26/2.27  % (13902)------------------------------
% 14.26/2.27  % (13902)------------------------------
% 15.26/2.32  % (13846)Time limit reached!
% 15.26/2.32  % (13846)------------------------------
% 15.26/2.32  % (13846)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.26/2.32  % (13846)Termination reason: Time limit
% 15.26/2.32  % (13846)Termination phase: Saturation
% 15.26/2.32  
% 15.26/2.32  % (13846)Memory used [KB]: 4861
% 15.26/2.32  % (13846)Time elapsed: 1.849 s
% 15.26/2.32  % (13846)------------------------------
% 15.26/2.32  % (13846)------------------------------
% 16.02/2.42  % (13908)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 16.36/2.44  % (13850)Time limit reached!
% 16.36/2.44  % (13850)------------------------------
% 16.36/2.44  % (13850)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.36/2.44  % (13850)Termination reason: Time limit
% 16.36/2.44  
% 16.36/2.44  % (13850)Memory used [KB]: 15223
% 16.36/2.44  % (13850)Time elapsed: 2.033 s
% 16.36/2.44  % (13850)------------------------------
% 16.36/2.44  % (13850)------------------------------
% 16.48/2.44  % (13909)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 16.48/2.46  % (13906)Time limit reached!
% 16.48/2.46  % (13906)------------------------------
% 16.48/2.46  % (13906)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.48/2.46  % (13906)Termination reason: Time limit
% 16.48/2.46  % (13906)Termination phase: Saturation
% 16.48/2.46  
% 16.48/2.46  % (13906)Memory used [KB]: 1918
% 16.48/2.46  % (13906)Time elapsed: 0.423 s
% 16.48/2.46  % (13906)------------------------------
% 16.48/2.46  % (13906)------------------------------
% 16.48/2.48  % (13838)Time limit reached!
% 16.48/2.48  % (13838)------------------------------
% 16.48/2.48  % (13838)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.48/2.51  % (13838)Termination reason: Time limit
% 16.48/2.51  % (13838)Termination phase: Saturation
% 16.48/2.51  
% 16.48/2.51  % (13838)Memory used [KB]: 18549
% 16.48/2.51  % (13838)Time elapsed: 2.0000 s
% 16.48/2.51  % (13838)------------------------------
% 16.48/2.51  % (13838)------------------------------
% 16.48/2.51  % (13911)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 16.99/2.56  % (13888)Time limit reached!
% 16.99/2.56  % (13888)------------------------------
% 16.99/2.56  % (13888)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.99/2.56  % (13888)Termination reason: Time limit
% 16.99/2.56  % (13888)Termination phase: Saturation
% 16.99/2.56  
% 16.99/2.56  % (13888)Memory used [KB]: 16630
% 16.99/2.56  % (13888)Time elapsed: 1.700 s
% 16.99/2.56  % (13888)------------------------------
% 16.99/2.56  % (13888)------------------------------
% 17.39/2.60  % (13913)dis+3_24_av=off:bd=off:bs=unit_only:fsr=off:fde=unused:gs=on:irw=on:lma=on:nm=0:nwc=1.1:sos=on:uhcvi=on_180 on theBenchmark
% 17.39/2.60  % (13912)ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 17.39/2.64  % (13914)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 18.06/2.69  % (13934)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_34 on theBenchmark
% 19.55/2.84  % (13894)Time limit reached!
% 19.55/2.84  % (13894)------------------------------
% 19.55/2.84  % (13894)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 19.55/2.84  % (13894)Termination reason: Time limit
% 19.55/2.84  
% 19.55/2.84  % (13894)Memory used [KB]: 13688
% 19.55/2.84  % (13894)Time elapsed: 1.746 s
% 19.55/2.84  % (13894)------------------------------
% 19.55/2.84  % (13894)------------------------------
% 19.97/2.90  % (13912)Time limit reached!
% 19.97/2.90  % (13912)------------------------------
% 19.97/2.90  % (13912)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 19.97/2.90  % (13912)Termination reason: Time limit
% 19.97/2.90  % (13912)Termination phase: Saturation
% 19.97/2.90  
% 19.97/2.90  % (13912)Memory used [KB]: 10106
% 19.97/2.90  % (13912)Time elapsed: 0.400 s
% 19.97/2.90  % (13912)------------------------------
% 19.97/2.90  % (13912)------------------------------
% 19.97/2.93  % (13840)Time limit reached!
% 19.97/2.93  % (13840)------------------------------
% 19.97/2.93  % (13840)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 19.97/2.93  % (13840)Termination reason: Time limit
% 19.97/2.93  
% 19.97/2.93  % (13840)Memory used [KB]: 19573
% 19.97/2.93  % (13840)Time elapsed: 2.516 s
% 19.97/2.93  % (13840)------------------------------
% 19.97/2.93  % (13840)------------------------------
% 19.97/2.95  % (13914)Time limit reached!
% 19.97/2.95  % (13914)------------------------------
% 19.97/2.95  % (13914)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 19.97/2.95  % (13914)Termination reason: Time limit
% 19.97/2.95  
% 19.97/2.95  % (13914)Memory used [KB]: 8827
% 19.97/2.95  % (13914)Time elapsed: 0.416 s
% 19.97/2.95  % (13914)------------------------------
% 19.97/2.95  % (13914)------------------------------
% 21.10/3.02  % (13901)Time limit reached!
% 21.10/3.02  % (13901)------------------------------
% 21.10/3.02  % (13901)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 21.10/3.02  % (13901)Termination reason: Time limit
% 21.10/3.02  
% 21.10/3.02  % (13901)Memory used [KB]: 13048
% 21.10/3.02  % (13901)Time elapsed: 1.235 s
% 21.10/3.02  % (13901)------------------------------
% 21.10/3.02  % (13901)------------------------------
% 21.27/3.04  % (13851)Time limit reached!
% 21.27/3.04  % (13851)------------------------------
% 21.27/3.04  % (13851)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 21.27/3.05  % (13851)Termination reason: Time limit
% 21.27/3.05  
% 21.27/3.05  % (13851)Memory used [KB]: 24562
% 21.27/3.05  % (13851)Time elapsed: 2.637 s
% 21.27/3.05  % (13851)------------------------------
% 21.27/3.05  % (13851)------------------------------
% 23.73/3.37  % (13905)Time limit reached!
% 23.73/3.37  % (13905)------------------------------
% 23.73/3.37  % (13905)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 23.73/3.37  % (13905)Termination reason: Time limit
% 23.73/3.37  
% 23.73/3.37  % (13905)Memory used [KB]: 11001
% 23.73/3.37  % (13905)Time elapsed: 1.304 s
% 23.73/3.37  % (13905)------------------------------
% 23.73/3.37  % (13905)------------------------------
% 23.73/3.42  % (13845)Time limit reached!
% 23.73/3.42  % (13845)------------------------------
% 23.73/3.42  % (13845)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 23.73/3.42  % (13845)Termination reason: Time limit
% 23.73/3.42  
% 23.73/3.42  % (13845)Memory used [KB]: 14456
% 23.73/3.42  % (13845)Time elapsed: 3.011 s
% 23.73/3.42  % (13845)------------------------------
% 23.73/3.42  % (13845)------------------------------
% 24.43/3.47  % (13887)Time limit reached!
% 24.43/3.47  % (13887)------------------------------
% 24.43/3.47  % (13887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 24.43/3.48  % (13887)Termination reason: Time limit
% 24.43/3.48  % (13887)Termination phase: Saturation
% 24.43/3.48  
% 24.43/3.48  % (13887)Memory used [KB]: 17398
% 24.43/3.48  % (13887)Time elapsed: 2.800 s
% 24.43/3.48  % (13887)------------------------------
% 24.43/3.48  % (13887)------------------------------
% 24.99/3.55  % (13934)Refutation found. Thanks to Tanya!
% 24.99/3.55  % SZS status Theorem for theBenchmark
% 24.99/3.55  % SZS output start Proof for theBenchmark
% 24.99/3.55  fof(f18860,plain,(
% 24.99/3.55    $false),
% 24.99/3.55    inference(avatar_sat_refutation,[],[f126,f131,f149,f183,f192,f202,f279,f295,f300,f325,f387,f397,f439,f485,f503,f535,f540,f599,f628,f686,f730,f1368,f1372,f1382,f1670,f1723,f1767,f1961,f2101,f2339,f2401,f2415,f2416,f2995,f3310,f3784,f3925,f3968,f4146,f4539,f4618,f5341,f5471,f5517,f5649,f5695,f12204,f12506,f12510,f12941,f13030,f13065,f13404,f13500,f17402,f18044,f18579])).
% 24.99/3.55  fof(f18579,plain,(
% 24.99/3.55    ~spl4_33 | ~spl4_94 | spl4_137 | ~spl4_167 | ~spl4_323 | ~spl4_409),
% 24.99/3.55    inference(avatar_contradiction_clause,[],[f18578])).
% 24.99/3.55  fof(f18578,plain,(
% 24.99/3.55    $false | (~spl4_33 | ~spl4_94 | spl4_137 | ~spl4_167 | ~spl4_323 | ~spl4_409)),
% 24.99/3.55    inference(subsumption_resolution,[],[f18191,f2399])).
% 24.99/3.55  fof(f2399,plain,(
% 24.99/3.55    k4_xboole_0(u1_struct_0(sK0),sK1) != k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) | spl4_137),
% 24.99/3.55    inference(avatar_component_clause,[],[f2398])).
% 24.99/3.55  fof(f2398,plain,(
% 24.99/3.55    spl4_137 <=> k4_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))),
% 24.99/3.55    introduced(avatar_definition,[new_symbols(naming,[spl4_137])])).
% 24.99/3.55  fof(f18191,plain,(
% 24.99/3.55    k4_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) | (~spl4_33 | ~spl4_94 | ~spl4_167 | ~spl4_323 | ~spl4_409)),
% 24.99/3.55    inference(backward_demodulation,[],[f4145,f18080])).
% 24.99/3.55  fof(f18080,plain,(
% 24.99/3.55    sK1 = k1_tops_1(sK0,sK1) | (~spl4_33 | ~spl4_94 | ~spl4_323 | ~spl4_409)),
% 24.99/3.55    inference(backward_demodulation,[],[f598,f18079])).
% 24.99/3.55  fof(f18079,plain,(
% 24.99/3.55    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl4_94 | ~spl4_323 | ~spl4_409)),
% 24.99/3.55    inference(forward_demodulation,[],[f18051,f1722])).
% 24.99/3.55  fof(f1722,plain,(
% 24.99/3.55    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~spl4_94),
% 24.99/3.55    inference(avatar_component_clause,[],[f1720])).
% 24.99/3.55  fof(f1720,plain,(
% 24.99/3.55    spl4_94 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 24.99/3.55    introduced(avatar_definition,[new_symbols(naming,[spl4_94])])).
% 24.99/3.55  fof(f18051,plain,(
% 24.99/3.55    sK1 = k4_xboole_0(sK1,k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)) | (~spl4_323 | ~spl4_409)),
% 24.99/3.55    inference(superposition,[],[f13064,f18043])).
% 24.99/3.55  fof(f18043,plain,(
% 24.99/3.55    sK1 = k3_xboole_0(sK1,k2_pre_topc(sK0,sK1)) | ~spl4_409),
% 24.99/3.55    inference(avatar_component_clause,[],[f18041])).
% 24.99/3.55  fof(f18041,plain,(
% 24.99/3.55    spl4_409 <=> sK1 = k3_xboole_0(sK1,k2_pre_topc(sK0,sK1))),
% 24.99/3.55    introduced(avatar_definition,[new_symbols(naming,[spl4_409])])).
% 24.99/3.55  fof(f13064,plain,(
% 24.99/3.55    ( ! [X49] : (sK1 = k4_xboole_0(sK1,k4_xboole_0(X49,k3_xboole_0(sK1,X49)))) ) | ~spl4_323),
% 24.99/3.55    inference(avatar_component_clause,[],[f13063])).
% 24.99/3.55  fof(f13063,plain,(
% 24.99/3.55    spl4_323 <=> ! [X49] : sK1 = k4_xboole_0(sK1,k4_xboole_0(X49,k3_xboole_0(sK1,X49)))),
% 24.99/3.55    introduced(avatar_definition,[new_symbols(naming,[spl4_323])])).
% 24.99/3.55  fof(f598,plain,(
% 24.99/3.55    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl4_33),
% 24.99/3.55    inference(avatar_component_clause,[],[f596])).
% 24.99/3.55  fof(f596,plain,(
% 24.99/3.55    spl4_33 <=> k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 24.99/3.55    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 24.99/3.55  fof(f4145,plain,(
% 24.99/3.55    k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) | ~spl4_167),
% 24.99/3.55    inference(avatar_component_clause,[],[f4143])).
% 24.99/3.55  fof(f4143,plain,(
% 24.99/3.55    spl4_167 <=> k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1))),
% 24.99/3.55    introduced(avatar_definition,[new_symbols(naming,[spl4_167])])).
% 24.99/3.55  fof(f18044,plain,(
% 24.99/3.55    spl4_409 | ~spl4_27 | ~spl4_117 | ~spl4_335 | ~spl4_392),
% 24.99/3.55    inference(avatar_split_clause,[],[f17997,f17399,f13498,f1958,f501,f18041])).
% 24.99/3.55  fof(f501,plain,(
% 24.99/3.55    spl4_27 <=> ! [X0] : k4_xboole_0(sK1,X0) = k3_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),X0))),
% 24.99/3.55    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 24.99/3.55  fof(f1958,plain,(
% 24.99/3.55    spl4_117 <=> k2_pre_topc(sK0,sK1) = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))),
% 24.99/3.55    introduced(avatar_definition,[new_symbols(naming,[spl4_117])])).
% 24.99/3.55  fof(f13498,plain,(
% 24.99/3.55    spl4_335 <=> ! [X0] : sK1 = k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),X0))),
% 24.99/3.55    introduced(avatar_definition,[new_symbols(naming,[spl4_335])])).
% 24.99/3.55  fof(f17399,plain,(
% 24.99/3.55    spl4_392 <=> k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))),
% 24.99/3.55    introduced(avatar_definition,[new_symbols(naming,[spl4_392])])).
% 24.99/3.55  fof(f17997,plain,(
% 24.99/3.55    sK1 = k3_xboole_0(sK1,k2_pre_topc(sK0,sK1)) | (~spl4_27 | ~spl4_117 | ~spl4_335 | ~spl4_392)),
% 24.99/3.55    inference(backward_demodulation,[],[f3635,f17986])).
% 24.99/3.55  fof(f17986,plain,(
% 24.99/3.55    sK1 = k4_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) | (~spl4_335 | ~spl4_392)),
% 24.99/3.55    inference(superposition,[],[f13499,f17401])).
% 24.99/3.55  fof(f17401,plain,(
% 24.99/3.55    k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) | ~spl4_392),
% 24.99/3.55    inference(avatar_component_clause,[],[f17399])).
% 24.99/3.55  fof(f13499,plain,(
% 24.99/3.55    ( ! [X0] : (sK1 = k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),X0))) ) | ~spl4_335),
% 24.99/3.55    inference(avatar_component_clause,[],[f13498])).
% 24.99/3.55  fof(f3635,plain,(
% 24.99/3.55    k4_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k3_xboole_0(sK1,k2_pre_topc(sK0,sK1)) | (~spl4_27 | ~spl4_117)),
% 24.99/3.55    inference(superposition,[],[f502,f1960])).
% 24.99/3.55  fof(f1960,plain,(
% 24.99/3.55    k2_pre_topc(sK0,sK1) = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) | ~spl4_117),
% 24.99/3.55    inference(avatar_component_clause,[],[f1958])).
% 24.99/3.55  fof(f502,plain,(
% 24.99/3.55    ( ! [X0] : (k4_xboole_0(sK1,X0) = k3_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),X0))) ) | ~spl4_27),
% 24.99/3.55    inference(avatar_component_clause,[],[f501])).
% 24.99/3.55  fof(f17402,plain,(
% 24.99/3.55    spl4_392 | ~spl4_123 | ~spl4_153),
% 24.99/3.55    inference(avatar_split_clause,[],[f5164,f3781,f2099,f17399])).
% 24.99/3.55  fof(f2099,plain,(
% 24.99/3.55    spl4_123 <=> ! [X0] : k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),X0) = k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),X0)),
% 24.99/3.55    introduced(avatar_definition,[new_symbols(naming,[spl4_123])])).
% 24.99/3.55  fof(f3781,plain,(
% 24.99/3.55    spl4_153 <=> k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))),
% 24.99/3.55    introduced(avatar_definition,[new_symbols(naming,[spl4_153])])).
% 24.99/3.55  fof(f5164,plain,(
% 24.99/3.55    k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) | (~spl4_123 | ~spl4_153)),
% 24.99/3.55    inference(superposition,[],[f3783,f2100])).
% 24.99/3.55  fof(f2100,plain,(
% 24.99/3.55    ( ! [X0] : (k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),X0) = k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),X0)) ) | ~spl4_123),
% 24.99/3.55    inference(avatar_component_clause,[],[f2099])).
% 24.99/3.55  fof(f3783,plain,(
% 24.99/3.55    k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) | ~spl4_153),
% 24.99/3.55    inference(avatar_component_clause,[],[f3781])).
% 24.99/3.55  fof(f13500,plain,(
% 24.99/3.55    spl4_335 | ~spl4_323 | ~spl4_333),
% 24.99/3.55    inference(avatar_split_clause,[],[f13439,f13402,f13063,f13498])).
% 24.99/3.55  fof(f13402,plain,(
% 24.99/3.55    spl4_333 <=> ! [X1] : k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),X1))),
% 24.99/3.55    introduced(avatar_definition,[new_symbols(naming,[spl4_333])])).
% 24.99/3.55  fof(f13439,plain,(
% 24.99/3.55    ( ! [X0] : (sK1 = k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),X0))) ) | (~spl4_323 | ~spl4_333)),
% 24.99/3.55    inference(forward_demodulation,[],[f13421,f76])).
% 24.99/3.55  fof(f76,plain,(
% 24.99/3.55    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 24.99/3.55    inference(cnf_transformation,[],[f10])).
% 24.99/3.55  fof(f10,axiom,(
% 24.99/3.55    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 24.99/3.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 24.99/3.55  fof(f13421,plain,(
% 24.99/3.55    ( ! [X0] : (sK1 = k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),X0),k1_xboole_0))) ) | (~spl4_323 | ~spl4_333)),
% 24.99/3.55    inference(superposition,[],[f13064,f13403])).
% 24.99/3.55  fof(f13403,plain,(
% 24.99/3.55    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),X1))) ) | ~spl4_333),
% 24.99/3.55    inference(avatar_component_clause,[],[f13402])).
% 24.99/3.55  fof(f13404,plain,(
% 24.99/3.55    spl4_333 | ~spl4_301 | ~spl4_322),
% 24.99/3.55    inference(avatar_split_clause,[],[f13058,f13027,f12504,f13402])).
% 24.99/3.55  fof(f12504,plain,(
% 24.99/3.55    spl4_301 <=> ! [X68] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X68)),
% 24.99/3.55    introduced(avatar_definition,[new_symbols(naming,[spl4_301])])).
% 24.99/3.55  fof(f13027,plain,(
% 24.99/3.55    spl4_322 <=> k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1))),
% 24.99/3.55    introduced(avatar_definition,[new_symbols(naming,[spl4_322])])).
% 24.99/3.55  fof(f13058,plain,(
% 24.99/3.55    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),X1))) ) | (~spl4_301 | ~spl4_322)),
% 24.99/3.55    inference(forward_demodulation,[],[f13045,f12505])).
% 24.99/3.55  fof(f12505,plain,(
% 24.99/3.55    ( ! [X68] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X68)) ) | ~spl4_301),
% 24.99/3.55    inference(avatar_component_clause,[],[f12504])).
% 24.99/3.55  fof(f13045,plain,(
% 24.99/3.55    ( ! [X1] : (k4_xboole_0(k1_xboole_0,X1) = k3_xboole_0(sK1,k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),X1))) ) | ~spl4_322),
% 24.99/3.55    inference(superposition,[],[f99,f13029])).
% 24.99/3.55  fof(f13029,plain,(
% 24.99/3.55    k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1)) | ~spl4_322),
% 24.99/3.55    inference(avatar_component_clause,[],[f13027])).
% 24.99/3.55  fof(f99,plain,(
% 24.99/3.55    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 24.99/3.55    inference(cnf_transformation,[],[f11])).
% 24.99/3.55  fof(f11,axiom,(
% 24.99/3.55    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 24.99/3.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 24.99/3.55  fof(f13065,plain,(
% 24.99/3.55    spl4_323 | ~spl4_221 | ~spl4_321),
% 24.99/3.55    inference(avatar_split_clause,[],[f13025,f12939,f5515,f13063])).
% 24.99/3.56  fof(f5515,plain,(
% 24.99/3.56    spl4_221 <=> ! [X6] : k4_xboole_0(sK1,X6) = k4_xboole_0(sK1,k3_xboole_0(sK1,X6))),
% 24.99/3.56    introduced(avatar_definition,[new_symbols(naming,[spl4_221])])).
% 24.99/3.56  fof(f12939,plain,(
% 24.99/3.56    spl4_321 <=> ! [X7,X8] : k1_xboole_0 = k3_xboole_0(X7,k4_xboole_0(X8,k3_xboole_0(X7,X8)))),
% 24.99/3.56    introduced(avatar_definition,[new_symbols(naming,[spl4_321])])).
% 24.99/3.56  fof(f13025,plain,(
% 24.99/3.56    ( ! [X49] : (sK1 = k4_xboole_0(sK1,k4_xboole_0(X49,k3_xboole_0(sK1,X49)))) ) | (~spl4_221 | ~spl4_321)),
% 24.99/3.56    inference(forward_demodulation,[],[f13003,f76])).
% 24.99/3.56  fof(f13003,plain,(
% 24.99/3.56    ( ! [X49] : (k4_xboole_0(sK1,k1_xboole_0) = k4_xboole_0(sK1,k4_xboole_0(X49,k3_xboole_0(sK1,X49)))) ) | (~spl4_221 | ~spl4_321)),
% 24.99/3.56    inference(superposition,[],[f5516,f12940])).
% 24.99/3.56  fof(f12940,plain,(
% 24.99/3.56    ( ! [X8,X7] : (k1_xboole_0 = k3_xboole_0(X7,k4_xboole_0(X8,k3_xboole_0(X7,X8)))) ) | ~spl4_321),
% 24.99/3.56    inference(avatar_component_clause,[],[f12939])).
% 24.99/3.56  fof(f5516,plain,(
% 24.99/3.56    ( ! [X6] : (k4_xboole_0(sK1,X6) = k4_xboole_0(sK1,k3_xboole_0(sK1,X6))) ) | ~spl4_221),
% 24.99/3.56    inference(avatar_component_clause,[],[f5515])).
% 24.99/3.56  fof(f13030,plain,(
% 24.99/3.56    spl4_322 | ~spl4_7 | ~spl4_321),
% 24.99/3.56    inference(avatar_split_clause,[],[f12966,f12939,f199,f13027])).
% 24.99/3.56  fof(f199,plain,(
% 24.99/3.56    spl4_7 <=> sK1 = k3_xboole_0(sK1,u1_struct_0(sK0))),
% 24.99/3.56    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 24.99/3.56  fof(f12966,plain,(
% 24.99/3.56    k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1)) | (~spl4_7 | ~spl4_321)),
% 24.99/3.56    inference(superposition,[],[f12940,f201])).
% 24.99/3.56  fof(f201,plain,(
% 24.99/3.56    sK1 = k3_xboole_0(sK1,u1_struct_0(sK0)) | ~spl4_7),
% 24.99/3.56    inference(avatar_component_clause,[],[f199])).
% 24.99/3.56  fof(f12941,plain,(
% 24.99/3.56    spl4_321 | ~spl4_302),
% 24.99/3.56    inference(avatar_split_clause,[],[f12524,f12508,f12939])).
% 24.99/3.56  fof(f12508,plain,(
% 24.99/3.56    spl4_302 <=> ! [X3] : k1_xboole_0 = k4_xboole_0(X3,X3)),
% 24.99/3.56    introduced(avatar_definition,[new_symbols(naming,[spl4_302])])).
% 24.99/3.56  fof(f12524,plain,(
% 24.99/3.56    ( ! [X8,X7] : (k1_xboole_0 = k3_xboole_0(X7,k4_xboole_0(X8,k3_xboole_0(X7,X8)))) ) | ~spl4_302),
% 24.99/3.56    inference(superposition,[],[f12509,f99])).
% 24.99/3.56  fof(f12509,plain,(
% 24.99/3.56    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(X3,X3)) ) | ~spl4_302),
% 24.99/3.56    inference(avatar_component_clause,[],[f12508])).
% 24.99/3.56  fof(f12510,plain,(
% 24.99/3.56    spl4_302 | ~spl4_227 | ~spl4_295),
% 24.99/3.56    inference(avatar_split_clause,[],[f12278,f12202,f5693,f12508])).
% 24.99/3.56  fof(f5693,plain,(
% 24.99/3.56    spl4_227 <=> ! [X13] : ~r2_hidden(X13,k1_xboole_0)),
% 24.99/3.56    introduced(avatar_definition,[new_symbols(naming,[spl4_227])])).
% 24.99/3.56  fof(f12202,plain,(
% 24.99/3.56    spl4_295 <=> ! [X3,X2] : (k1_xboole_0 = k4_xboole_0(X2,X3) | r2_hidden(sK2(X2,X3,k1_xboole_0),X2))),
% 24.99/3.56    introduced(avatar_definition,[new_symbols(naming,[spl4_295])])).
% 24.99/3.56  fof(f12278,plain,(
% 24.99/3.56    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(X3,X3)) ) | (~spl4_227 | ~spl4_295)),
% 24.99/3.56    inference(subsumption_resolution,[],[f12275,f5694])).
% 24.99/3.56  fof(f5694,plain,(
% 24.99/3.56    ( ! [X13] : (~r2_hidden(X13,k1_xboole_0)) ) | ~spl4_227),
% 24.99/3.56    inference(avatar_component_clause,[],[f5693])).
% 24.99/3.56  fof(f12275,plain,(
% 24.99/3.56    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(X3,X3) | r2_hidden(sK2(X3,X3,k1_xboole_0),k1_xboole_0)) ) | ~spl4_295),
% 24.99/3.56    inference(duplicate_literal_removal,[],[f12233])).
% 24.99/3.56  fof(f12233,plain,(
% 24.99/3.56    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(X3,X3) | k1_xboole_0 = k4_xboole_0(X3,X3) | r2_hidden(sK2(X3,X3,k1_xboole_0),k1_xboole_0)) ) | ~spl4_295),
% 24.99/3.56    inference(resolution,[],[f12203,f108])).
% 24.99/3.56  fof(f108,plain,(
% 24.99/3.56    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 24.99/3.56    inference(cnf_transformation,[],[f64])).
% 24.99/3.56  fof(f64,plain,(
% 24.99/3.56    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 24.99/3.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f62,f63])).
% 24.99/3.56  fof(f63,plain,(
% 24.99/3.56    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 24.99/3.56    introduced(choice_axiom,[])).
% 24.99/3.56  fof(f62,plain,(
% 24.99/3.56    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 24.99/3.56    inference(rectify,[],[f61])).
% 24.99/3.56  fof(f61,plain,(
% 24.99/3.56    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 24.99/3.56    inference(flattening,[],[f60])).
% 24.99/3.56  fof(f60,plain,(
% 24.99/3.56    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 24.99/3.56    inference(nnf_transformation,[],[f2])).
% 24.99/3.56  fof(f2,axiom,(
% 24.99/3.56    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 24.99/3.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 24.99/3.56  fof(f12203,plain,(
% 24.99/3.56    ( ! [X2,X3] : (r2_hidden(sK2(X2,X3,k1_xboole_0),X2) | k1_xboole_0 = k4_xboole_0(X2,X3)) ) | ~spl4_295),
% 24.99/3.56    inference(avatar_component_clause,[],[f12202])).
% 24.99/3.56  fof(f12506,plain,(
% 24.99/3.56    spl4_301 | ~spl4_227 | ~spl4_295),
% 24.99/3.56    inference(avatar_split_clause,[],[f12264,f12202,f5693,f12504])).
% 24.99/3.56  fof(f12264,plain,(
% 24.99/3.56    ( ! [X68] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X68)) ) | (~spl4_227 | ~spl4_295)),
% 24.99/3.56    inference(resolution,[],[f12203,f5694])).
% 24.99/3.56  fof(f12204,plain,(
% 24.99/3.56    spl4_295 | ~spl4_227),
% 24.99/3.56    inference(avatar_split_clause,[],[f5697,f5693,f12202])).
% 24.99/3.56  fof(f5697,plain,(
% 24.99/3.56    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,X3) | r2_hidden(sK2(X2,X3,k1_xboole_0),X2)) ) | ~spl4_227),
% 24.99/3.56    inference(resolution,[],[f5694,f107])).
% 24.99/3.56  fof(f107,plain,(
% 24.99/3.56    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 24.99/3.56    inference(cnf_transformation,[],[f64])).
% 24.99/3.56  fof(f5695,plain,(
% 24.99/3.56    spl4_227 | ~spl4_226),
% 24.99/3.56    inference(avatar_split_clause,[],[f5688,f5647,f5693])).
% 24.99/3.56  fof(f5647,plain,(
% 24.99/3.56    spl4_226 <=> ! [X27,X26] : (~r2_hidden(X27,k4_xboole_0(sK1,X26)) | ~r2_hidden(X27,k3_xboole_0(sK1,X26)))),
% 24.99/3.56    introduced(avatar_definition,[new_symbols(naming,[spl4_226])])).
% 24.99/3.56  fof(f5688,plain,(
% 24.99/3.56    ( ! [X13] : (~r2_hidden(X13,k1_xboole_0)) ) | ~spl4_226),
% 24.99/3.56    inference(forward_demodulation,[],[f5687,f75])).
% 24.99/3.56  fof(f75,plain,(
% 24.99/3.56    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 24.99/3.56    inference(cnf_transformation,[],[f8])).
% 24.99/3.56  fof(f8,axiom,(
% 24.99/3.56    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 24.99/3.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 24.99/3.56  fof(f5687,plain,(
% 24.99/3.56    ( ! [X13] : (~r2_hidden(X13,k3_xboole_0(sK1,k1_xboole_0))) ) | ~spl4_226),
% 24.99/3.56    inference(subsumption_resolution,[],[f5673,f121])).
% 24.99/3.56  fof(f121,plain,(
% 24.99/3.56    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 24.99/3.56    inference(equality_resolution,[],[f110])).
% 24.99/3.56  fof(f110,plain,(
% 24.99/3.56    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 24.99/3.56    inference(cnf_transformation,[],[f69])).
% 24.99/3.56  fof(f69,plain,(
% 24.99/3.56    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 24.99/3.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f67,f68])).
% 24.99/3.56  fof(f68,plain,(
% 24.99/3.56    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 24.99/3.56    introduced(choice_axiom,[])).
% 24.99/3.56  fof(f67,plain,(
% 24.99/3.56    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 24.99/3.56    inference(rectify,[],[f66])).
% 24.99/3.56  fof(f66,plain,(
% 24.99/3.56    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 24.99/3.56    inference(flattening,[],[f65])).
% 24.99/3.56  fof(f65,plain,(
% 24.99/3.56    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 24.99/3.56    inference(nnf_transformation,[],[f1])).
% 24.99/3.56  fof(f1,axiom,(
% 24.99/3.56    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 24.99/3.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 24.99/3.56  fof(f5673,plain,(
% 24.99/3.56    ( ! [X13] : (~r2_hidden(X13,sK1) | ~r2_hidden(X13,k3_xboole_0(sK1,k1_xboole_0))) ) | ~spl4_226),
% 24.99/3.56    inference(superposition,[],[f5648,f76])).
% 24.99/3.56  fof(f5648,plain,(
% 24.99/3.56    ( ! [X26,X27] : (~r2_hidden(X27,k4_xboole_0(sK1,X26)) | ~r2_hidden(X27,k3_xboole_0(sK1,X26))) ) | ~spl4_226),
% 24.99/3.56    inference(avatar_component_clause,[],[f5647])).
% 24.99/3.56  fof(f5649,plain,(
% 24.99/3.56    spl4_226 | ~spl4_221),
% 24.99/3.56    inference(avatar_split_clause,[],[f5546,f5515,f5647])).
% 24.99/3.56  fof(f5546,plain,(
% 24.99/3.56    ( ! [X26,X27] : (~r2_hidden(X27,k4_xboole_0(sK1,X26)) | ~r2_hidden(X27,k3_xboole_0(sK1,X26))) ) | ~spl4_221),
% 24.99/3.56    inference(superposition,[],[f117,f5516])).
% 24.99/3.56  fof(f117,plain,(
% 24.99/3.56    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 24.99/3.56    inference(equality_resolution,[],[f105])).
% 24.99/3.56  fof(f105,plain,(
% 24.99/3.56    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 24.99/3.56    inference(cnf_transformation,[],[f64])).
% 24.99/3.56  fof(f5517,plain,(
% 24.99/3.56    spl4_221 | ~spl4_219),
% 24.99/3.56    inference(avatar_split_clause,[],[f5504,f5469,f5515])).
% 24.99/3.56  fof(f5469,plain,(
% 24.99/3.56    spl4_219 <=> ! [X3] : k3_xboole_0(sK1,X3) = k3_xboole_0(sK1,k3_xboole_0(sK1,X3))),
% 24.99/3.56    introduced(avatar_definition,[new_symbols(naming,[spl4_219])])).
% 24.99/3.56  fof(f5504,plain,(
% 24.99/3.56    ( ! [X6] : (k4_xboole_0(sK1,X6) = k4_xboole_0(sK1,k3_xboole_0(sK1,X6))) ) | ~spl4_219),
% 24.99/3.56    inference(forward_demodulation,[],[f5492,f90])).
% 24.99/3.56  fof(f90,plain,(
% 24.99/3.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 24.99/3.56    inference(cnf_transformation,[],[f4])).
% 24.99/3.56  fof(f4,axiom,(
% 24.99/3.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 24.99/3.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 24.99/3.56  fof(f5492,plain,(
% 24.99/3.56    ( ! [X6] : (k4_xboole_0(sK1,k3_xboole_0(sK1,X6)) = k5_xboole_0(sK1,k3_xboole_0(sK1,X6))) ) | ~spl4_219),
% 24.99/3.56    inference(superposition,[],[f90,f5470])).
% 24.99/3.56  fof(f5470,plain,(
% 24.99/3.56    ( ! [X3] : (k3_xboole_0(sK1,X3) = k3_xboole_0(sK1,k3_xboole_0(sK1,X3))) ) | ~spl4_219),
% 24.99/3.56    inference(avatar_component_clause,[],[f5469])).
% 24.99/3.56  fof(f5471,plain,(
% 24.99/3.56    spl4_219 | ~spl4_29 | ~spl4_215),
% 24.99/3.56    inference(avatar_split_clause,[],[f5424,f5339,f532,f5469])).
% 24.99/3.56  fof(f532,plain,(
% 24.99/3.56    spl4_29 <=> sK1 = k4_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1))),
% 24.99/3.56    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 24.99/3.56  fof(f5339,plain,(
% 24.99/3.56    spl4_215 <=> ! [X11,X10] : k3_xboole_0(k4_xboole_0(sK1,X10),X11) = k3_xboole_0(sK1,k3_xboole_0(k4_xboole_0(sK1,X10),X11))),
% 24.99/3.56    introduced(avatar_definition,[new_symbols(naming,[spl4_215])])).
% 24.99/3.56  fof(f5424,plain,(
% 24.99/3.56    ( ! [X3] : (k3_xboole_0(sK1,X3) = k3_xboole_0(sK1,k3_xboole_0(sK1,X3))) ) | (~spl4_29 | ~spl4_215)),
% 24.99/3.56    inference(superposition,[],[f5340,f534])).
% 24.99/3.56  fof(f534,plain,(
% 24.99/3.56    sK1 = k4_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1)) | ~spl4_29),
% 24.99/3.56    inference(avatar_component_clause,[],[f532])).
% 24.99/3.56  fof(f5340,plain,(
% 24.99/3.56    ( ! [X10,X11] : (k3_xboole_0(k4_xboole_0(sK1,X10),X11) = k3_xboole_0(sK1,k3_xboole_0(k4_xboole_0(sK1,X10),X11))) ) | ~spl4_215),
% 24.99/3.56    inference(avatar_component_clause,[],[f5339])).
% 24.99/3.56  fof(f5341,plain,(
% 24.99/3.56    spl4_215 | ~spl4_192),
% 24.99/3.56    inference(avatar_split_clause,[],[f4636,f4616,f5339])).
% 24.99/3.56  fof(f4616,plain,(
% 24.99/3.56    spl4_192 <=> ! [X3] : k4_xboole_0(sK1,X3) = k3_xboole_0(sK1,k4_xboole_0(sK1,X3))),
% 24.99/3.56    introduced(avatar_definition,[new_symbols(naming,[spl4_192])])).
% 24.99/3.56  fof(f4636,plain,(
% 24.99/3.56    ( ! [X10,X11] : (k3_xboole_0(k4_xboole_0(sK1,X10),X11) = k3_xboole_0(sK1,k3_xboole_0(k4_xboole_0(sK1,X10),X11))) ) | ~spl4_192),
% 24.99/3.56    inference(superposition,[],[f100,f4617])).
% 24.99/3.56  fof(f4617,plain,(
% 24.99/3.56    ( ! [X3] : (k4_xboole_0(sK1,X3) = k3_xboole_0(sK1,k4_xboole_0(sK1,X3))) ) | ~spl4_192),
% 24.99/3.56    inference(avatar_component_clause,[],[f4616])).
% 24.99/3.56  fof(f100,plain,(
% 24.99/3.56    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 24.99/3.56    inference(cnf_transformation,[],[f6])).
% 24.99/3.56  fof(f6,axiom,(
% 24.99/3.56    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 24.99/3.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 24.99/3.56  fof(f4618,plain,(
% 24.99/3.56    spl4_192 | ~spl4_21 | ~spl4_29 | ~spl4_187),
% 24.99/3.56    inference(avatar_split_clause,[],[f4602,f4537,f532,f394,f4616])).
% 24.99/3.56  fof(f394,plain,(
% 24.99/3.56    spl4_21 <=> sK1 = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))),
% 24.99/3.56    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 24.99/3.56  fof(f4537,plain,(
% 24.99/3.56    spl4_187 <=> ! [X3,X2] : k3_xboole_0(sK1,k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),X2),X3)) = k4_xboole_0(k4_xboole_0(sK1,X2),X3)),
% 24.99/3.56    introduced(avatar_definition,[new_symbols(naming,[spl4_187])])).
% 24.99/3.56  fof(f4602,plain,(
% 24.99/3.56    ( ! [X3] : (k4_xboole_0(sK1,X3) = k3_xboole_0(sK1,k4_xboole_0(sK1,X3))) ) | (~spl4_21 | ~spl4_29 | ~spl4_187)),
% 24.99/3.56    inference(forward_demodulation,[],[f4565,f534])).
% 24.99/3.56  fof(f4565,plain,(
% 24.99/3.56    ( ! [X3] : (k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1)),X3) = k3_xboole_0(sK1,k4_xboole_0(sK1,X3))) ) | (~spl4_21 | ~spl4_187)),
% 24.99/3.56    inference(superposition,[],[f4538,f396])).
% 24.99/3.56  fof(f396,plain,(
% 24.99/3.56    sK1 = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) | ~spl4_21),
% 24.99/3.56    inference(avatar_component_clause,[],[f394])).
% 24.99/3.56  fof(f4538,plain,(
% 24.99/3.56    ( ! [X2,X3] : (k3_xboole_0(sK1,k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),X2),X3)) = k4_xboole_0(k4_xboole_0(sK1,X2),X3)) ) | ~spl4_187),
% 24.99/3.56    inference(avatar_component_clause,[],[f4537])).
% 24.99/3.56  fof(f4539,plain,(
% 24.99/3.56    spl4_187 | ~spl4_27),
% 24.99/3.56    inference(avatar_split_clause,[],[f519,f501,f4537])).
% 24.99/3.56  fof(f519,plain,(
% 24.99/3.56    ( ! [X2,X3] : (k3_xboole_0(sK1,k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),X2),X3)) = k4_xboole_0(k4_xboole_0(sK1,X2),X3)) ) | ~spl4_27),
% 24.99/3.56    inference(superposition,[],[f99,f502])).
% 24.99/3.56  fof(f4146,plain,(
% 24.99/3.56    spl4_167 | ~spl4_42 | ~spl4_50 | ~spl4_51),
% 24.99/3.56    inference(avatar_split_clause,[],[f4011,f911,f907,f727,f4143])).
% 24.99/3.56  fof(f727,plain,(
% 24.99/3.56    spl4_42 <=> k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)))),
% 24.99/3.56    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 24.99/3.56  fof(f907,plain,(
% 24.99/3.56    spl4_50 <=> m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 24.99/3.56    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).
% 24.99/3.56  fof(f911,plain,(
% 24.99/3.56    spl4_51 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 24.99/3.56    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).
% 24.99/3.56  fof(f4011,plain,(
% 24.99/3.56    k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) | (~spl4_42 | ~spl4_50 | ~spl4_51)),
% 24.99/3.56    inference(forward_demodulation,[],[f4010,f3938])).
% 24.99/3.56  fof(f3938,plain,(
% 24.99/3.56    k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) = k4_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) | ~spl4_51),
% 24.99/3.56    inference(resolution,[],[f913,f93])).
% 24.99/3.56  fof(f93,plain,(
% 24.99/3.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 24.99/3.56    inference(cnf_transformation,[],[f44])).
% 24.99/3.56  fof(f44,plain,(
% 24.99/3.56    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 24.99/3.56    inference(ennf_transformation,[],[f13])).
% 24.99/3.56  fof(f13,axiom,(
% 24.99/3.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 24.99/3.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 24.99/3.56  fof(f913,plain,(
% 24.99/3.56    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_51),
% 24.99/3.56    inference(avatar_component_clause,[],[f911])).
% 24.99/3.56  fof(f4010,plain,(
% 24.99/3.56    k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) | (~spl4_42 | ~spl4_50)),
% 24.99/3.56    inference(forward_demodulation,[],[f3983,f729])).
% 24.99/3.56  fof(f729,plain,(
% 24.99/3.56    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))) | ~spl4_42),
% 24.99/3.56    inference(avatar_component_clause,[],[f727])).
% 24.99/3.56  fof(f3983,plain,(
% 24.99/3.56    k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)))) | ~spl4_50),
% 24.99/3.56    inference(resolution,[],[f908,f94])).
% 24.99/3.56  fof(f94,plain,(
% 24.99/3.56    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 24.99/3.56    inference(cnf_transformation,[],[f45])).
% 24.99/3.56  fof(f45,plain,(
% 24.99/3.56    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 24.99/3.56    inference(ennf_transformation,[],[f16])).
% 24.99/3.56  fof(f16,axiom,(
% 24.99/3.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 24.99/3.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 24.99/3.56  fof(f908,plain,(
% 24.99/3.56    m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_50),
% 24.99/3.56    inference(avatar_component_clause,[],[f907])).
% 24.99/3.56  fof(f3968,plain,(
% 24.99/3.56    spl4_50 | ~spl4_18 | ~spl4_23 | ~spl4_134),
% 24.99/3.56    inference(avatar_split_clause,[],[f3912,f2336,f436,f322,f907])).
% 24.99/3.56  fof(f322,plain,(
% 24.99/3.56    spl4_18 <=> m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 24.99/3.56    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 24.99/3.56  fof(f436,plain,(
% 24.99/3.56    spl4_23 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 24.99/3.56    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 24.99/3.56  fof(f2336,plain,(
% 24.99/3.56    spl4_134 <=> k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1))),
% 24.99/3.56    introduced(avatar_definition,[new_symbols(naming,[spl4_134])])).
% 24.99/3.56  fof(f3912,plain,(
% 24.99/3.56    m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_18 | ~spl4_23 | ~spl4_134)),
% 24.99/3.56    inference(subsumption_resolution,[],[f3911,f324])).
% 24.99/3.56  fof(f324,plain,(
% 24.99/3.56    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_18),
% 24.99/3.56    inference(avatar_component_clause,[],[f322])).
% 24.99/3.56  fof(f3911,plain,(
% 24.99/3.56    m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_23 | ~spl4_134)),
% 24.99/3.56    inference(subsumption_resolution,[],[f3906,f438])).
% 24.99/3.56  fof(f438,plain,(
% 24.99/3.56    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_23),
% 24.99/3.56    inference(avatar_component_clause,[],[f436])).
% 24.99/3.56  fof(f3906,plain,(
% 24.99/3.56    m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_134),
% 24.99/3.56    inference(superposition,[],[f103,f2338])).
% 24.99/3.56  fof(f2338,plain,(
% 24.99/3.56    k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) | ~spl4_134),
% 24.99/3.56    inference(avatar_component_clause,[],[f2336])).
% 24.99/3.56  fof(f103,plain,(
% 24.99/3.56    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 24.99/3.56    inference(cnf_transformation,[],[f52])).
% 24.99/3.56  fof(f52,plain,(
% 24.99/3.56    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 24.99/3.56    inference(flattening,[],[f51])).
% 24.99/3.56  fof(f51,plain,(
% 24.99/3.56    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 24.99/3.56    inference(ennf_transformation,[],[f15])).
% 24.99/3.56  fof(f15,axiom,(
% 24.99/3.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 24.99/3.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 24.99/3.56  fof(f3925,plain,(
% 24.99/3.56    spl4_51 | ~spl4_18 | ~spl4_23 | ~spl4_42 | ~spl4_134),
% 24.99/3.56    inference(avatar_split_clause,[],[f3913,f2336,f727,f436,f322,f911])).
% 24.99/3.56  fof(f3913,plain,(
% 24.99/3.56    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_18 | ~spl4_23 | ~spl4_42 | ~spl4_134)),
% 24.99/3.56    inference(subsumption_resolution,[],[f3158,f3912])).
% 24.99/3.56  fof(f3158,plain,(
% 24.99/3.56    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_42),
% 24.99/3.56    inference(superposition,[],[f92,f729])).
% 24.99/3.56  fof(f92,plain,(
% 24.99/3.56    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 24.99/3.56    inference(cnf_transformation,[],[f43])).
% 24.99/3.56  fof(f43,plain,(
% 24.99/3.56    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 24.99/3.56    inference(ennf_transformation,[],[f14])).
% 24.99/3.56  fof(f14,axiom,(
% 24.99/3.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 24.99/3.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 24.99/3.56  fof(f3784,plain,(
% 24.99/3.56    spl4_153 | ~spl4_2 | ~spl4_3 | ~spl4_16 | ~spl4_18 | ~spl4_36),
% 24.99/3.56    inference(avatar_split_clause,[],[f659,f625,f322,f297,f146,f128,f3781])).
% 24.99/3.56  fof(f128,plain,(
% 24.99/3.56    spl4_2 <=> l1_pre_topc(sK0)),
% 24.99/3.56    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 24.99/3.56  fof(f146,plain,(
% 24.99/3.56    spl4_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 24.99/3.56    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 24.99/3.56  fof(f297,plain,(
% 24.99/3.56    spl4_16 <=> sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))),
% 24.99/3.56    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 24.99/3.56  fof(f625,plain,(
% 24.99/3.56    spl4_36 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 24.99/3.56    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 24.99/3.56  fof(f659,plain,(
% 24.99/3.56    k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) | (~spl4_2 | ~spl4_3 | ~spl4_16 | ~spl4_18 | ~spl4_36)),
% 24.99/3.56    inference(backward_demodulation,[],[f355,f641])).
% 24.99/3.56  fof(f641,plain,(
% 24.99/3.56    k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) | ~spl4_36),
% 24.99/3.56    inference(resolution,[],[f627,f93])).
% 24.99/3.56  fof(f627,plain,(
% 24.99/3.56    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_36),
% 24.99/3.56    inference(avatar_component_clause,[],[f625])).
% 24.99/3.56  fof(f355,plain,(
% 24.99/3.56    k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) | (~spl4_2 | ~spl4_3 | ~spl4_16 | ~spl4_18)),
% 24.99/3.56    inference(backward_demodulation,[],[f350,f354])).
% 24.99/3.56  fof(f354,plain,(
% 24.99/3.56    k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) | (~spl4_2 | ~spl4_16 | ~spl4_18)),
% 24.99/3.56    inference(forward_demodulation,[],[f353,f299])).
% 24.99/3.56  fof(f299,plain,(
% 24.99/3.56    sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) | ~spl4_16),
% 24.99/3.56    inference(avatar_component_clause,[],[f297])).
% 24.99/3.56  fof(f353,plain,(
% 24.99/3.56    k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)))) | (~spl4_2 | ~spl4_18)),
% 24.99/3.56    inference(subsumption_resolution,[],[f329,f130])).
% 24.99/3.56  fof(f130,plain,(
% 24.99/3.56    l1_pre_topc(sK0) | ~spl4_2),
% 24.99/3.56    inference(avatar_component_clause,[],[f128])).
% 24.99/3.56  fof(f329,plain,(
% 24.99/3.56    k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)))) | ~l1_pre_topc(sK0) | ~spl4_18),
% 24.99/3.56    inference(resolution,[],[f324,f80])).
% 24.99/3.56  fof(f80,plain,(
% 24.99/3.56    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 24.99/3.56    inference(cnf_transformation,[],[f37])).
% 24.99/3.56  fof(f37,plain,(
% 24.99/3.56    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 24.99/3.56    inference(ennf_transformation,[],[f21])).
% 24.99/3.56  fof(f21,axiom,(
% 24.99/3.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 24.99/3.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).
% 24.99/3.56  fof(f350,plain,(
% 24.99/3.56    k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) | (~spl4_2 | ~spl4_3 | ~spl4_18)),
% 24.99/3.56    inference(forward_demodulation,[],[f349,f177])).
% 24.99/3.56  fof(f177,plain,(
% 24.99/3.56    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) | (~spl4_2 | ~spl4_3)),
% 24.99/3.56    inference(backward_demodulation,[],[f168,f162])).
% 24.99/3.56  fof(f162,plain,(
% 24.99/3.56    k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) | ~spl4_3),
% 24.99/3.56    inference(resolution,[],[f148,f93])).
% 24.99/3.56  fof(f148,plain,(
% 24.99/3.56    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_3),
% 24.99/3.56    inference(avatar_component_clause,[],[f146])).
% 24.99/3.56  fof(f168,plain,(
% 24.99/3.56    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl4_2 | ~spl4_3)),
% 24.99/3.56    inference(subsumption_resolution,[],[f150,f130])).
% 24.99/3.56  fof(f150,plain,(
% 24.99/3.56    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0) | ~spl4_3),
% 24.99/3.56    inference(resolution,[],[f148,f77])).
% 24.99/3.56  fof(f77,plain,(
% 24.99/3.56    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 24.99/3.56    inference(cnf_transformation,[],[f34])).
% 24.99/3.56  fof(f34,plain,(
% 24.99/3.56    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 24.99/3.56    inference(ennf_transformation,[],[f26])).
% 24.99/3.56  fof(f26,axiom,(
% 24.99/3.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))))),
% 24.99/3.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).
% 24.99/3.56  fof(f349,plain,(
% 24.99/3.56    k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))) | (~spl4_2 | ~spl4_18)),
% 24.99/3.56    inference(subsumption_resolution,[],[f327,f130])).
% 24.99/3.56  fof(f327,plain,(
% 24.99/3.56    k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))) | ~l1_pre_topc(sK0) | ~spl4_18),
% 24.99/3.56    inference(resolution,[],[f324,f78])).
% 24.99/3.56  fof(f78,plain,(
% 24.99/3.56    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 24.99/3.56    inference(cnf_transformation,[],[f35])).
% 24.99/3.56  fof(f35,plain,(
% 24.99/3.56    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 24.99/3.56    inference(ennf_transformation,[],[f28])).
% 24.99/3.56  fof(f28,axiom,(
% 24.99/3.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 24.99/3.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 24.99/3.56  fof(f3310,plain,(
% 24.99/3.56    ~spl4_137 | spl4_19 | ~spl4_1 | ~spl4_2 | ~spl4_18),
% 24.99/3.56    inference(avatar_split_clause,[],[f361,f322,f128,f123,f379,f2398])).
% 24.99/3.56  fof(f379,plain,(
% 24.99/3.56    spl4_19 <=> v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)),
% 24.99/3.56    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 24.99/3.56  fof(f123,plain,(
% 24.99/3.56    spl4_1 <=> v2_pre_topc(sK0)),
% 24.99/3.56    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 24.99/3.56  fof(f361,plain,(
% 24.99/3.56    v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | k4_xboole_0(u1_struct_0(sK0),sK1) != k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) | (~spl4_1 | ~spl4_2 | ~spl4_18)),
% 24.99/3.56    inference(subsumption_resolution,[],[f360,f130])).
% 24.99/3.56  fof(f360,plain,(
% 24.99/3.56    v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | k4_xboole_0(u1_struct_0(sK0),sK1) != k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0) | (~spl4_1 | ~spl4_18)),
% 24.99/3.56    inference(subsumption_resolution,[],[f332,f125])).
% 24.99/3.56  fof(f125,plain,(
% 24.99/3.56    v2_pre_topc(sK0) | ~spl4_1),
% 24.99/3.56    inference(avatar_component_clause,[],[f123])).
% 24.99/3.56  fof(f332,plain,(
% 24.99/3.56    v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | k4_xboole_0(u1_struct_0(sK0),sK1) != k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~spl4_18),
% 24.99/3.56    inference(resolution,[],[f324,f83])).
% 24.99/3.56  fof(f83,plain,(
% 24.99/3.56    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 24.99/3.56    inference(cnf_transformation,[],[f40])).
% 24.99/3.56  fof(f40,plain,(
% 24.99/3.56    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 24.99/3.56    inference(flattening,[],[f39])).
% 24.99/3.56  fof(f39,plain,(
% 24.99/3.56    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 24.99/3.56    inference(ennf_transformation,[],[f20])).
% 24.99/3.56  fof(f20,axiom,(
% 24.99/3.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 24.99/3.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 24.99/3.56  fof(f2995,plain,(
% 24.99/3.56    ~spl4_5 | ~spl4_16 | ~spl4_42 | ~spl4_81 | ~spl4_96 | ~spl4_137),
% 24.99/3.56    inference(avatar_contradiction_clause,[],[f2994])).
% 24.99/3.56  fof(f2994,plain,(
% 24.99/3.56    $false | (~spl4_5 | ~spl4_16 | ~spl4_42 | ~spl4_81 | ~spl4_96 | ~spl4_137)),
% 24.99/3.56    inference(subsumption_resolution,[],[f187,f2735])).
% 24.99/3.56  fof(f2735,plain,(
% 24.99/3.56    ~v3_pre_topc(sK1,sK0) | (~spl4_16 | ~spl4_42 | ~spl4_81 | ~spl4_96 | ~spl4_137)),
% 24.99/3.56    inference(trivial_inequality_removal,[],[f2734])).
% 24.99/3.56  fof(f2734,plain,(
% 24.99/3.56    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0) | (~spl4_16 | ~spl4_42 | ~spl4_81 | ~spl4_96 | ~spl4_137)),
% 24.99/3.56    inference(backward_demodulation,[],[f2406,f2503])).
% 24.99/3.56  fof(f2503,plain,(
% 24.99/3.56    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (~spl4_16 | ~spl4_42 | ~spl4_96 | ~spl4_137)),
% 24.99/3.56    inference(backward_demodulation,[],[f1766,f2444])).
% 24.99/3.56  fof(f2444,plain,(
% 24.99/3.56    sK1 = k1_tops_1(sK0,sK1) | (~spl4_16 | ~spl4_42 | ~spl4_137)),
% 24.99/3.56    inference(forward_demodulation,[],[f2439,f299])).
% 24.99/3.56  fof(f2439,plain,(
% 24.99/3.56    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) | (~spl4_42 | ~spl4_137)),
% 24.99/3.56    inference(backward_demodulation,[],[f729,f2400])).
% 24.99/3.56  fof(f2400,plain,(
% 24.99/3.56    k4_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) | ~spl4_137),
% 24.99/3.56    inference(avatar_component_clause,[],[f2398])).
% 24.99/3.56  fof(f1766,plain,(
% 24.99/3.56    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~spl4_96),
% 24.99/3.56    inference(avatar_component_clause,[],[f1764])).
% 24.99/3.56  fof(f1764,plain,(
% 24.99/3.56    spl4_96 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 24.99/3.56    introduced(avatar_definition,[new_symbols(naming,[spl4_96])])).
% 24.99/3.56  fof(f2406,plain,(
% 24.99/3.56    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0) | ~spl4_81),
% 24.99/3.56    inference(forward_demodulation,[],[f74,f1371])).
% 24.99/3.56  fof(f1371,plain,(
% 24.99/3.56    ( ! [X0] : (k4_xboole_0(k2_pre_topc(sK0,sK1),X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0)) ) | ~spl4_81),
% 24.99/3.56    inference(avatar_component_clause,[],[f1370])).
% 24.99/3.56  fof(f1370,plain,(
% 24.99/3.56    spl4_81 <=> ! [X0] : k4_xboole_0(k2_pre_topc(sK0,sK1),X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0)),
% 24.99/3.56    introduced(avatar_definition,[new_symbols(naming,[spl4_81])])).
% 24.99/3.56  fof(f74,plain,(
% 24.99/3.56    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 24.99/3.56    inference(cnf_transformation,[],[f57])).
% 24.99/3.56  fof(f57,plain,(
% 24.99/3.56    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 24.99/3.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f54,f56,f55])).
% 24.99/3.56  fof(f55,plain,(
% 24.99/3.56    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 24.99/3.56    introduced(choice_axiom,[])).
% 24.99/3.56  fof(f56,plain,(
% 24.99/3.56    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 24.99/3.56    introduced(choice_axiom,[])).
% 24.99/3.56  fof(f54,plain,(
% 24.99/3.56    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 24.99/3.56    inference(flattening,[],[f53])).
% 24.99/3.56  fof(f53,plain,(
% 24.99/3.56    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 24.99/3.56    inference(nnf_transformation,[],[f33])).
% 24.99/3.56  fof(f33,plain,(
% 24.99/3.56    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 24.99/3.56    inference(flattening,[],[f32])).
% 24.99/3.56  fof(f32,plain,(
% 24.99/3.56    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 24.99/3.56    inference(ennf_transformation,[],[f30])).
% 24.99/3.56  fof(f30,negated_conjecture,(
% 24.99/3.56    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 24.99/3.56    inference(negated_conjecture,[],[f29])).
% 24.99/3.56  fof(f29,conjecture,(
% 24.99/3.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 24.99/3.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).
% 24.99/3.56  fof(f187,plain,(
% 24.99/3.56    v3_pre_topc(sK1,sK0) | ~spl4_5),
% 24.99/3.56    inference(avatar_component_clause,[],[f185])).
% 24.99/3.56  fof(f185,plain,(
% 24.99/3.56    spl4_5 <=> v3_pre_topc(sK1,sK0)),
% 24.99/3.56    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 24.99/3.56  fof(f2416,plain,(
% 24.99/3.56    ~spl4_19 | spl4_5 | ~spl4_2 | ~spl4_16 | ~spl4_18),
% 24.99/3.56    inference(avatar_split_clause,[],[f2405,f322,f297,f128,f185,f379])).
% 24.99/3.56  fof(f2405,plain,(
% 24.99/3.56    v3_pre_topc(sK1,sK0) | ~v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | (~spl4_2 | ~spl4_16 | ~spl4_18)),
% 24.99/3.56    inference(subsumption_resolution,[],[f2404,f130])).
% 24.99/3.56  fof(f2404,plain,(
% 24.99/3.56    v3_pre_topc(sK1,sK0) | ~v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | ~l1_pre_topc(sK0) | (~spl4_16 | ~spl4_18)),
% 24.99/3.56    inference(subsumption_resolution,[],[f368,f324])).
% 24.99/3.56  fof(f368,plain,(
% 24.99/3.56    v3_pre_topc(sK1,sK0) | ~v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl4_16),
% 24.99/3.56    inference(superposition,[],[f84,f299])).
% 24.99/3.56  fof(f84,plain,(
% 24.99/3.56    ( ! [X0,X1] : (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 24.99/3.56    inference(cnf_transformation,[],[f58])).
% 24.99/3.56  fof(f58,plain,(
% 24.99/3.56    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 24.99/3.56    inference(nnf_transformation,[],[f41])).
% 24.99/3.56  fof(f41,plain,(
% 24.99/3.56    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 24.99/3.56    inference(ennf_transformation,[],[f25])).
% 24.99/3.56  fof(f25,axiom,(
% 24.99/3.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 24.99/3.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).
% 24.99/3.56  fof(f2415,plain,(
% 24.99/3.56    spl4_19 | ~spl4_5 | ~spl4_2 | ~spl4_16 | ~spl4_18),
% 24.99/3.56    inference(avatar_split_clause,[],[f2403,f322,f297,f128,f185,f379])).
% 24.99/3.56  fof(f2403,plain,(
% 24.99/3.56    ~v3_pre_topc(sK1,sK0) | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | (~spl4_2 | ~spl4_16 | ~spl4_18)),
% 24.99/3.56    inference(subsumption_resolution,[],[f2402,f130])).
% 24.99/3.56  fof(f2402,plain,(
% 24.99/3.56    ~v3_pre_topc(sK1,sK0) | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | ~l1_pre_topc(sK0) | (~spl4_16 | ~spl4_18)),
% 24.99/3.56    inference(subsumption_resolution,[],[f369,f324])).
% 24.99/3.56  fof(f369,plain,(
% 24.99/3.56    ~v3_pre_topc(sK1,sK0) | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl4_16),
% 24.99/3.56    inference(superposition,[],[f85,f299])).
% 24.99/3.56  fof(f85,plain,(
% 24.99/3.56    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 24.99/3.56    inference(cnf_transformation,[],[f58])).
% 24.99/3.56  fof(f2401,plain,(
% 24.99/3.56    ~spl4_19 | spl4_137 | ~spl4_2 | ~spl4_18),
% 24.99/3.56    inference(avatar_split_clause,[],[f359,f322,f128,f2398,f379])).
% 24.99/3.56  fof(f359,plain,(
% 24.99/3.56    k4_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) | ~v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | (~spl4_2 | ~spl4_18)),
% 24.99/3.56    inference(subsumption_resolution,[],[f331,f130])).
% 24.99/3.56  fof(f331,plain,(
% 24.99/3.56    k4_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) | ~v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | ~l1_pre_topc(sK0) | ~spl4_18),
% 24.99/3.56    inference(resolution,[],[f324,f82])).
% 24.99/3.56  fof(f82,plain,(
% 24.99/3.56    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 24.99/3.56    inference(cnf_transformation,[],[f40])).
% 24.99/3.56  fof(f2339,plain,(
% 24.99/3.56    spl4_134 | ~spl4_2 | ~spl4_3 | ~spl4_18),
% 24.99/3.56    inference(avatar_split_clause,[],[f352,f322,f146,f128,f2336])).
% 24.99/3.56  fof(f352,plain,(
% 24.99/3.56    k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) | (~spl4_2 | ~spl4_3 | ~spl4_18)),
% 24.99/3.56    inference(forward_demodulation,[],[f351,f177])).
% 24.99/3.56  fof(f351,plain,(
% 24.99/3.56    k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))) | (~spl4_2 | ~spl4_18)),
% 24.99/3.56    inference(subsumption_resolution,[],[f328,f130])).
% 24.99/3.56  fof(f328,plain,(
% 24.99/3.56    k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))) | ~l1_pre_topc(sK0) | ~spl4_18),
% 24.99/3.56    inference(resolution,[],[f324,f79])).
% 24.99/3.56  fof(f79,plain,(
% 24.99/3.56    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 24.99/3.56    inference(cnf_transformation,[],[f36])).
% 24.99/3.56  fof(f36,plain,(
% 24.99/3.56    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 24.99/3.56    inference(ennf_transformation,[],[f27])).
% 24.99/3.56  fof(f27,axiom,(
% 24.99/3.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 24.99/3.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 24.99/3.56  fof(f2101,plain,(
% 24.99/3.56    spl4_123 | ~spl4_18),
% 24.99/3.56    inference(avatar_split_clause,[],[f341,f322,f2099])).
% 24.99/3.56  fof(f341,plain,(
% 24.99/3.56    ( ! [X0] : (k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),X0) = k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),X0)) ) | ~spl4_18),
% 24.99/3.56    inference(resolution,[],[f324,f102])).
% 24.99/3.56  fof(f102,plain,(
% 24.99/3.56    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 24.99/3.56    inference(cnf_transformation,[],[f50])).
% 24.99/3.56  fof(f50,plain,(
% 24.99/3.56    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 24.99/3.56    inference(ennf_transformation,[],[f17])).
% 24.99/3.56  fof(f17,axiom,(
% 24.99/3.56    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 24.99/3.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 24.99/3.56  fof(f1961,plain,(
% 24.99/3.56    spl4_117 | ~spl4_83 | ~spl4_93),
% 24.99/3.56    inference(avatar_split_clause,[],[f1708,f1667,f1379,f1958])).
% 24.99/3.56  fof(f1379,plain,(
% 24.99/3.56    spl4_83 <=> k2_pre_topc(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))),
% 24.99/3.56    introduced(avatar_definition,[new_symbols(naming,[spl4_83])])).
% 24.99/3.56  fof(f1667,plain,(
% 24.99/3.56    spl4_93 <=> m1_subset_1(k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 24.99/3.56    introduced(avatar_definition,[new_symbols(naming,[spl4_93])])).
% 24.99/3.56  fof(f1708,plain,(
% 24.99/3.56    k2_pre_topc(sK0,sK1) = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) | (~spl4_83 | ~spl4_93)),
% 24.99/3.56    inference(forward_demodulation,[],[f1683,f1381])).
% 24.99/3.56  fof(f1381,plain,(
% 24.99/3.56    k2_pre_topc(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) | ~spl4_83),
% 24.99/3.56    inference(avatar_component_clause,[],[f1379])).
% 24.99/3.56  fof(f1683,plain,(
% 24.99/3.56    k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) | ~spl4_93),
% 24.99/3.56    inference(resolution,[],[f1669,f93])).
% 24.99/3.56  fof(f1669,plain,(
% 24.99/3.56    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_93),
% 24.99/3.56    inference(avatar_component_clause,[],[f1667])).
% 24.99/3.56  fof(f1767,plain,(
% 24.99/3.56    spl4_96 | ~spl4_38 | ~spl4_81),
% 24.99/3.56    inference(avatar_split_clause,[],[f1712,f1370,f683,f1764])).
% 24.99/3.56  fof(f683,plain,(
% 24.99/3.56    spl4_38 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 24.99/3.56    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 24.99/3.56  fof(f1712,plain,(
% 24.99/3.56    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl4_38 | ~spl4_81)),
% 24.99/3.56    inference(superposition,[],[f1371,f685])).
% 24.99/3.56  fof(f685,plain,(
% 24.99/3.56    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~spl4_38),
% 24.99/3.56    inference(avatar_component_clause,[],[f683])).
% 24.99/3.56  fof(f1723,plain,(
% 24.99/3.56    spl4_94 | ~spl4_6 | ~spl4_81),
% 24.99/3.56    inference(avatar_split_clause,[],[f1711,f1370,f189,f1720])).
% 24.99/3.56  fof(f189,plain,(
% 24.99/3.56    spl4_6 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 24.99/3.56    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 24.99/3.56  fof(f1711,plain,(
% 24.99/3.56    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (~spl4_6 | ~spl4_81)),
% 24.99/3.56    inference(superposition,[],[f1371,f191])).
% 24.99/3.56  fof(f191,plain,(
% 24.99/3.56    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl4_6),
% 24.99/3.56    inference(avatar_component_clause,[],[f189])).
% 24.99/3.56  fof(f1670,plain,(
% 24.99/3.56    spl4_93 | ~spl4_36 | ~spl4_80),
% 24.99/3.56    inference(avatar_split_clause,[],[f1665,f1365,f625,f1667])).
% 24.99/3.56  fof(f1365,plain,(
% 24.99/3.56    spl4_80 <=> k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))),
% 24.99/3.56    introduced(avatar_definition,[new_symbols(naming,[spl4_80])])).
% 24.99/3.56  fof(f1665,plain,(
% 24.99/3.56    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_36 | ~spl4_80)),
% 24.99/3.56    inference(subsumption_resolution,[],[f1660,f627])).
% 24.99/3.56  fof(f1660,plain,(
% 24.99/3.56    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_80),
% 24.99/3.56    inference(superposition,[],[f92,f1367])).
% 24.99/3.56  fof(f1367,plain,(
% 24.99/3.56    k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) | ~spl4_80),
% 24.99/3.56    inference(avatar_component_clause,[],[f1365])).
% 24.99/3.56  fof(f1382,plain,(
% 24.99/3.56    spl4_83 | ~spl4_36),
% 24.99/3.56    inference(avatar_split_clause,[],[f661,f625,f1379])).
% 24.99/3.56  fof(f661,plain,(
% 24.99/3.56    k2_pre_topc(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) | ~spl4_36),
% 24.99/3.56    inference(forward_demodulation,[],[f642,f641])).
% 24.99/3.56  fof(f642,plain,(
% 24.99/3.56    k2_pre_topc(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) | ~spl4_36),
% 24.99/3.56    inference(resolution,[],[f627,f94])).
% 24.99/3.56  fof(f1372,plain,(
% 24.99/3.56    spl4_81 | ~spl4_36),
% 24.99/3.56    inference(avatar_split_clause,[],[f644,f625,f1370])).
% 24.99/3.56  fof(f644,plain,(
% 24.99/3.56    ( ! [X0] : (k4_xboole_0(k2_pre_topc(sK0,sK1),X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0)) ) | ~spl4_36),
% 24.99/3.56    inference(resolution,[],[f627,f102])).
% 24.99/3.56  fof(f1368,plain,(
% 24.99/3.56    spl4_80 | ~spl4_36),
% 24.99/3.56    inference(avatar_split_clause,[],[f641,f625,f1365])).
% 24.99/3.56  fof(f730,plain,(
% 24.99/3.56    spl4_42 | ~spl4_2 | ~spl4_3),
% 24.99/3.56    inference(avatar_split_clause,[],[f176,f146,f128,f727])).
% 24.99/3.56  fof(f176,plain,(
% 24.99/3.56    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))) | (~spl4_2 | ~spl4_3)),
% 24.99/3.56    inference(backward_demodulation,[],[f171,f162])).
% 24.99/3.56  fof(f171,plain,(
% 24.99/3.56    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | (~spl4_2 | ~spl4_3)),
% 24.99/3.56    inference(subsumption_resolution,[],[f153,f130])).
% 24.99/3.56  fof(f153,plain,(
% 24.99/3.56    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | ~l1_pre_topc(sK0) | ~spl4_3),
% 24.99/3.56    inference(resolution,[],[f148,f80])).
% 24.99/3.56  fof(f686,plain,(
% 24.99/3.56    spl4_38 | ~spl4_2 | ~spl4_3),
% 24.99/3.56    inference(avatar_split_clause,[],[f172,f146,f128,f683])).
% 24.99/3.56  fof(f172,plain,(
% 24.99/3.56    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl4_2 | ~spl4_3)),
% 24.99/3.56    inference(subsumption_resolution,[],[f154,f130])).
% 24.99/3.56  fof(f154,plain,(
% 24.99/3.56    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~spl4_3),
% 24.99/3.56    inference(resolution,[],[f148,f81])).
% 24.99/3.56  fof(f81,plain,(
% 24.99/3.56    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 24.99/3.56    inference(cnf_transformation,[],[f38])).
% 24.99/3.56  fof(f38,plain,(
% 24.99/3.56    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 24.99/3.56    inference(ennf_transformation,[],[f24])).
% 24.99/3.56  fof(f24,axiom,(
% 24.99/3.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 24.99/3.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 24.99/3.56  fof(f628,plain,(
% 24.99/3.56    spl4_36 | ~spl4_3 | ~spl4_23 | ~spl4_30),
% 24.99/3.56    inference(avatar_split_clause,[],[f623,f537,f436,f146,f625])).
% 24.99/3.56  fof(f537,plain,(
% 24.99/3.56    spl4_30 <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 24.99/3.56    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 24.99/3.56  fof(f623,plain,(
% 24.99/3.56    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_3 | ~spl4_23 | ~spl4_30)),
% 24.99/3.56    inference(subsumption_resolution,[],[f622,f148])).
% 24.99/3.56  fof(f622,plain,(
% 24.99/3.56    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_23 | ~spl4_30)),
% 24.99/3.56    inference(subsumption_resolution,[],[f621,f438])).
% 24.99/3.56  fof(f621,plain,(
% 24.99/3.56    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_30),
% 24.99/3.56    inference(superposition,[],[f103,f539])).
% 24.99/3.56  fof(f539,plain,(
% 24.99/3.56    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl4_30),
% 24.99/3.56    inference(avatar_component_clause,[],[f537])).
% 24.99/3.56  fof(f599,plain,(
% 24.99/3.56    spl4_33 | ~spl4_15 | ~spl4_26),
% 24.99/3.56    inference(avatar_split_clause,[],[f591,f482,f293,f596])).
% 24.99/3.56  fof(f293,plain,(
% 24.99/3.56    spl4_15 <=> ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)),
% 24.99/3.56    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 24.99/3.56  fof(f482,plain,(
% 24.99/3.56    spl4_26 <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 24.99/3.56    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 24.99/3.56  fof(f591,plain,(
% 24.99/3.56    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl4_15 | ~spl4_26)),
% 24.99/3.56    inference(superposition,[],[f484,f294])).
% 24.99/3.56  fof(f294,plain,(
% 24.99/3.56    ( ! [X0] : (k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)) ) | ~spl4_15),
% 24.99/3.56    inference(avatar_component_clause,[],[f293])).
% 24.99/3.56  fof(f484,plain,(
% 24.99/3.56    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl4_26),
% 24.99/3.56    inference(avatar_component_clause,[],[f482])).
% 24.99/3.56  fof(f540,plain,(
% 24.99/3.56    spl4_30 | ~spl4_2 | ~spl4_3),
% 24.99/3.56    inference(avatar_split_clause,[],[f170,f146,f128,f537])).
% 24.99/3.56  fof(f170,plain,(
% 24.99/3.56    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl4_2 | ~spl4_3)),
% 24.99/3.56    inference(subsumption_resolution,[],[f152,f130])).
% 24.99/3.56  fof(f152,plain,(
% 24.99/3.56    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~spl4_3),
% 24.99/3.56    inference(resolution,[],[f148,f79])).
% 24.99/3.56  fof(f535,plain,(
% 24.99/3.56    spl4_29 | ~spl4_21 | ~spl4_27),
% 24.99/3.56    inference(avatar_split_clause,[],[f529,f501,f394,f532])).
% 24.99/3.56  fof(f529,plain,(
% 24.99/3.56    sK1 = k4_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1)) | (~spl4_21 | ~spl4_27)),
% 24.99/3.56    inference(forward_demodulation,[],[f508,f86])).
% 24.99/3.56  fof(f86,plain,(
% 24.99/3.56    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 24.99/3.56    inference(cnf_transformation,[],[f31])).
% 24.99/3.56  fof(f31,plain,(
% 24.99/3.56    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 24.99/3.56    inference(rectify,[],[f3])).
% 24.99/3.56  fof(f3,axiom,(
% 24.99/3.56    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 24.99/3.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 24.99/3.56  fof(f508,plain,(
% 24.99/3.56    k4_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1)) = k3_xboole_0(sK1,sK1) | (~spl4_21 | ~spl4_27)),
% 24.99/3.56    inference(superposition,[],[f502,f396])).
% 24.99/3.56  fof(f503,plain,(
% 24.99/3.56    spl4_27 | ~spl4_7),
% 24.99/3.56    inference(avatar_split_clause,[],[f207,f199,f501])).
% 24.99/3.56  fof(f207,plain,(
% 24.99/3.56    ( ! [X0] : (k4_xboole_0(sK1,X0) = k3_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),X0))) ) | ~spl4_7),
% 24.99/3.56    inference(superposition,[],[f99,f201])).
% 24.99/3.56  fof(f485,plain,(
% 24.99/3.56    spl4_26 | ~spl4_2 | ~spl4_3),
% 24.99/3.56    inference(avatar_split_clause,[],[f169,f146,f128,f482])).
% 24.99/3.56  fof(f169,plain,(
% 24.99/3.56    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl4_2 | ~spl4_3)),
% 24.99/3.56    inference(subsumption_resolution,[],[f151,f130])).
% 24.99/3.56  fof(f151,plain,(
% 24.99/3.56    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~spl4_3),
% 24.99/3.56    inference(resolution,[],[f148,f78])).
% 24.99/3.56  fof(f439,plain,(
% 24.99/3.56    spl4_23 | ~spl4_2 | ~spl4_18 | ~spl4_20),
% 24.99/3.56    inference(avatar_split_clause,[],[f434,f384,f322,f128,f436])).
% 24.99/3.56  fof(f384,plain,(
% 24.99/3.56    spl4_20 <=> k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))),
% 24.99/3.56    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 24.99/3.56  fof(f434,plain,(
% 24.99/3.56    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_2 | ~spl4_18 | ~spl4_20)),
% 24.99/3.56    inference(subsumption_resolution,[],[f433,f130])).
% 24.99/3.56  fof(f433,plain,(
% 24.99/3.56    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl4_18 | ~spl4_20)),
% 24.99/3.56    inference(subsumption_resolution,[],[f430,f324])).
% 24.99/3.56  fof(f430,plain,(
% 24.99/3.56    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl4_20),
% 24.99/3.56    inference(superposition,[],[f96,f386])).
% 24.99/3.56  fof(f386,plain,(
% 24.99/3.56    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) | ~spl4_20),
% 24.99/3.56    inference(avatar_component_clause,[],[f384])).
% 24.99/3.56  fof(f96,plain,(
% 24.99/3.56    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 24.99/3.56    inference(cnf_transformation,[],[f49])).
% 24.99/3.56  fof(f49,plain,(
% 24.99/3.56    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 24.99/3.56    inference(flattening,[],[f48])).
% 24.99/3.56  fof(f48,plain,(
% 24.99/3.56    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 24.99/3.56    inference(ennf_transformation,[],[f22])).
% 24.99/3.56  fof(f22,axiom,(
% 24.99/3.56    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 24.99/3.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 24.99/3.56  fof(f397,plain,(
% 24.99/3.56    spl4_21 | ~spl4_16 | ~spl4_18),
% 24.99/3.56    inference(avatar_split_clause,[],[f362,f322,f297,f394])).
% 24.99/3.56  fof(f362,plain,(
% 24.99/3.56    sK1 = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) | (~spl4_16 | ~spl4_18)),
% 24.99/3.56    inference(forward_demodulation,[],[f338,f299])).
% 24.99/3.56  fof(f338,plain,(
% 24.99/3.56    k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) | ~spl4_18),
% 24.99/3.56    inference(resolution,[],[f324,f93])).
% 24.99/3.56  fof(f387,plain,(
% 24.99/3.56    spl4_20 | ~spl4_2 | ~spl4_3),
% 24.99/3.56    inference(avatar_split_clause,[],[f177,f146,f128,f384])).
% 24.99/3.56  fof(f325,plain,(
% 24.99/3.56    spl4_18 | ~spl4_3 | ~spl4_14),
% 24.99/3.56    inference(avatar_split_clause,[],[f310,f276,f146,f322])).
% 24.99/3.56  fof(f276,plain,(
% 24.99/3.56    spl4_14 <=> k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1)),
% 24.99/3.56    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 24.99/3.56  fof(f310,plain,(
% 24.99/3.56    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_3 | ~spl4_14)),
% 24.99/3.56    inference(subsumption_resolution,[],[f306,f148])).
% 24.99/3.56  fof(f306,plain,(
% 24.99/3.56    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_14),
% 24.99/3.56    inference(superposition,[],[f92,f278])).
% 24.99/3.56  fof(f278,plain,(
% 24.99/3.56    k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) | ~spl4_14),
% 24.99/3.56    inference(avatar_component_clause,[],[f276])).
% 24.99/3.56  fof(f300,plain,(
% 24.99/3.56    spl4_16 | ~spl4_3),
% 24.99/3.56    inference(avatar_split_clause,[],[f178,f146,f297])).
% 24.99/3.56  fof(f178,plain,(
% 24.99/3.56    sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) | ~spl4_3),
% 24.99/3.56    inference(forward_demodulation,[],[f163,f162])).
% 24.99/3.56  fof(f163,plain,(
% 24.99/3.56    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl4_3),
% 24.99/3.56    inference(resolution,[],[f148,f94])).
% 24.99/3.56  fof(f295,plain,(
% 24.99/3.56    spl4_15 | ~spl4_3),
% 24.99/3.56    inference(avatar_split_clause,[],[f165,f146,f293])).
% 24.99/3.56  fof(f165,plain,(
% 24.99/3.56    ( ! [X0] : (k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)) ) | ~spl4_3),
% 24.99/3.56    inference(resolution,[],[f148,f102])).
% 24.99/3.56  fof(f279,plain,(
% 24.99/3.56    spl4_14 | ~spl4_3),
% 24.99/3.56    inference(avatar_split_clause,[],[f162,f146,f276])).
% 24.99/3.56  fof(f202,plain,(
% 24.99/3.56    spl4_7 | ~spl4_4),
% 24.99/3.56    inference(avatar_split_clause,[],[f197,f180,f199])).
% 24.99/3.56  fof(f180,plain,(
% 24.99/3.56    spl4_4 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 24.99/3.56    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 24.99/3.56  fof(f197,plain,(
% 24.99/3.56    sK1 = k3_xboole_0(sK1,u1_struct_0(sK0)) | ~spl4_4),
% 24.99/3.56    inference(resolution,[],[f182,f91])).
% 24.99/3.56  fof(f91,plain,(
% 24.99/3.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 24.99/3.56    inference(cnf_transformation,[],[f42])).
% 24.99/3.56  fof(f42,plain,(
% 24.99/3.56    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 24.99/3.56    inference(ennf_transformation,[],[f7])).
% 24.99/3.56  fof(f7,axiom,(
% 24.99/3.56    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 24.99/3.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 24.99/3.56  fof(f182,plain,(
% 24.99/3.56    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl4_4),
% 24.99/3.56    inference(avatar_component_clause,[],[f180])).
% 24.99/3.56  fof(f192,plain,(
% 24.99/3.56    spl4_5 | spl4_6),
% 24.99/3.56    inference(avatar_split_clause,[],[f73,f189,f185])).
% 24.99/3.56  fof(f73,plain,(
% 24.99/3.56    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 24.99/3.56    inference(cnf_transformation,[],[f57])).
% 24.99/3.56  fof(f183,plain,(
% 24.99/3.56    spl4_4 | ~spl4_3),
% 24.99/3.56    inference(avatar_split_clause,[],[f164,f146,f180])).
% 24.99/3.56  fof(f164,plain,(
% 24.99/3.56    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl4_3),
% 24.99/3.56    inference(resolution,[],[f148,f97])).
% 24.99/3.56  fof(f97,plain,(
% 24.99/3.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 24.99/3.56    inference(cnf_transformation,[],[f59])).
% 24.99/3.56  fof(f59,plain,(
% 24.99/3.56    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 24.99/3.56    inference(nnf_transformation,[],[f19])).
% 24.99/3.56  fof(f19,axiom,(
% 24.99/3.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 24.99/3.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 24.99/3.56  fof(f149,plain,(
% 24.99/3.56    spl4_3),
% 24.99/3.56    inference(avatar_split_clause,[],[f72,f146])).
% 24.99/3.56  fof(f72,plain,(
% 24.99/3.56    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 24.99/3.56    inference(cnf_transformation,[],[f57])).
% 24.99/3.56  fof(f131,plain,(
% 24.99/3.56    spl4_2),
% 24.99/3.56    inference(avatar_split_clause,[],[f71,f128])).
% 24.99/3.56  fof(f71,plain,(
% 24.99/3.56    l1_pre_topc(sK0)),
% 24.99/3.56    inference(cnf_transformation,[],[f57])).
% 24.99/3.56  fof(f126,plain,(
% 24.99/3.56    spl4_1),
% 24.99/3.56    inference(avatar_split_clause,[],[f70,f123])).
% 24.99/3.56  fof(f70,plain,(
% 24.99/3.56    v2_pre_topc(sK0)),
% 24.99/3.56    inference(cnf_transformation,[],[f57])).
% 24.99/3.56  % SZS output end Proof for theBenchmark
% 24.99/3.56  % (13934)------------------------------
% 24.99/3.56  % (13934)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 24.99/3.56  % (13934)Termination reason: Refutation
% 24.99/3.56  
% 24.99/3.56  % (13934)Memory used [KB]: 19445
% 24.99/3.56  % (13934)Time elapsed: 0.928 s
% 24.99/3.56  % (13934)------------------------------
% 24.99/3.56  % (13934)------------------------------
% 25.60/3.58  % (13831)Success in time 3.229 s
%------------------------------------------------------------------------------
