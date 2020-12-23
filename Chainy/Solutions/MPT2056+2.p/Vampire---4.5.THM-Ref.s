%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT2056+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:40 EST 2020

% Result     : Theorem 5.58s
% Output     : Refutation 5.58s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 200 expanded)
%              Number of leaves         :   31 (  92 expanded)
%              Depth                    :   10
%              Number of atoms          :  373 ( 951 expanded)
%              Number of equality atoms :   47 ( 133 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20545,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f8517,f8521,f8525,f8529,f8533,f8537,f8541,f8545,f8556,f8764,f8806,f9779,f9780,f9865,f9876,f10102,f14283,f20538,f20544])).

fof(f20544,plain,
    ( k2_struct_0(sK216) != u1_struct_0(sK216)
    | k2_yellow19(sK216,k3_yellow19(sK216,u1_struct_0(sK216),sK217)) != k4_xboole_0(sK217,k1_tarski(k1_xboole_0))
    | sK217 != k4_xboole_0(sK217,k1_tarski(k1_xboole_0))
    | sK217 = k2_yellow19(sK216,k3_yellow19(sK216,k2_struct_0(sK216),sK217)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f20538,plain,
    ( spl470_1282
    | ~ spl470_25
    | ~ spl470_324 ),
    inference(avatar_split_clause,[],[f20528,f11161,f8804,f20536])).

fof(f20536,plain,
    ( spl470_1282
  <=> sK217 = k4_xboole_0(sK217,k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl470_1282])])).

fof(f8804,plain,
    ( spl470_25
  <=> ! [X3] :
        ( ~ r2_hidden(X3,sK217)
        | ~ v1_xboole_0(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl470_25])])).

fof(f11161,plain,
    ( spl470_324
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl470_324])])).

fof(f20528,plain,
    ( sK217 = k4_xboole_0(sK217,k1_tarski(k1_xboole_0))
    | ~ spl470_25
    | ~ spl470_324 ),
    inference(resolution,[],[f10193,f14282])).

fof(f14282,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl470_324 ),
    inference(avatar_component_clause,[],[f11161])).

fof(f10193,plain,
    ( ! [X14] :
        ( ~ v1_xboole_0(X14)
        | sK217 = k4_xboole_0(sK217,k1_tarski(X14)) )
    | ~ spl470_25 ),
    inference(resolution,[],[f8805,f8127])).

fof(f8127,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ),
    inference(cnf_transformation,[],[f6571])).

fof(f6571,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f421])).

fof(f421,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f8805,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK217)
        | ~ v1_xboole_0(X3) )
    | ~ spl470_25 ),
    inference(avatar_component_clause,[],[f8804])).

fof(f14283,plain,(
    spl470_324 ),
    inference(avatar_split_clause,[],[f7047,f11161])).

fof(f7047,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f10102,plain,
    ( spl470_20
    | ~ spl470_5
    | ~ spl470_10 ),
    inference(avatar_split_clause,[],[f10066,f8554,f8531,f8772])).

fof(f8772,plain,
    ( spl470_20
  <=> v1_subset_1(sK217,u1_struct_0(k3_yellow_1(u1_struct_0(sK216)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl470_20])])).

fof(f8531,plain,
    ( spl470_5
  <=> v1_subset_1(sK217,u1_struct_0(k3_yellow_1(k2_struct_0(sK216)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl470_5])])).

fof(f8554,plain,
    ( spl470_10
  <=> k2_struct_0(sK216) = u1_struct_0(sK216) ),
    introduced(avatar_definition,[new_symbols(naming,[spl470_10])])).

fof(f10066,plain,
    ( v1_subset_1(sK217,u1_struct_0(k3_yellow_1(u1_struct_0(sK216))))
    | ~ spl470_5
    | ~ spl470_10 ),
    inference(superposition,[],[f8532,f8555])).

fof(f8555,plain,
    ( k2_struct_0(sK216) = u1_struct_0(sK216)
    | ~ spl470_10 ),
    inference(avatar_component_clause,[],[f8554])).

fof(f8532,plain,
    ( v1_subset_1(sK217,u1_struct_0(k3_yellow_1(k2_struct_0(sK216))))
    | ~ spl470_5 ),
    inference(avatar_component_clause,[],[f8531])).

fof(f9876,plain,
    ( spl470_8
    | ~ spl470_7
    | ~ spl470_22 ),
    inference(avatar_split_clause,[],[f9871,f8778,f8539,f8543])).

fof(f8543,plain,
    ( spl470_8
  <=> v2_struct_0(sK216) ),
    introduced(avatar_definition,[new_symbols(naming,[spl470_8])])).

fof(f8539,plain,
    ( spl470_7
  <=> l1_struct_0(sK216) ),
    introduced(avatar_definition,[new_symbols(naming,[spl470_7])])).

fof(f8778,plain,
    ( spl470_22
  <=> v1_xboole_0(u1_struct_0(sK216)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl470_22])])).

fof(f9871,plain,
    ( ~ l1_struct_0(sK216)
    | v2_struct_0(sK216)
    | ~ spl470_22 ),
    inference(resolution,[],[f8779,f6881])).

fof(f6881,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4638])).

fof(f4638,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4637])).

fof(f4637,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1795])).

fof(f1795,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f8779,plain,
    ( v1_xboole_0(u1_struct_0(sK216))
    | ~ spl470_22 ),
    inference(avatar_component_clause,[],[f8778])).

fof(f9865,plain,
    ( spl470_172
    | ~ spl470_2
    | ~ spl470_10
    | ~ spl470_17 ),
    inference(avatar_split_clause,[],[f9835,f8756,f8554,f8519,f9863])).

fof(f9863,plain,
    ( spl470_172
  <=> k2_yellow19(sK216,k3_yellow19(sK216,u1_struct_0(sK216),sK217)) = k4_xboole_0(sK217,k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl470_172])])).

fof(f8519,plain,
    ( spl470_2
  <=> m1_subset_1(sK217,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK216))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl470_2])])).

fof(f8756,plain,
    ( spl470_17
  <=> k2_yellow19(sK216,k3_yellow19(sK216,u1_struct_0(sK216),sK217)) = k7_subset_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK216))),sK217,k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl470_17])])).

fof(f9835,plain,
    ( k2_yellow19(sK216,k3_yellow19(sK216,u1_struct_0(sK216),sK217)) = k4_xboole_0(sK217,k1_tarski(k1_xboole_0))
    | ~ spl470_2
    | ~ spl470_10
    | ~ spl470_17 ),
    inference(forward_demodulation,[],[f8757,f9675])).

fof(f9675,plain,
    ( ! [X89] : k4_xboole_0(sK217,X89) = k7_subset_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK216))),sK217,X89)
    | ~ spl470_2
    | ~ spl470_10 ),
    inference(forward_demodulation,[],[f8722,f8555])).

fof(f8722,plain,
    ( ! [X89] : k4_xboole_0(sK217,X89) = k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK216))),sK217,X89)
    | ~ spl470_2 ),
    inference(resolution,[],[f8520,f6957])).

fof(f6957,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f4676])).

fof(f4676,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f494])).

fof(f494,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f8520,plain,
    ( m1_subset_1(sK217,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK216)))))
    | ~ spl470_2 ),
    inference(avatar_component_clause,[],[f8519])).

fof(f8757,plain,
    ( k2_yellow19(sK216,k3_yellow19(sK216,u1_struct_0(sK216),sK217)) = k7_subset_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK216))),sK217,k1_tarski(k1_xboole_0))
    | ~ spl470_17 ),
    inference(avatar_component_clause,[],[f8756])).

fof(f9780,plain,
    ( k2_struct_0(sK216) != u1_struct_0(sK216)
    | v2_waybel_0(sK217,k3_yellow_1(u1_struct_0(sK216)))
    | ~ v2_waybel_0(sK217,k3_yellow_1(k2_struct_0(sK216))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f9779,plain,
    ( k2_struct_0(sK216) != u1_struct_0(sK216)
    | v13_waybel_0(sK217,k3_yellow_1(u1_struct_0(sK216)))
    | ~ v13_waybel_0(sK217,k3_yellow_1(k2_struct_0(sK216))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f8806,plain,
    ( spl470_6
    | spl470_25
    | ~ spl470_18
    | ~ spl470_19
    | ~ spl470_20
    | spl470_22
    | ~ spl470_2
    | ~ spl470_10 ),
    inference(avatar_split_clause,[],[f8802,f8554,f8519,f8778,f8772,f8762,f8759,f8804,f8535])).

fof(f8535,plain,
    ( spl470_6
  <=> v1_xboole_0(sK217) ),
    introduced(avatar_definition,[new_symbols(naming,[spl470_6])])).

fof(f8759,plain,
    ( spl470_18
  <=> v13_waybel_0(sK217,k3_yellow_1(u1_struct_0(sK216))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl470_18])])).

fof(f8762,plain,
    ( spl470_19
  <=> v2_waybel_0(sK217,k3_yellow_1(u1_struct_0(sK216))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl470_19])])).

fof(f8802,plain,
    ( ! [X3] :
        ( v1_xboole_0(u1_struct_0(sK216))
        | ~ v1_subset_1(sK217,u1_struct_0(k3_yellow_1(u1_struct_0(sK216))))
        | ~ v2_waybel_0(sK217,k3_yellow_1(u1_struct_0(sK216)))
        | ~ v13_waybel_0(sK217,k3_yellow_1(u1_struct_0(sK216)))
        | ~ r2_hidden(X3,sK217)
        | ~ v1_xboole_0(X3)
        | v1_xboole_0(sK217) )
    | ~ spl470_2
    | ~ spl470_10 ),
    inference(forward_demodulation,[],[f8801,f8555])).

fof(f8801,plain,
    ( ! [X3] :
        ( ~ v1_subset_1(sK217,u1_struct_0(k3_yellow_1(u1_struct_0(sK216))))
        | ~ v2_waybel_0(sK217,k3_yellow_1(u1_struct_0(sK216)))
        | ~ v13_waybel_0(sK217,k3_yellow_1(u1_struct_0(sK216)))
        | ~ r2_hidden(X3,sK217)
        | ~ v1_xboole_0(X3)
        | v1_xboole_0(sK217)
        | v1_xboole_0(k2_struct_0(sK216)) )
    | ~ spl470_2
    | ~ spl470_10 ),
    inference(forward_demodulation,[],[f8800,f8555])).

fof(f8800,plain,
    ( ! [X3] :
        ( ~ v2_waybel_0(sK217,k3_yellow_1(u1_struct_0(sK216)))
        | ~ v13_waybel_0(sK217,k3_yellow_1(u1_struct_0(sK216)))
        | ~ r2_hidden(X3,sK217)
        | ~ v1_xboole_0(X3)
        | ~ v1_subset_1(sK217,u1_struct_0(k3_yellow_1(k2_struct_0(sK216))))
        | v1_xboole_0(sK217)
        | v1_xboole_0(k2_struct_0(sK216)) )
    | ~ spl470_2
    | ~ spl470_10 ),
    inference(forward_demodulation,[],[f8799,f8555])).

fof(f8799,plain,
    ( ! [X3] :
        ( ~ v13_waybel_0(sK217,k3_yellow_1(u1_struct_0(sK216)))
        | ~ r2_hidden(X3,sK217)
        | ~ v1_xboole_0(X3)
        | ~ v2_waybel_0(sK217,k3_yellow_1(k2_struct_0(sK216)))
        | ~ v1_subset_1(sK217,u1_struct_0(k3_yellow_1(k2_struct_0(sK216))))
        | v1_xboole_0(sK217)
        | v1_xboole_0(k2_struct_0(sK216)) )
    | ~ spl470_2
    | ~ spl470_10 ),
    inference(forward_demodulation,[],[f8590,f8555])).

fof(f8590,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK217)
        | ~ v1_xboole_0(X3)
        | ~ v13_waybel_0(sK217,k3_yellow_1(k2_struct_0(sK216)))
        | ~ v2_waybel_0(sK217,k3_yellow_1(k2_struct_0(sK216)))
        | ~ v1_subset_1(sK217,u1_struct_0(k3_yellow_1(k2_struct_0(sK216))))
        | v1_xboole_0(sK217)
        | v1_xboole_0(k2_struct_0(sK216)) )
    | ~ spl470_2 ),
    inference(resolution,[],[f8520,f6777])).

fof(f6777,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | ~ r2_hidden(X2,X1)
      | ~ v1_xboole_0(X2)
      | ~ v13_waybel_0(X1,k3_yellow_1(X0))
      | ~ v2_waybel_0(X1,k3_yellow_1(X0))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f4590])).

fof(f4590,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ v1_xboole_0(X2)
              | ~ r2_hidden(X2,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          | ~ v13_waybel_0(X1,k3_yellow_1(X0))
          | ~ v2_waybel_0(X1,k3_yellow_1(X0))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f4589])).

fof(f4589,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ v1_xboole_0(X2)
              | ~ r2_hidden(X2,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          | ~ v13_waybel_0(X1,k3_yellow_1(X0))
          | ~ v2_waybel_0(X1,k3_yellow_1(X0))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4522])).

fof(f4522,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
            & v13_waybel_0(X1,k3_yellow_1(X0))
            & v2_waybel_0(X1,k3_yellow_1(X0))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ~ ( v1_xboole_0(X2)
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow19)).

fof(f8764,plain,
    ( spl470_8
    | ~ spl470_7
    | spl470_6
    | spl470_17
    | ~ spl470_18
    | ~ spl470_19
    | ~ spl470_2
    | ~ spl470_10 ),
    inference(avatar_split_clause,[],[f8752,f8554,f8519,f8762,f8759,f8756,f8535,f8539,f8543])).

fof(f8752,plain,
    ( ~ v2_waybel_0(sK217,k3_yellow_1(u1_struct_0(sK216)))
    | ~ v13_waybel_0(sK217,k3_yellow_1(u1_struct_0(sK216)))
    | k2_yellow19(sK216,k3_yellow19(sK216,u1_struct_0(sK216),sK217)) = k7_subset_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK216))),sK217,k1_tarski(k1_xboole_0))
    | v1_xboole_0(sK217)
    | ~ l1_struct_0(sK216)
    | v2_struct_0(sK216)
    | ~ spl470_2
    | ~ spl470_10 ),
    inference(forward_demodulation,[],[f8751,f8555])).

fof(f8751,plain,
    ( ~ v13_waybel_0(sK217,k3_yellow_1(u1_struct_0(sK216)))
    | k2_yellow19(sK216,k3_yellow19(sK216,u1_struct_0(sK216),sK217)) = k7_subset_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK216))),sK217,k1_tarski(k1_xboole_0))
    | ~ v2_waybel_0(sK217,k3_yellow_1(k2_struct_0(sK216)))
    | v1_xboole_0(sK217)
    | ~ l1_struct_0(sK216)
    | v2_struct_0(sK216)
    | ~ spl470_2
    | ~ spl470_10 ),
    inference(forward_demodulation,[],[f8750,f8555])).

fof(f8750,plain,
    ( k2_yellow19(sK216,k3_yellow19(sK216,u1_struct_0(sK216),sK217)) = k7_subset_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK216))),sK217,k1_tarski(k1_xboole_0))
    | ~ v13_waybel_0(sK217,k3_yellow_1(k2_struct_0(sK216)))
    | ~ v2_waybel_0(sK217,k3_yellow_1(k2_struct_0(sK216)))
    | v1_xboole_0(sK217)
    | ~ l1_struct_0(sK216)
    | v2_struct_0(sK216)
    | ~ spl470_2
    | ~ spl470_10 ),
    inference(forward_demodulation,[],[f8586,f8555])).

fof(f8586,plain,
    ( k2_yellow19(sK216,k3_yellow19(sK216,k2_struct_0(sK216),sK217)) = k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK216))),sK217,k1_tarski(k1_xboole_0))
    | ~ v13_waybel_0(sK217,k3_yellow_1(k2_struct_0(sK216)))
    | ~ v2_waybel_0(sK217,k3_yellow_1(k2_struct_0(sK216)))
    | v1_xboole_0(sK217)
    | ~ l1_struct_0(sK216)
    | v2_struct_0(sK216)
    | ~ spl470_2 ),
    inference(resolution,[],[f8520,f6724])).

fof(f6724,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4564])).

fof(f4564,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4563])).

fof(f4563,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4519])).

fof(f4519,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow19)).

fof(f8556,plain,
    ( spl470_10
    | ~ spl470_7 ),
    inference(avatar_split_clause,[],[f8551,f8539,f8554])).

fof(f8551,plain,
    ( k2_struct_0(sK216) = u1_struct_0(sK216)
    | ~ spl470_7 ),
    inference(resolution,[],[f8540,f6847])).

fof(f6847,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4615])).

fof(f4615,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1773])).

fof(f1773,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f8540,plain,
    ( l1_struct_0(sK216)
    | ~ spl470_7 ),
    inference(avatar_component_clause,[],[f8539])).

fof(f8545,plain,(
    ~ spl470_8 ),
    inference(avatar_split_clause,[],[f6692,f8543])).

fof(f6692,plain,(
    ~ v2_struct_0(sK216) ),
    inference(cnf_transformation,[],[f5763])).

fof(f5763,plain,
    ( sK217 != k2_yellow19(sK216,k3_yellow19(sK216,k2_struct_0(sK216),sK217))
    & m1_subset_1(sK217,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK216)))))
    & v13_waybel_0(sK217,k3_yellow_1(k2_struct_0(sK216)))
    & v2_waybel_0(sK217,k3_yellow_1(k2_struct_0(sK216)))
    & v1_subset_1(sK217,u1_struct_0(k3_yellow_1(k2_struct_0(sK216))))
    & ~ v1_xboole_0(sK217)
    & l1_struct_0(sK216)
    & ~ v2_struct_0(sK216) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK216,sK217])],[f4548,f5762,f5761])).

fof(f5761,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k2_yellow19(sK216,k3_yellow19(sK216,k2_struct_0(sK216),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK216)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK216)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK216)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK216))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(sK216)
      & ~ v2_struct_0(sK216) ) ),
    introduced(choice_axiom,[])).

fof(f5762,plain,
    ( ? [X1] :
        ( k2_yellow19(sK216,k3_yellow19(sK216,k2_struct_0(sK216),X1)) != X1
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK216)))))
        & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK216)))
        & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK216)))
        & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK216))))
        & ~ v1_xboole_0(X1) )
   => ( sK217 != k2_yellow19(sK216,k3_yellow19(sK216,k2_struct_0(sK216),sK217))
      & m1_subset_1(sK217,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK216)))))
      & v13_waybel_0(sK217,k3_yellow_1(k2_struct_0(sK216)))
      & v2_waybel_0(sK217,k3_yellow_1(k2_struct_0(sK216)))
      & v1_subset_1(sK217,u1_struct_0(k3_yellow_1(k2_struct_0(sK216))))
      & ~ v1_xboole_0(sK217) ) ),
    introduced(choice_axiom,[])).

fof(f4548,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f4547])).

fof(f4547,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4521])).

fof(f4521,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
              & ~ v1_xboole_0(X1) )
           => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    inference(negated_conjecture,[],[f4520])).

fof(f4520,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow19)).

fof(f8541,plain,(
    spl470_7 ),
    inference(avatar_split_clause,[],[f6693,f8539])).

fof(f6693,plain,(
    l1_struct_0(sK216) ),
    inference(cnf_transformation,[],[f5763])).

fof(f8537,plain,(
    ~ spl470_6 ),
    inference(avatar_split_clause,[],[f6694,f8535])).

fof(f6694,plain,(
    ~ v1_xboole_0(sK217) ),
    inference(cnf_transformation,[],[f5763])).

fof(f8533,plain,(
    spl470_5 ),
    inference(avatar_split_clause,[],[f6695,f8531])).

fof(f6695,plain,(
    v1_subset_1(sK217,u1_struct_0(k3_yellow_1(k2_struct_0(sK216)))) ),
    inference(cnf_transformation,[],[f5763])).

fof(f8529,plain,(
    spl470_4 ),
    inference(avatar_split_clause,[],[f6696,f8527])).

fof(f8527,plain,
    ( spl470_4
  <=> v2_waybel_0(sK217,k3_yellow_1(k2_struct_0(sK216))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl470_4])])).

fof(f6696,plain,(
    v2_waybel_0(sK217,k3_yellow_1(k2_struct_0(sK216))) ),
    inference(cnf_transformation,[],[f5763])).

fof(f8525,plain,(
    spl470_3 ),
    inference(avatar_split_clause,[],[f6697,f8523])).

fof(f8523,plain,
    ( spl470_3
  <=> v13_waybel_0(sK217,k3_yellow_1(k2_struct_0(sK216))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl470_3])])).

fof(f6697,plain,(
    v13_waybel_0(sK217,k3_yellow_1(k2_struct_0(sK216))) ),
    inference(cnf_transformation,[],[f5763])).

fof(f8521,plain,(
    spl470_2 ),
    inference(avatar_split_clause,[],[f6698,f8519])).

fof(f6698,plain,(
    m1_subset_1(sK217,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK216))))) ),
    inference(cnf_transformation,[],[f5763])).

fof(f8517,plain,(
    ~ spl470_1 ),
    inference(avatar_split_clause,[],[f6699,f8515])).

fof(f8515,plain,
    ( spl470_1
  <=> sK217 = k2_yellow19(sK216,k3_yellow19(sK216,k2_struct_0(sK216),sK217)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl470_1])])).

fof(f6699,plain,(
    sK217 != k2_yellow19(sK216,k3_yellow19(sK216,k2_struct_0(sK216),sK217)) ),
    inference(cnf_transformation,[],[f5763])).
%------------------------------------------------------------------------------
