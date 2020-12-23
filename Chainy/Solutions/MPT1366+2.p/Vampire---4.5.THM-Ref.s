%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1366+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:19 EST 2020

% Result     : Theorem 1.54s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :  196 ( 587 expanded)
%              Number of leaves         :   30 ( 262 expanded)
%              Depth                    :   20
%              Number of atoms          : 1491 (4776 expanded)
%              Number of equality atoms :   73 ( 233 expanded)
%              Maximal formula depth    :   21 (   8 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3196,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2594,f2598,f2602,f2606,f2610,f2614,f2645,f2670,f2845,f2886,f2904,f2914,f2952,f3123,f3131,f3141,f3157,f3174,f3186,f3195])).

fof(f3195,plain,
    ( ~ spl16_43
    | ~ spl16_40
    | spl16_22
    | ~ spl16_28
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_12
    | spl16_45 ),
    inference(avatar_split_clause,[],[f3194,f3155,f2668,f2608,f2604,f2600,f2899,f2840,f3118,f3149])).

fof(f3149,plain,
    ( spl16_43
  <=> r2_hidden(sK1(sK0),k3_subset_1(u1_struct_0(sK0),sK2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_43])])).

fof(f3118,plain,
    ( spl16_40
  <=> m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_40])])).

fof(f2840,plain,
    ( spl16_22
  <=> k1_xboole_0 = sK2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_22])])).

fof(f2899,plain,
    ( spl16_28
  <=> m1_subset_1(sK1(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_28])])).

fof(f2600,plain,
    ( spl16_3
  <=> v8_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_3])])).

fof(f2604,plain,
    ( spl16_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_4])])).

fof(f2608,plain,
    ( spl16_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_5])])).

fof(f2668,plain,
    ( spl16_12
  <=> v2_compts_1(sK2(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_12])])).

fof(f3155,plain,
    ( spl16_45
  <=> v3_pre_topc(sK9(sK0,sK2(sK0),sK1(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_45])])).

fof(f3194,plain,
    ( ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | k1_xboole_0 = sK2(sK0)
    | ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1(sK0),k3_subset_1(u1_struct_0(sK0),sK2(sK0)))
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_12
    | spl16_45 ),
    inference(subsumption_resolution,[],[f3193,f2669])).

fof(f2669,plain,
    ( v2_compts_1(sK2(sK0),sK0)
    | ~ spl16_12 ),
    inference(avatar_component_clause,[],[f2668])).

fof(f3193,plain,
    ( ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | k1_xboole_0 = sK2(sK0)
    | ~ v2_compts_1(sK2(sK0),sK0)
    | ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1(sK0),k3_subset_1(u1_struct_0(sK0),sK2(sK0)))
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_5
    | spl16_45 ),
    inference(resolution,[],[f3156,f2813])).

fof(f2813,plain,
    ( ! [X0,X1] :
        ( v3_pre_topc(sK9(sK0,X1,X0),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_xboole_0 = X1
        | ~ v2_compts_1(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,k3_subset_1(u1_struct_0(sK0),X1)) )
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_5 ),
    inference(subsumption_resolution,[],[f2812,f2609])).

fof(f2609,plain,
    ( v2_pre_topc(sK0)
    | ~ spl16_5 ),
    inference(avatar_component_clause,[],[f2608])).

fof(f2812,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k3_subset_1(u1_struct_0(sK0),X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_xboole_0 = X1
        | ~ v2_compts_1(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(sK9(sK0,X1,X0),sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl16_3
    | ~ spl16_4 ),
    inference(subsumption_resolution,[],[f2809,f2605])).

fof(f2605,plain,
    ( l1_pre_topc(sK0)
    | ~ spl16_4 ),
    inference(avatar_component_clause,[],[f2604])).

fof(f2809,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k3_subset_1(u1_struct_0(sK0),X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_xboole_0 = X1
        | ~ v2_compts_1(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(sK9(sK0,X1,X0),sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl16_3 ),
    inference(resolution,[],[f2572,f2601])).

fof(f2601,plain,
    ( v8_pre_topc(sK0)
    | ~ spl16_3 ),
    inference(avatar_component_clause,[],[f2600])).

fof(f2572,plain,(
    ! [X2,X0,X1] :
      ( ~ v8_pre_topc(X0)
      | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_xboole_0 = X1
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(sK9(X0,X1,X2),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2514])).

fof(f2514,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_xboole_0(sK9(X0,X1,X2),sK10(X0,X1,X2))
                & r1_tarski(X1,sK10(X0,X1,X2))
                & r2_hidden(X2,sK9(X0,X1,X2))
                & v3_pre_topc(sK10(X0,X1,X2),X0)
                & v3_pre_topc(sK9(X0,X1,X2),X0)
                & m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                & m1_subset_1(sK9(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | k1_xboole_0 = X1
          | ~ v2_compts_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f2488,f2513,f2512])).

fof(f2512,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ? [X4] :
              ( r1_xboole_0(X3,X4)
              & r1_tarski(X1,X4)
              & r2_hidden(X2,X3)
              & v3_pre_topc(X4,X0)
              & v3_pre_topc(X3,X0)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X4] :
            ( r1_xboole_0(sK9(X0,X1,X2),X4)
            & r1_tarski(X1,X4)
            & r2_hidden(X2,sK9(X0,X1,X2))
            & v3_pre_topc(X4,X0)
            & v3_pre_topc(sK9(X0,X1,X2),X0)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK9(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f2513,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r1_xboole_0(sK9(X0,X1,X2),X4)
          & r1_tarski(X1,X4)
          & r2_hidden(X2,sK9(X0,X1,X2))
          & v3_pre_topc(X4,X0)
          & v3_pre_topc(sK9(X0,X1,X2),X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_xboole_0(sK9(X0,X1,X2),sK10(X0,X1,X2))
        & r1_tarski(X1,sK10(X0,X1,X2))
        & r2_hidden(X2,sK9(X0,X1,X2))
        & v3_pre_topc(sK10(X0,X1,X2),X0)
        & v3_pre_topc(sK9(X0,X1,X2),X0)
        & m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f2488,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( r1_xboole_0(X3,X4)
                      & r1_tarski(X1,X4)
                      & r2_hidden(X2,X3)
                      & v3_pre_topc(X4,X0)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | k1_xboole_0 = X1
          | ~ v2_compts_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f2487])).

fof(f2487,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( r1_xboole_0(X3,X4)
                      & r1_tarski(X1,X4)
                      & r2_hidden(X2,X3)
                      & v3_pre_topc(X4,X0)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | k1_xboole_0 = X1
          | ~ v2_compts_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2461])).

fof(f2461,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v8_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_compts_1(X1,X0)
             => ( ! [X2] :
                    ( m1_subset_1(X2,u1_struct_0(X0))
                   => ~ ( ! [X3] :
                            ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                           => ! [X4] :
                                ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                               => ~ ( r1_xboole_0(X3,X4)
                                    & r1_tarski(X1,X4)
                                    & r2_hidden(X2,X3)
                                    & v3_pre_topc(X4,X0)
                                    & v3_pre_topc(X3,X0) ) ) )
                        & r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1)) ) )
                | k1_xboole_0 = X1 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_compts_1)).

fof(f3156,plain,
    ( ~ v3_pre_topc(sK9(sK0,sK2(sK0),sK1(sK0)),sK0)
    | spl16_45 ),
    inference(avatar_component_clause,[],[f3155])).

fof(f3186,plain,
    ( ~ spl16_40
    | spl16_22
    | ~ spl16_28
    | ~ spl16_43
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_12
    | spl16_44 ),
    inference(avatar_split_clause,[],[f3185,f3152,f2668,f2608,f2604,f2600,f3149,f2899,f2840,f3118])).

fof(f3152,plain,
    ( spl16_44
  <=> m1_subset_1(sK9(sK0,sK2(sK0),sK1(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_44])])).

fof(f3185,plain,
    ( ~ r2_hidden(sK1(sK0),k3_subset_1(u1_struct_0(sK0),sK2(sK0)))
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | k1_xboole_0 = sK2(sK0)
    | ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_12
    | spl16_44 ),
    inference(subsumption_resolution,[],[f3184,f2609])).

fof(f3184,plain,
    ( ~ r2_hidden(sK1(sK0),k3_subset_1(u1_struct_0(sK0),sK2(sK0)))
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | k1_xboole_0 = sK2(sK0)
    | ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_12
    | spl16_44 ),
    inference(subsumption_resolution,[],[f3183,f2605])).

fof(f3183,plain,
    ( ~ r2_hidden(sK1(sK0),k3_subset_1(u1_struct_0(sK0),sK2(sK0)))
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | k1_xboole_0 = sK2(sK0)
    | ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl16_3
    | ~ spl16_12
    | spl16_44 ),
    inference(subsumption_resolution,[],[f3182,f2601])).

fof(f3182,plain,
    ( ~ r2_hidden(sK1(sK0),k3_subset_1(u1_struct_0(sK0),sK2(sK0)))
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | k1_xboole_0 = sK2(sK0)
    | ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v8_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl16_12
    | spl16_44 ),
    inference(subsumption_resolution,[],[f3181,f2669])).

fof(f3181,plain,
    ( ~ r2_hidden(sK1(sK0),k3_subset_1(u1_struct_0(sK0),sK2(sK0)))
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | k1_xboole_0 = sK2(sK0)
    | ~ v2_compts_1(sK2(sK0),sK0)
    | ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v8_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl16_44 ),
    inference(resolution,[],[f3153,f2570])).

fof(f2570,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK9(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_xboole_0 = X1
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2514])).

fof(f3153,plain,
    ( ~ m1_subset_1(sK9(sK0,sK2(sK0),sK1(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl16_44 ),
    inference(avatar_component_clause,[],[f3152])).

fof(f3174,plain,
    ( spl16_1
    | ~ spl16_4
    | ~ spl16_5
    | spl16_6
    | spl16_43 ),
    inference(avatar_contradiction_clause,[],[f3173])).

fof(f3173,plain,
    ( $false
    | spl16_1
    | ~ spl16_4
    | ~ spl16_5
    | spl16_6
    | spl16_43 ),
    inference(subsumption_resolution,[],[f3172,f2613])).

fof(f2613,plain,
    ( ~ v2_struct_0(sK0)
    | spl16_6 ),
    inference(avatar_component_clause,[],[f2612])).

fof(f2612,plain,
    ( spl16_6
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_6])])).

fof(f3172,plain,
    ( v2_struct_0(sK0)
    | spl16_1
    | ~ spl16_4
    | ~ spl16_5
    | spl16_43 ),
    inference(subsumption_resolution,[],[f3171,f2609])).

fof(f3171,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl16_1
    | ~ spl16_4
    | spl16_43 ),
    inference(subsumption_resolution,[],[f3170,f2605])).

fof(f3170,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl16_1
    | spl16_43 ),
    inference(subsumption_resolution,[],[f3168,f2593])).

fof(f2593,plain,
    ( ~ v9_pre_topc(sK0)
    | spl16_1 ),
    inference(avatar_component_clause,[],[f2592])).

fof(f2592,plain,
    ( spl16_1
  <=> v9_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_1])])).

fof(f3168,plain,
    ( v9_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl16_43 ),
    inference(resolution,[],[f3150,f2541])).

fof(f2541,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),k3_subset_1(u1_struct_0(X0),sK2(X0)))
      | v9_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2499])).

fof(f2499,plain,(
    ! [X0] :
      ( ( ( v9_pre_topc(X0)
          | ( ! [X3] :
                ( ! [X4] :
                    ( ~ r1_xboole_0(X3,X4)
                    | ~ r1_tarski(sK2(X0),X4)
                    | ~ r2_hidden(sK1(X0),X3)
                    | ~ v3_pre_topc(X4,X0)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & r2_hidden(sK1(X0),k3_subset_1(u1_struct_0(X0),sK2(X0)))
            & v4_pre_topc(sK2(X0),X0)
            & k1_xboole_0 != sK2(X0)
            & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
            & m1_subset_1(sK1(X0),u1_struct_0(X0)) ) )
        & ( ! [X5] :
              ( ! [X6] :
                  ( ( r1_xboole_0(sK3(X0,X5,X6),sK4(X0,X5,X6))
                    & r1_tarski(X6,sK4(X0,X5,X6))
                    & r2_hidden(X5,sK3(X0,X5,X6))
                    & v3_pre_topc(sK4(X0,X5,X6),X0)
                    & v3_pre_topc(sK3(X0,X5,X6),X0)
                    & m1_subset_1(sK4(X0,X5,X6),k1_zfmisc_1(u1_struct_0(X0)))
                    & m1_subset_1(sK3(X0,X5,X6),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X5,k3_subset_1(u1_struct_0(X0),X6))
                  | ~ v4_pre_topc(X6,X0)
                  | k1_xboole_0 = X6
                  | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          | ~ v9_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f2494,f2498,f2497,f2496,f2495])).

fof(f2495,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ~ r1_xboole_0(X3,X4)
                      | ~ r1_tarski(X2,X4)
                      | ~ r2_hidden(X1,X3)
                      | ~ v3_pre_topc(X4,X0)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X1,k3_subset_1(u1_struct_0(X0),X2))
              & v4_pre_topc(X2,X0)
              & k1_xboole_0 != X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ! [X3] :
                ( ! [X4] :
                    ( ~ r1_xboole_0(X3,X4)
                    | ~ r1_tarski(X2,X4)
                    | ~ r2_hidden(sK1(X0),X3)
                    | ~ v3_pre_topc(X4,X0)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & r2_hidden(sK1(X0),k3_subset_1(u1_struct_0(X0),X2))
            & v4_pre_topc(X2,X0)
            & k1_xboole_0 != X2
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2496,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ! [X4] :
                  ( ~ r1_xboole_0(X3,X4)
                  | ~ r1_tarski(X2,X4)
                  | ~ r2_hidden(sK1(X0),X3)
                  | ~ v3_pre_topc(X4,X0)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r2_hidden(sK1(X0),k3_subset_1(u1_struct_0(X0),X2))
          & v4_pre_topc(X2,X0)
          & k1_xboole_0 != X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ! [X3] :
            ( ! [X4] :
                ( ~ r1_xboole_0(X3,X4)
                | ~ r1_tarski(sK2(X0),X4)
                | ~ r2_hidden(sK1(X0),X3)
                | ~ v3_pre_topc(X4,X0)
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r2_hidden(sK1(X0),k3_subset_1(u1_struct_0(X0),sK2(X0)))
        & v4_pre_topc(sK2(X0),X0)
        & k1_xboole_0 != sK2(X0)
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f2497,plain,(
    ! [X6,X5,X0] :
      ( ? [X7] :
          ( ? [X8] :
              ( r1_xboole_0(X7,X8)
              & r1_tarski(X6,X8)
              & r2_hidden(X5,X7)
              & v3_pre_topc(X8,X0)
              & v3_pre_topc(X7,X0)
              & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X8] :
            ( r1_xboole_0(sK3(X0,X5,X6),X8)
            & r1_tarski(X6,X8)
            & r2_hidden(X5,sK3(X0,X5,X6))
            & v3_pre_topc(X8,X0)
            & v3_pre_topc(sK3(X0,X5,X6),X0)
            & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK3(X0,X5,X6),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f2498,plain,(
    ! [X6,X5,X0] :
      ( ? [X8] :
          ( r1_xboole_0(sK3(X0,X5,X6),X8)
          & r1_tarski(X6,X8)
          & r2_hidden(X5,sK3(X0,X5,X6))
          & v3_pre_topc(X8,X0)
          & v3_pre_topc(sK3(X0,X5,X6),X0)
          & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_xboole_0(sK3(X0,X5,X6),sK4(X0,X5,X6))
        & r1_tarski(X6,sK4(X0,X5,X6))
        & r2_hidden(X5,sK3(X0,X5,X6))
        & v3_pre_topc(sK4(X0,X5,X6),X0)
        & v3_pre_topc(sK3(X0,X5,X6),X0)
        & m1_subset_1(sK4(X0,X5,X6),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f2494,plain,(
    ! [X0] :
      ( ( ( v9_pre_topc(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ! [X3] :
                      ( ! [X4] :
                          ( ~ r1_xboole_0(X3,X4)
                          | ~ r1_tarski(X2,X4)
                          | ~ r2_hidden(X1,X3)
                          | ~ v3_pre_topc(X4,X0)
                          | ~ v3_pre_topc(X3,X0)
                          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r2_hidden(X1,k3_subset_1(u1_struct_0(X0),X2))
                  & v4_pre_topc(X2,X0)
                  & k1_xboole_0 != X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X5] :
              ( ! [X6] :
                  ( ? [X7] :
                      ( ? [X8] :
                          ( r1_xboole_0(X7,X8)
                          & r1_tarski(X6,X8)
                          & r2_hidden(X5,X7)
                          & v3_pre_topc(X8,X0)
                          & v3_pre_topc(X7,X0)
                          & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0))) )
                      & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X5,k3_subset_1(u1_struct_0(X0),X6))
                  | ~ v4_pre_topc(X6,X0)
                  | k1_xboole_0 = X6
                  | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          | ~ v9_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f2493])).

fof(f2493,plain,(
    ! [X0] :
      ( ( ( v9_pre_topc(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ! [X3] :
                      ( ! [X4] :
                          ( ~ r1_xboole_0(X3,X4)
                          | ~ r1_tarski(X2,X4)
                          | ~ r2_hidden(X1,X3)
                          | ~ v3_pre_topc(X4,X0)
                          | ~ v3_pre_topc(X3,X0)
                          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r2_hidden(X1,k3_subset_1(u1_struct_0(X0),X2))
                  & v4_pre_topc(X2,X0)
                  & k1_xboole_0 != X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( ? [X3] :
                      ( ? [X4] :
                          ( r1_xboole_0(X3,X4)
                          & r1_tarski(X2,X4)
                          & r2_hidden(X1,X3)
                          & v3_pre_topc(X4,X0)
                          & v3_pre_topc(X3,X0)
                          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(X0),X2))
                  | ~ v4_pre_topc(X2,X0)
                  | k1_xboole_0 = X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v9_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f2473])).

fof(f2473,plain,(
    ! [X0] :
      ( ( v9_pre_topc(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( r1_xboole_0(X3,X4)
                        & r1_tarski(X2,X4)
                        & r2_hidden(X1,X3)
                        & v3_pre_topc(X4,X0)
                        & v3_pre_topc(X3,X0)
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(X0),X2))
                | ~ v4_pre_topc(X2,X0)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2472])).

fof(f2472,plain,(
    ! [X0] :
      ( ( v9_pre_topc(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( r1_xboole_0(X3,X4)
                        & r1_tarski(X2,X4)
                        & r2_hidden(X1,X3)
                        & v3_pre_topc(X4,X0)
                        & v3_pre_topc(X3,X0)
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(X0),X2))
                | ~ v4_pre_topc(X2,X0)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2446])).

fof(f2446,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v9_pre_topc(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ! [X4] :
                            ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                           => ~ ( r1_xboole_0(X3,X4)
                                & r1_tarski(X2,X4)
                                & r2_hidden(X1,X3)
                                & v3_pre_topc(X4,X0)
                                & v3_pre_topc(X3,X0) ) ) )
                    & r2_hidden(X1,k3_subset_1(u1_struct_0(X0),X2))
                    & v4_pre_topc(X2,X0)
                    & k1_xboole_0 != X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_compts_1)).

fof(f3150,plain,
    ( ~ r2_hidden(sK1(sK0),k3_subset_1(u1_struct_0(sK0),sK2(sK0)))
    | spl16_43 ),
    inference(avatar_component_clause,[],[f3149])).

fof(f3157,plain,
    ( ~ spl16_40
    | spl16_22
    | ~ spl16_28
    | ~ spl16_43
    | ~ spl16_44
    | ~ spl16_45
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_12
    | ~ spl16_29
    | ~ spl16_42 ),
    inference(avatar_split_clause,[],[f3147,f3139,f2902,f2668,f2608,f2604,f2600,f3155,f3152,f3149,f2899,f2840,f3118])).

fof(f2902,plain,
    ( spl16_29
  <=> r2_hidden(sK1(sK0),sK9(sK0,sK2(sK0),sK1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_29])])).

fof(f3139,plain,
    ( spl16_42
  <=> ! [X0] :
        ( ~ r2_hidden(sK1(sK0),X0)
        | ~ v3_pre_topc(X0,sK0)
        | ~ r1_xboole_0(X0,sK10(sK0,sK2(sK0),sK1(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_42])])).

fof(f3147,plain,
    ( ~ v3_pre_topc(sK9(sK0,sK2(sK0),sK1(sK0)),sK0)
    | ~ m1_subset_1(sK9(sK0,sK2(sK0),sK1(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1(sK0),k3_subset_1(u1_struct_0(sK0),sK2(sK0)))
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | k1_xboole_0 = sK2(sK0)
    | ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_12
    | ~ spl16_29
    | ~ spl16_42 ),
    inference(subsumption_resolution,[],[f3146,f2609])).

fof(f3146,plain,
    ( ~ v3_pre_topc(sK9(sK0,sK2(sK0),sK1(sK0)),sK0)
    | ~ m1_subset_1(sK9(sK0,sK2(sK0),sK1(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1(sK0),k3_subset_1(u1_struct_0(sK0),sK2(sK0)))
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | k1_xboole_0 = sK2(sK0)
    | ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_12
    | ~ spl16_29
    | ~ spl16_42 ),
    inference(subsumption_resolution,[],[f3145,f2605])).

fof(f3145,plain,
    ( ~ v3_pre_topc(sK9(sK0,sK2(sK0),sK1(sK0)),sK0)
    | ~ m1_subset_1(sK9(sK0,sK2(sK0),sK1(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1(sK0),k3_subset_1(u1_struct_0(sK0),sK2(sK0)))
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | k1_xboole_0 = sK2(sK0)
    | ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl16_3
    | ~ spl16_12
    | ~ spl16_29
    | ~ spl16_42 ),
    inference(subsumption_resolution,[],[f3144,f2601])).

fof(f3144,plain,
    ( ~ v3_pre_topc(sK9(sK0,sK2(sK0),sK1(sK0)),sK0)
    | ~ m1_subset_1(sK9(sK0,sK2(sK0),sK1(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1(sK0),k3_subset_1(u1_struct_0(sK0),sK2(sK0)))
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | k1_xboole_0 = sK2(sK0)
    | ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v8_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl16_12
    | ~ spl16_29
    | ~ spl16_42 ),
    inference(subsumption_resolution,[],[f3143,f2669])).

fof(f3143,plain,
    ( ~ v3_pre_topc(sK9(sK0,sK2(sK0),sK1(sK0)),sK0)
    | ~ m1_subset_1(sK9(sK0,sK2(sK0),sK1(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1(sK0),k3_subset_1(u1_struct_0(sK0),sK2(sK0)))
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | k1_xboole_0 = sK2(sK0)
    | ~ v2_compts_1(sK2(sK0),sK0)
    | ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v8_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl16_29
    | ~ spl16_42 ),
    inference(subsumption_resolution,[],[f3142,f2903])).

fof(f2903,plain,
    ( r2_hidden(sK1(sK0),sK9(sK0,sK2(sK0),sK1(sK0)))
    | ~ spl16_29 ),
    inference(avatar_component_clause,[],[f2902])).

fof(f3142,plain,
    ( ~ v3_pre_topc(sK9(sK0,sK2(sK0),sK1(sK0)),sK0)
    | ~ r2_hidden(sK1(sK0),sK9(sK0,sK2(sK0),sK1(sK0)))
    | ~ m1_subset_1(sK9(sK0,sK2(sK0),sK1(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1(sK0),k3_subset_1(u1_struct_0(sK0),sK2(sK0)))
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | k1_xboole_0 = sK2(sK0)
    | ~ v2_compts_1(sK2(sK0),sK0)
    | ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v8_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl16_42 ),
    inference(resolution,[],[f3140,f2576])).

fof(f2576,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(sK9(X0,X1,X2),sK10(X0,X1,X2))
      | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_xboole_0 = X1
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2514])).

fof(f3140,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,sK10(sK0,sK2(sK0),sK1(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ r2_hidden(sK1(sK0),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl16_42 ),
    inference(avatar_component_clause,[],[f3139])).

fof(f3141,plain,
    ( spl16_42
    | ~ spl16_28
    | spl16_1
    | ~ spl16_4
    | ~ spl16_5
    | spl16_6
    | ~ spl16_41 ),
    inference(avatar_split_clause,[],[f3137,f3121,f2612,f2608,f2604,f2592,f2899,f3139])).

fof(f3121,plain,
    ( spl16_41
  <=> ! [X1,X0] :
        ( ~ r2_hidden(sK1(sK0),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK0),sK2(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_xboole_0(X0,sK10(sK0,sK2(sK0),X1))
        | ~ v3_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_41])])).

fof(f3137,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
        | ~ r2_hidden(sK1(sK0),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_xboole_0(X0,sK10(sK0,sK2(sK0),sK1(sK0)))
        | ~ v3_pre_topc(X0,sK0) )
    | spl16_1
    | ~ spl16_4
    | ~ spl16_5
    | spl16_6
    | ~ spl16_41 ),
    inference(subsumption_resolution,[],[f3136,f2613])).

fof(f3136,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
        | ~ r2_hidden(sK1(sK0),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_xboole_0(X0,sK10(sK0,sK2(sK0),sK1(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | v2_struct_0(sK0) )
    | spl16_1
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_41 ),
    inference(subsumption_resolution,[],[f3135,f2609])).

fof(f3135,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
        | ~ r2_hidden(sK1(sK0),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_xboole_0(X0,sK10(sK0,sK2(sK0),sK1(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl16_1
    | ~ spl16_4
    | ~ spl16_41 ),
    inference(subsumption_resolution,[],[f3134,f2605])).

fof(f3134,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
        | ~ r2_hidden(sK1(sK0),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_xboole_0(X0,sK10(sK0,sK2(sK0),sK1(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl16_1
    | ~ spl16_41 ),
    inference(subsumption_resolution,[],[f3133,f2593])).

fof(f3133,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
        | ~ r2_hidden(sK1(sK0),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_xboole_0(X0,sK10(sK0,sK2(sK0),sK1(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | v9_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl16_41 ),
    inference(resolution,[],[f3122,f2541])).

fof(f3122,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK0),sK2(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(sK1(sK0),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_xboole_0(X0,sK10(sK0,sK2(sK0),X1))
        | ~ v3_pre_topc(X0,sK0) )
    | ~ spl16_41 ),
    inference(avatar_component_clause,[],[f3121])).

fof(f3131,plain,
    ( spl16_1
    | ~ spl16_4
    | ~ spl16_5
    | spl16_6
    | spl16_40 ),
    inference(avatar_contradiction_clause,[],[f3130])).

fof(f3130,plain,
    ( $false
    | spl16_1
    | ~ spl16_4
    | ~ spl16_5
    | spl16_6
    | spl16_40 ),
    inference(subsumption_resolution,[],[f3129,f2613])).

fof(f3129,plain,
    ( v2_struct_0(sK0)
    | spl16_1
    | ~ spl16_4
    | ~ spl16_5
    | spl16_40 ),
    inference(subsumption_resolution,[],[f3128,f2609])).

fof(f3128,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl16_1
    | ~ spl16_4
    | spl16_40 ),
    inference(subsumption_resolution,[],[f3127,f2605])).

fof(f3127,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl16_1
    | spl16_40 ),
    inference(subsumption_resolution,[],[f3125,f2593])).

fof(f3125,plain,
    ( v9_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl16_40 ),
    inference(resolution,[],[f3119,f2538])).

fof(f2538,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | v9_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2499])).

fof(f3119,plain,
    ( ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl16_40 ),
    inference(avatar_component_clause,[],[f3118])).

fof(f3123,plain,
    ( ~ spl16_40
    | spl16_22
    | spl16_41
    | spl16_1
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_5
    | spl16_6
    | ~ spl16_12
    | ~ spl16_30 ),
    inference(avatar_split_clause,[],[f3116,f2950,f2668,f2612,f2608,f2604,f2600,f2592,f3121,f2840,f3118])).

fof(f2950,plain,
    ( spl16_30
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_tarski(sK2(sK0),sK10(sK0,sK2(sK0),X0))
        | ~ r2_hidden(X0,k3_subset_1(u1_struct_0(sK0),sK2(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_30])])).

fof(f3116,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK1(sK0),X0)
        | ~ v3_pre_topc(X0,sK0)
        | ~ r1_xboole_0(X0,sK10(sK0,sK2(sK0),X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK0),sK2(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k1_xboole_0 = sK2(sK0)
        | ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl16_1
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_5
    | spl16_6
    | ~ spl16_12
    | ~ spl16_30 ),
    inference(subsumption_resolution,[],[f3115,f2669])).

fof(f3115,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK1(sK0),X0)
        | ~ v3_pre_topc(X0,sK0)
        | ~ r1_xboole_0(X0,sK10(sK0,sK2(sK0),X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK0),sK2(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k1_xboole_0 = sK2(sK0)
        | ~ v2_compts_1(sK2(sK0),sK0)
        | ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl16_1
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_5
    | spl16_6
    | ~ spl16_30 ),
    inference(duplicate_literal_removal,[],[f3114])).

fof(f3114,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK1(sK0),X0)
        | ~ v3_pre_topc(X0,sK0)
        | ~ r1_xboole_0(X0,sK10(sK0,sK2(sK0),X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK0),sK2(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k1_xboole_0 = sK2(sK0)
        | ~ v2_compts_1(sK2(sK0),sK0)
        | ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK0),sK2(sK0))) )
    | spl16_1
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_5
    | spl16_6
    | ~ spl16_30 ),
    inference(resolution,[],[f3003,f2951])).

fof(f2951,plain,
    ( ! [X0] :
        ( r1_tarski(sK2(sK0),sK10(sK0,sK2(sK0),X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k3_subset_1(u1_struct_0(sK0),sK2(sK0))) )
    | ~ spl16_30 ),
    inference(avatar_component_clause,[],[f2950])).

fof(f3003,plain,
    ( ! [X6,X4,X5] :
        ( ~ r1_tarski(sK2(sK0),sK10(sK0,X4,X5))
        | ~ r2_hidden(sK1(sK0),X6)
        | ~ v3_pre_topc(X6,sK0)
        | ~ r1_xboole_0(X6,sK10(sK0,X4,X5))
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X5,k3_subset_1(u1_struct_0(sK0),X4))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | k1_xboole_0 = X4
        | ~ v2_compts_1(X4,sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl16_1
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_5
    | spl16_6 ),
    inference(subsumption_resolution,[],[f3002,f2818])).

fof(f2818,plain,
    ( ! [X0,X1] :
        ( v3_pre_topc(sK10(sK0,X1,X0),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_xboole_0 = X1
        | ~ v2_compts_1(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,k3_subset_1(u1_struct_0(sK0),X1)) )
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_5 ),
    inference(subsumption_resolution,[],[f2817,f2609])).

fof(f2817,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k3_subset_1(u1_struct_0(sK0),X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_xboole_0 = X1
        | ~ v2_compts_1(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(sK10(sK0,X1,X0),sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl16_3
    | ~ spl16_4 ),
    inference(subsumption_resolution,[],[f2814,f2605])).

fof(f2814,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k3_subset_1(u1_struct_0(sK0),X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_xboole_0 = X1
        | ~ v2_compts_1(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(sK10(sK0,X1,X0),sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl16_3 ),
    inference(resolution,[],[f2573,f2601])).

fof(f2573,plain,(
    ! [X2,X0,X1] :
      ( ~ v8_pre_topc(X0)
      | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_xboole_0 = X1
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(sK10(X0,X1,X2),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2514])).

fof(f3002,plain,
    ( ! [X6,X4,X5] :
        ( ~ r1_tarski(sK2(sK0),sK10(sK0,X4,X5))
        | ~ r2_hidden(sK1(sK0),X6)
        | ~ v3_pre_topc(sK10(sK0,X4,X5),sK0)
        | ~ v3_pre_topc(X6,sK0)
        | ~ r1_xboole_0(X6,sK10(sK0,X4,X5))
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X5,k3_subset_1(u1_struct_0(sK0),X4))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | k1_xboole_0 = X4
        | ~ v2_compts_1(X4,sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl16_1
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_5
    | spl16_6 ),
    inference(subsumption_resolution,[],[f3001,f2609])).

fof(f3001,plain,
    ( ! [X6,X4,X5] :
        ( ~ r1_tarski(sK2(sK0),sK10(sK0,X4,X5))
        | ~ r2_hidden(sK1(sK0),X6)
        | ~ v3_pre_topc(sK10(sK0,X4,X5),sK0)
        | ~ v3_pre_topc(X6,sK0)
        | ~ r1_xboole_0(X6,sK10(sK0,X4,X5))
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X5,k3_subset_1(u1_struct_0(sK0),X4))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | k1_xboole_0 = X4
        | ~ v2_compts_1(X4,sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_pre_topc(sK0) )
    | spl16_1
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_5
    | spl16_6 ),
    inference(subsumption_resolution,[],[f3000,f2605])).

fof(f3000,plain,
    ( ! [X6,X4,X5] :
        ( ~ r1_tarski(sK2(sK0),sK10(sK0,X4,X5))
        | ~ r2_hidden(sK1(sK0),X6)
        | ~ v3_pre_topc(sK10(sK0,X4,X5),sK0)
        | ~ v3_pre_topc(X6,sK0)
        | ~ r1_xboole_0(X6,sK10(sK0,X4,X5))
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X5,k3_subset_1(u1_struct_0(sK0),X4))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | k1_xboole_0 = X4
        | ~ v2_compts_1(X4,sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | spl16_1
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_5
    | spl16_6 ),
    inference(subsumption_resolution,[],[f2979,f2601])).

fof(f2979,plain,
    ( ! [X6,X4,X5] :
        ( ~ r1_tarski(sK2(sK0),sK10(sK0,X4,X5))
        | ~ r2_hidden(sK1(sK0),X6)
        | ~ v3_pre_topc(sK10(sK0,X4,X5),sK0)
        | ~ v3_pre_topc(X6,sK0)
        | ~ r1_xboole_0(X6,sK10(sK0,X4,X5))
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X5,k3_subset_1(u1_struct_0(sK0),X4))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | k1_xboole_0 = X4
        | ~ v2_compts_1(X4,sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v8_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | spl16_1
    | ~ spl16_4
    | ~ spl16_5
    | spl16_6 ),
    inference(resolution,[],[f2926,f2571])).

fof(f2571,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_xboole_0 = X1
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2514])).

fof(f2926,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(sK2(sK0),X1)
        | ~ r2_hidden(sK1(sK0),X0)
        | ~ v3_pre_topc(X1,sK0)
        | ~ v3_pre_topc(X0,sK0)
        | ~ r1_xboole_0(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl16_1
    | ~ spl16_4
    | ~ spl16_5
    | spl16_6 ),
    inference(subsumption_resolution,[],[f2925,f2613])).

fof(f2925,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r1_tarski(sK2(sK0),X1)
        | ~ r2_hidden(sK1(sK0),X0)
        | ~ v3_pre_topc(X1,sK0)
        | ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0) )
    | spl16_1
    | ~ spl16_4
    | ~ spl16_5 ),
    inference(subsumption_resolution,[],[f2924,f2609])).

fof(f2924,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r1_tarski(sK2(sK0),X1)
        | ~ r2_hidden(sK1(sK0),X0)
        | ~ v3_pre_topc(X1,sK0)
        | ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl16_1
    | ~ spl16_4 ),
    inference(subsumption_resolution,[],[f2915,f2605])).

fof(f2915,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r1_tarski(sK2(sK0),X1)
        | ~ r2_hidden(sK1(sK0),X0)
        | ~ v3_pre_topc(X1,sK0)
        | ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl16_1 ),
    inference(resolution,[],[f2542,f2593])).

fof(f2542,plain,(
    ! [X4,X0,X3] :
      ( v9_pre_topc(X0)
      | ~ r1_xboole_0(X3,X4)
      | ~ r1_tarski(sK2(X0),X4)
      | ~ r2_hidden(sK1(X0),X3)
      | ~ v3_pre_topc(X4,X0)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2499])).

fof(f2952,plain,
    ( spl16_22
    | spl16_30
    | spl16_1
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_5
    | spl16_6
    | ~ spl16_12 ),
    inference(avatar_split_clause,[],[f2948,f2668,f2612,f2608,f2604,f2600,f2592,f2950,f2840])).

fof(f2948,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_xboole_0 = sK2(sK0)
        | ~ r2_hidden(X0,k3_subset_1(u1_struct_0(sK0),sK2(sK0)))
        | r1_tarski(sK2(sK0),sK10(sK0,sK2(sK0),X0)) )
    | spl16_1
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_5
    | spl16_6
    | ~ spl16_12 ),
    inference(subsumption_resolution,[],[f2947,f2613])).

fof(f2947,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_xboole_0 = sK2(sK0)
        | ~ r2_hidden(X0,k3_subset_1(u1_struct_0(sK0),sK2(sK0)))
        | r1_tarski(sK2(sK0),sK10(sK0,sK2(sK0),X0))
        | v2_struct_0(sK0) )
    | spl16_1
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_12 ),
    inference(subsumption_resolution,[],[f2946,f2609])).

fof(f2946,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_xboole_0 = sK2(sK0)
        | ~ r2_hidden(X0,k3_subset_1(u1_struct_0(sK0),sK2(sK0)))
        | r1_tarski(sK2(sK0),sK10(sK0,sK2(sK0),X0))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl16_1
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_12 ),
    inference(subsumption_resolution,[],[f2945,f2605])).

fof(f2945,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_xboole_0 = sK2(sK0)
        | ~ r2_hidden(X0,k3_subset_1(u1_struct_0(sK0),sK2(sK0)))
        | r1_tarski(sK2(sK0),sK10(sK0,sK2(sK0),X0))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl16_1
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_12 ),
    inference(subsumption_resolution,[],[f2944,f2593])).

fof(f2944,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_xboole_0 = sK2(sK0)
        | ~ r2_hidden(X0,k3_subset_1(u1_struct_0(sK0),sK2(sK0)))
        | r1_tarski(sK2(sK0),sK10(sK0,sK2(sK0),X0))
        | v9_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_12 ),
    inference(subsumption_resolution,[],[f2940,f2669])).

fof(f2940,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_xboole_0 = sK2(sK0)
        | ~ v2_compts_1(sK2(sK0),sK0)
        | ~ r2_hidden(X0,k3_subset_1(u1_struct_0(sK0),sK2(sK0)))
        | r1_tarski(sK2(sK0),sK10(sK0,sK2(sK0),X0))
        | v9_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_5 ),
    inference(resolution,[],[f2830,f2538])).

fof(f2830,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_xboole_0 = X1
        | ~ v2_compts_1(X1,sK0)
        | ~ r2_hidden(X0,k3_subset_1(u1_struct_0(sK0),X1))
        | r1_tarski(X1,sK10(sK0,X1,X0)) )
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_5 ),
    inference(subsumption_resolution,[],[f2829,f2609])).

fof(f2829,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k3_subset_1(u1_struct_0(sK0),X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_xboole_0 = X1
        | ~ v2_compts_1(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X1,sK10(sK0,X1,X0))
        | ~ v2_pre_topc(sK0) )
    | ~ spl16_3
    | ~ spl16_4 ),
    inference(subsumption_resolution,[],[f2826,f2605])).

fof(f2826,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k3_subset_1(u1_struct_0(sK0),X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_xboole_0 = X1
        | ~ v2_compts_1(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X1,sK10(sK0,X1,X0))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl16_3 ),
    inference(resolution,[],[f2575,f2601])).

fof(f2575,plain,(
    ! [X2,X0,X1] :
      ( ~ v8_pre_topc(X0)
      | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_xboole_0 = X1
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,sK10(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2514])).

fof(f2914,plain,
    ( spl16_1
    | ~ spl16_4
    | ~ spl16_5
    | spl16_6
    | spl16_28 ),
    inference(avatar_contradiction_clause,[],[f2913])).

fof(f2913,plain,
    ( $false
    | spl16_1
    | ~ spl16_4
    | ~ spl16_5
    | spl16_6
    | spl16_28 ),
    inference(subsumption_resolution,[],[f2912,f2613])).

fof(f2912,plain,
    ( v2_struct_0(sK0)
    | spl16_1
    | ~ spl16_4
    | ~ spl16_5
    | spl16_28 ),
    inference(subsumption_resolution,[],[f2911,f2609])).

fof(f2911,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl16_1
    | ~ spl16_4
    | spl16_28 ),
    inference(subsumption_resolution,[],[f2910,f2605])).

fof(f2910,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl16_1
    | spl16_28 ),
    inference(subsumption_resolution,[],[f2908,f2593])).

fof(f2908,plain,
    ( v9_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl16_28 ),
    inference(resolution,[],[f2900,f2537])).

fof(f2537,plain,(
    ! [X0] :
      ( m1_subset_1(sK1(X0),u1_struct_0(X0))
      | v9_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2499])).

fof(f2900,plain,
    ( ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | spl16_28 ),
    inference(avatar_component_clause,[],[f2899])).

fof(f2904,plain,
    ( ~ spl16_28
    | spl16_29
    | spl16_1
    | ~ spl16_4
    | ~ spl16_5
    | spl16_6
    | ~ spl16_23 ),
    inference(avatar_split_clause,[],[f2897,f2843,f2612,f2608,f2604,f2592,f2902,f2899])).

fof(f2843,plain,
    ( spl16_23
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK9(sK0,sK2(sK0),X0))
        | ~ r2_hidden(X0,k3_subset_1(u1_struct_0(sK0),sK2(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_23])])).

fof(f2897,plain,
    ( r2_hidden(sK1(sK0),sK9(sK0,sK2(sK0),sK1(sK0)))
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | spl16_1
    | ~ spl16_4
    | ~ spl16_5
    | spl16_6
    | ~ spl16_23 ),
    inference(subsumption_resolution,[],[f2896,f2613])).

fof(f2896,plain,
    ( r2_hidden(sK1(sK0),sK9(sK0,sK2(sK0),sK1(sK0)))
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | spl16_1
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_23 ),
    inference(subsumption_resolution,[],[f2895,f2609])).

fof(f2895,plain,
    ( r2_hidden(sK1(sK0),sK9(sK0,sK2(sK0),sK1(sK0)))
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl16_1
    | ~ spl16_4
    | ~ spl16_23 ),
    inference(subsumption_resolution,[],[f2894,f2605])).

fof(f2894,plain,
    ( r2_hidden(sK1(sK0),sK9(sK0,sK2(sK0),sK1(sK0)))
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl16_1
    | ~ spl16_23 ),
    inference(subsumption_resolution,[],[f2893,f2593])).

fof(f2893,plain,
    ( r2_hidden(sK1(sK0),sK9(sK0,sK2(sK0),sK1(sK0)))
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | v9_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl16_23 ),
    inference(resolution,[],[f2844,f2541])).

fof(f2844,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k3_subset_1(u1_struct_0(sK0),sK2(sK0)))
        | r2_hidden(X0,sK9(sK0,sK2(sK0),X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl16_23 ),
    inference(avatar_component_clause,[],[f2843])).

fof(f2886,plain,
    ( spl16_1
    | ~ spl16_4
    | ~ spl16_5
    | spl16_6
    | ~ spl16_22 ),
    inference(avatar_contradiction_clause,[],[f2885])).

fof(f2885,plain,
    ( $false
    | spl16_1
    | ~ spl16_4
    | ~ spl16_5
    | spl16_6
    | ~ spl16_22 ),
    inference(subsumption_resolution,[],[f2884,f2613])).

fof(f2884,plain,
    ( v2_struct_0(sK0)
    | spl16_1
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_22 ),
    inference(subsumption_resolution,[],[f2883,f2609])).

fof(f2883,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl16_1
    | ~ spl16_4
    | ~ spl16_22 ),
    inference(subsumption_resolution,[],[f2882,f2605])).

fof(f2882,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl16_1
    | ~ spl16_22 ),
    inference(subsumption_resolution,[],[f2856,f2593])).

fof(f2856,plain,
    ( v9_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl16_22 ),
    inference(trivial_inequality_removal,[],[f2855])).

fof(f2855,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v9_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl16_22 ),
    inference(superposition,[],[f2539,f2841])).

fof(f2841,plain,
    ( k1_xboole_0 = sK2(sK0)
    | ~ spl16_22 ),
    inference(avatar_component_clause,[],[f2840])).

fof(f2539,plain,(
    ! [X0] :
      ( k1_xboole_0 != sK2(X0)
      | v9_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2499])).

fof(f2845,plain,
    ( spl16_22
    | spl16_23
    | spl16_1
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_5
    | spl16_6
    | ~ spl16_12 ),
    inference(avatar_split_clause,[],[f2838,f2668,f2612,f2608,f2604,f2600,f2592,f2843,f2840])).

fof(f2838,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_xboole_0 = sK2(sK0)
        | ~ r2_hidden(X0,k3_subset_1(u1_struct_0(sK0),sK2(sK0)))
        | r2_hidden(X0,sK9(sK0,sK2(sK0),X0)) )
    | spl16_1
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_5
    | spl16_6
    | ~ spl16_12 ),
    inference(subsumption_resolution,[],[f2837,f2613])).

fof(f2837,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_xboole_0 = sK2(sK0)
        | ~ r2_hidden(X0,k3_subset_1(u1_struct_0(sK0),sK2(sK0)))
        | r2_hidden(X0,sK9(sK0,sK2(sK0),X0))
        | v2_struct_0(sK0) )
    | spl16_1
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_12 ),
    inference(subsumption_resolution,[],[f2836,f2609])).

fof(f2836,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_xboole_0 = sK2(sK0)
        | ~ r2_hidden(X0,k3_subset_1(u1_struct_0(sK0),sK2(sK0)))
        | r2_hidden(X0,sK9(sK0,sK2(sK0),X0))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl16_1
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_12 ),
    inference(subsumption_resolution,[],[f2835,f2605])).

fof(f2835,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_xboole_0 = sK2(sK0)
        | ~ r2_hidden(X0,k3_subset_1(u1_struct_0(sK0),sK2(sK0)))
        | r2_hidden(X0,sK9(sK0,sK2(sK0),X0))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl16_1
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_12 ),
    inference(subsumption_resolution,[],[f2834,f2593])).

fof(f2834,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_xboole_0 = sK2(sK0)
        | ~ r2_hidden(X0,k3_subset_1(u1_struct_0(sK0),sK2(sK0)))
        | r2_hidden(X0,sK9(sK0,sK2(sK0),X0))
        | v9_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_12 ),
    inference(subsumption_resolution,[],[f2831,f2669])).

fof(f2831,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_xboole_0 = sK2(sK0)
        | ~ v2_compts_1(sK2(sK0),sK0)
        | ~ r2_hidden(X0,k3_subset_1(u1_struct_0(sK0),sK2(sK0)))
        | r2_hidden(X0,sK9(sK0,sK2(sK0),X0))
        | v9_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_5 ),
    inference(resolution,[],[f2825,f2538])).

fof(f2825,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_xboole_0 = X1
        | ~ v2_compts_1(X1,sK0)
        | ~ r2_hidden(X0,k3_subset_1(u1_struct_0(sK0),X1))
        | r2_hidden(X0,sK9(sK0,X1,X0)) )
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_5 ),
    inference(subsumption_resolution,[],[f2824,f2609])).

fof(f2824,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k3_subset_1(u1_struct_0(sK0),X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_xboole_0 = X1
        | ~ v2_compts_1(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X0,sK9(sK0,X1,X0))
        | ~ v2_pre_topc(sK0) )
    | ~ spl16_3
    | ~ spl16_4 ),
    inference(subsumption_resolution,[],[f2821,f2605])).

fof(f2821,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k3_subset_1(u1_struct_0(sK0),X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_xboole_0 = X1
        | ~ v2_compts_1(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X0,sK9(sK0,X1,X0))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl16_3 ),
    inference(resolution,[],[f2574,f2601])).

fof(f2574,plain,(
    ! [X2,X0,X1] :
      ( ~ v8_pre_topc(X0)
      | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_xboole_0 = X1
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X2,sK9(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2514])).

fof(f2670,plain,
    ( spl16_12
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_5
    | spl16_6
    | ~ spl16_11 ),
    inference(avatar_split_clause,[],[f2666,f2643,f2612,f2608,f2604,f2596,f2592,f2668])).

fof(f2596,plain,
    ( spl16_2
  <=> v1_compts_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_2])])).

fof(f2643,plain,
    ( spl16_11
  <=> v4_pre_topc(sK2(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_11])])).

fof(f2666,plain,
    ( v2_compts_1(sK2(sK0),sK0)
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_5
    | spl16_6
    | ~ spl16_11 ),
    inference(subsumption_resolution,[],[f2665,f2613])).

fof(f2665,plain,
    ( v2_compts_1(sK2(sK0),sK0)
    | v2_struct_0(sK0)
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_11 ),
    inference(subsumption_resolution,[],[f2664,f2609])).

fof(f2664,plain,
    ( v2_compts_1(sK2(sK0),sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_11 ),
    inference(subsumption_resolution,[],[f2663,f2605])).

fof(f2663,plain,
    ( v2_compts_1(sK2(sK0),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_11 ),
    inference(subsumption_resolution,[],[f2662,f2593])).

fof(f2662,plain,
    ( v2_compts_1(sK2(sK0),sK0)
    | v9_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_11 ),
    inference(subsumption_resolution,[],[f2661,f2644])).

fof(f2644,plain,
    ( v4_pre_topc(sK2(sK0),sK0)
    | ~ spl16_11 ),
    inference(avatar_component_clause,[],[f2643])).

fof(f2661,plain,
    ( v2_compts_1(sK2(sK0),sK0)
    | ~ v4_pre_topc(sK2(sK0),sK0)
    | v9_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl16_2
    | ~ spl16_4 ),
    inference(resolution,[],[f2660,f2538])).

fof(f2660,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_compts_1(X0,sK0)
        | ~ v4_pre_topc(X0,sK0) )
    | ~ spl16_2
    | ~ spl16_4 ),
    inference(subsumption_resolution,[],[f2651,f2605])).

fof(f2651,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | v2_compts_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl16_2 ),
    inference(resolution,[],[f2553,f2597])).

fof(f2597,plain,
    ( v1_compts_1(sK0)
    | ~ spl16_2 ),
    inference(avatar_component_clause,[],[f2596])).

fof(f2553,plain,(
    ! [X0,X1] :
      ( ~ v1_compts_1(X0)
      | ~ v4_pre_topc(X1,X0)
      | v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2477])).

fof(f2477,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_compts_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v1_compts_1(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2476])).

fof(f2476,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_compts_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v1_compts_1(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2463])).

fof(f2463,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v4_pre_topc(X1,X0)
              & v1_compts_1(X0) )
           => v2_compts_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_compts_1)).

fof(f2645,plain,
    ( spl16_11
    | spl16_1
    | ~ spl16_4
    | ~ spl16_5
    | spl16_6 ),
    inference(avatar_split_clause,[],[f2641,f2612,f2608,f2604,f2592,f2643])).

fof(f2641,plain,
    ( v4_pre_topc(sK2(sK0),sK0)
    | spl16_1
    | ~ spl16_4
    | ~ spl16_5
    | spl16_6 ),
    inference(subsumption_resolution,[],[f2640,f2613])).

fof(f2640,plain,
    ( v4_pre_topc(sK2(sK0),sK0)
    | v2_struct_0(sK0)
    | spl16_1
    | ~ spl16_4
    | ~ spl16_5 ),
    inference(subsumption_resolution,[],[f2639,f2609])).

fof(f2639,plain,
    ( v4_pre_topc(sK2(sK0),sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl16_1
    | ~ spl16_4 ),
    inference(subsumption_resolution,[],[f2638,f2605])).

fof(f2638,plain,
    ( v4_pre_topc(sK2(sK0),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl16_1 ),
    inference(resolution,[],[f2540,f2593])).

fof(f2540,plain,(
    ! [X0] :
      ( v9_pre_topc(X0)
      | v4_pre_topc(sK2(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2499])).

fof(f2614,plain,(
    ~ spl16_6 ),
    inference(avatar_split_clause,[],[f2524,f2612])).

fof(f2524,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f2492])).

fof(f2492,plain,
    ( ~ v9_pre_topc(sK0)
    & v1_compts_1(sK0)
    & v8_pre_topc(sK0)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f2471,f2491])).

fof(f2491,plain,
    ( ? [X0] :
        ( ~ v9_pre_topc(X0)
        & v1_compts_1(X0)
        & v8_pre_topc(X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ~ v9_pre_topc(sK0)
      & v1_compts_1(sK0)
      & v8_pre_topc(sK0)
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2471,plain,(
    ? [X0] :
      ( ~ v9_pre_topc(X0)
      & v1_compts_1(X0)
      & v8_pre_topc(X0)
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f2470])).

fof(f2470,plain,(
    ? [X0] :
      ( ~ v9_pre_topc(X0)
      & v1_compts_1(X0)
      & v8_pre_topc(X0)
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2469])).

fof(f2469,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( ( v1_compts_1(X0)
            & v8_pre_topc(X0) )
         => v9_pre_topc(X0) ) ) ),
    inference(negated_conjecture,[],[f2468])).

fof(f2468,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( ( v1_compts_1(X0)
          & v8_pre_topc(X0) )
       => v9_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_compts_1)).

fof(f2610,plain,(
    spl16_5 ),
    inference(avatar_split_clause,[],[f2525,f2608])).

fof(f2525,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f2492])).

fof(f2606,plain,(
    spl16_4 ),
    inference(avatar_split_clause,[],[f2526,f2604])).

fof(f2526,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f2492])).

fof(f2602,plain,(
    spl16_3 ),
    inference(avatar_split_clause,[],[f2527,f2600])).

fof(f2527,plain,(
    v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f2492])).

fof(f2598,plain,(
    spl16_2 ),
    inference(avatar_split_clause,[],[f2528,f2596])).

fof(f2528,plain,(
    v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f2492])).

fof(f2594,plain,(
    ~ spl16_1 ),
    inference(avatar_split_clause,[],[f2529,f2592])).

fof(f2529,plain,(
    ~ v9_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f2492])).
%------------------------------------------------------------------------------
