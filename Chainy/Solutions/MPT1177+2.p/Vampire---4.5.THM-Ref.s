%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1177+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:11 EST 2020

% Result     : Theorem 1.80s
% Output     : Refutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 474 expanded)
%              Number of leaves         :   40 ( 239 expanded)
%              Depth                    :   12
%              Number of atoms          :  854 (2591 expanded)
%              Number of equality atoms :   57 (  85 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3067,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2235,f2236,f2241,f2246,f2251,f2256,f2261,f2266,f2271,f2276,f2455,f2476,f2481,f2490,f2536,f2593,f2595,f2619,f2701,f2773,f2774,f2847,f2962,f2990,f2995,f3000,f3066])).

fof(f3066,plain,
    ( ~ spl19_107
    | ~ spl19_5
    | ~ spl19_6
    | ~ spl19_7
    | ~ spl19_8
    | ~ spl19_9
    | spl19_10
    | ~ spl19_105
    | ~ spl19_106 ),
    inference(avatar_split_clause,[],[f3065,f2992,f2987,f2273,f2268,f2263,f2258,f2253,f2248,f2997])).

fof(f2997,plain,
    ( spl19_107
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_107])])).

fof(f2248,plain,
    ( spl19_5
  <=> m1_orders_1(sK1,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k9_setfam_1(u1_struct_0(sK0)),k1_tarski(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_5])])).

fof(f2253,plain,
    ( spl19_6
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_6])])).

fof(f2258,plain,
    ( spl19_7
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_7])])).

fof(f2263,plain,
    ( spl19_8
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_8])])).

fof(f2268,plain,
    ( spl19_9
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_9])])).

fof(f2273,plain,
    ( spl19_10
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_10])])).

fof(f2987,plain,
    ( spl19_105
  <=> m2_orders_2(k1_xboole_0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_105])])).

fof(f2992,plain,
    ( spl19_106
  <=> v6_orders_2(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_106])])).

fof(f3065,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl19_5
    | ~ spl19_6
    | ~ spl19_7
    | ~ spl19_8
    | ~ spl19_9
    | spl19_10
    | ~ spl19_105
    | ~ spl19_106 ),
    inference(unit_resulting_resolution,[],[f2275,f2270,f2265,f2260,f2255,f2989,f2250,f2994,f2220])).

fof(f2220,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m2_orders_2(k1_xboole_0,X0,X1)
      | ~ v6_orders_2(k1_xboole_0,X0)
      | ~ m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_tarski(k1_xboole_0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f2206])).

fof(f2206,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X2
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v6_orders_2(X2,X0)
      | ~ m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_tarski(k1_xboole_0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f2155,f2175])).

fof(f2175,plain,(
    ! [X0] : k1_orders_1(X0) = k7_subset_1(k1_zfmisc_1(X0),k9_setfam_1(X0),k1_tarski(k1_xboole_0)) ),
    inference(cnf_transformation,[],[f1871])).

fof(f1871,axiom,(
    ! [X0] : k1_orders_1(X0) = k7_subset_1(k1_zfmisc_1(X0),k9_setfam_1(X0),k1_tarski(k1_xboole_0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_orders_1)).

fof(f2155,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X2
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v6_orders_2(X2,X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2084])).

fof(f2084,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_orders_2(X2,X0,X1)
                  | ( sK12(X0,X1,X2) != k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,sK12(X0,X1,X2))))
                    & r2_hidden(sK12(X0,X1,X2),X2)
                    & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X0)) )
                  | ~ r2_wellord1(u1_orders_2(X0),X2)
                  | k1_xboole_0 = X2 )
                & ( ( ! [X4] :
                        ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X4))) = X4
                        | ~ r2_hidden(X4,X2)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r2_wellord1(u1_orders_2(X0),X2)
                    & k1_xboole_0 != X2 )
                  | ~ m2_orders_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X2,X0) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f2082,f2083])).

fof(f2083,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( sK12(X0,X1,X2) != k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,sK12(X0,X1,X2))))
        & r2_hidden(sK12(X0,X1,X2),X2)
        & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2082,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_orders_2(X2,X0,X1)
                  | ? [X3] :
                      ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3
                      & r2_hidden(X3,X2)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ r2_wellord1(u1_orders_2(X0),X2)
                  | k1_xboole_0 = X2 )
                & ( ( ! [X4] :
                        ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X4))) = X4
                        | ~ r2_hidden(X4,X2)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r2_wellord1(u1_orders_2(X0),X2)
                    & k1_xboole_0 != X2 )
                  | ~ m2_orders_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X2,X0) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f2081])).

fof(f2081,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_orders_2(X2,X0,X1)
                  | ? [X3] :
                      ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3
                      & r2_hidden(X3,X2)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ r2_wellord1(u1_orders_2(X0),X2)
                  | k1_xboole_0 = X2 )
                & ( ( ! [X3] :
                        ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3
                        | ~ r2_hidden(X3,X2)
                        | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                    & r2_wellord1(u1_orders_2(X0),X2)
                    & k1_xboole_0 != X2 )
                  | ~ m2_orders_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X2,X0) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2080])).

fof(f2080,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_orders_2(X2,X0,X1)
                  | ? [X3] :
                      ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3
                      & r2_hidden(X3,X2)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ r2_wellord1(u1_orders_2(X0),X2)
                  | k1_xboole_0 = X2 )
                & ( ( ! [X3] :
                        ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3
                        | ~ r2_hidden(X3,X2)
                        | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                    & r2_wellord1(u1_orders_2(X0),X2)
                    & k1_xboole_0 != X2 )
                  | ~ m2_orders_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X2,X0) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f2011])).

fof(f2011,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_orders_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3
                      | ~ r2_hidden(X3,X2)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r2_wellord1(u1_orders_2(X0),X2)
                  & k1_xboole_0 != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X2,X0) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2010])).

fof(f2010,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_orders_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3
                      | ~ r2_hidden(X3,X2)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r2_wellord1(u1_orders_2(X0),X2)
                  & k1_xboole_0 != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X2,X0) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1869])).

fof(f1869,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v6_orders_2(X2,X0) )
             => ( m2_orders_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_hidden(X3,X2)
                       => k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 ) )
                  & r2_wellord1(u1_orders_2(X0),X2)
                  & k1_xboole_0 != X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_orders_2)).

fof(f2994,plain,
    ( v6_orders_2(k1_xboole_0,sK0)
    | ~ spl19_106 ),
    inference(avatar_component_clause,[],[f2992])).

fof(f2250,plain,
    ( m1_orders_1(sK1,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k9_setfam_1(u1_struct_0(sK0)),k1_tarski(k1_xboole_0)))
    | ~ spl19_5 ),
    inference(avatar_component_clause,[],[f2248])).

fof(f2989,plain,
    ( m2_orders_2(k1_xboole_0,sK0,sK1)
    | ~ spl19_105 ),
    inference(avatar_component_clause,[],[f2987])).

fof(f2255,plain,
    ( l1_orders_2(sK0)
    | ~ spl19_6 ),
    inference(avatar_component_clause,[],[f2253])).

fof(f2260,plain,
    ( v5_orders_2(sK0)
    | ~ spl19_7 ),
    inference(avatar_component_clause,[],[f2258])).

fof(f2265,plain,
    ( v4_orders_2(sK0)
    | ~ spl19_8 ),
    inference(avatar_component_clause,[],[f2263])).

fof(f2270,plain,
    ( v3_orders_2(sK0)
    | ~ spl19_9 ),
    inference(avatar_component_clause,[],[f2268])).

fof(f2275,plain,
    ( ~ v2_struct_0(sK0)
    | spl19_10 ),
    inference(avatar_component_clause,[],[f2273])).

fof(f3000,plain,
    ( spl19_107
    | ~ spl19_40
    | ~ spl19_101 ),
    inference(avatar_split_clause,[],[f2972,f2944,f2473,f2997])).

fof(f2473,plain,
    ( spl19_40
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_40])])).

fof(f2944,plain,
    ( spl19_101
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_101])])).

fof(f2972,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl19_40
    | ~ spl19_101 ),
    inference(backward_demodulation,[],[f2475,f2946])).

fof(f2946,plain,
    ( k1_xboole_0 = sK2
    | ~ spl19_101 ),
    inference(avatar_component_clause,[],[f2944])).

fof(f2475,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl19_40 ),
    inference(avatar_component_clause,[],[f2473])).

fof(f2995,plain,
    ( spl19_106
    | ~ spl19_37
    | ~ spl19_101 ),
    inference(avatar_split_clause,[],[f2971,f2944,f2452,f2992])).

fof(f2452,plain,
    ( spl19_37
  <=> v6_orders_2(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_37])])).

fof(f2971,plain,
    ( v6_orders_2(k1_xboole_0,sK0)
    | ~ spl19_37
    | ~ spl19_101 ),
    inference(backward_demodulation,[],[f2454,f2946])).

fof(f2454,plain,
    ( v6_orders_2(sK2,sK0)
    | ~ spl19_37 ),
    inference(avatar_component_clause,[],[f2452])).

fof(f2990,plain,
    ( spl19_105
    | ~ spl19_4
    | ~ spl19_101 ),
    inference(avatar_split_clause,[],[f2970,f2944,f2243,f2987])).

fof(f2243,plain,
    ( spl19_4
  <=> m2_orders_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_4])])).

fof(f2970,plain,
    ( m2_orders_2(k1_xboole_0,sK0,sK1)
    | ~ spl19_4
    | ~ spl19_101 ),
    inference(backward_demodulation,[],[f2245,f2946])).

fof(f2245,plain,
    ( m2_orders_2(sK2,sK0,sK1)
    | ~ spl19_4 ),
    inference(avatar_component_clause,[],[f2243])).

fof(f2962,plain,
    ( spl19_101
    | ~ spl19_40
    | ~ spl19_93
    | ~ spl19_43
    | ~ spl19_93 ),
    inference(avatar_split_clause,[],[f2940,f2836,f2488,f2836,f2473,f2944])).

fof(f2488,plain,
    ( spl19_43
  <=> ! [X1,X0] :
        ( ~ m1_orders_2(X0,sK0,X1)
        | ~ m1_orders_2(X1,sK0,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_43])])).

fof(f2836,plain,
    ( spl19_93
  <=> m1_orders_2(sK2,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_93])])).

fof(f2940,plain,
    ( ~ m1_orders_2(sK2,sK0,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK2
    | ~ spl19_43
    | ~ spl19_93 ),
    inference(duplicate_literal_removal,[],[f2936])).

fof(f2936,plain,
    ( ~ m1_orders_2(sK2,sK0,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK2
    | ~ spl19_43
    | ~ spl19_93 ),
    inference(resolution,[],[f2838,f2489])).

fof(f2489,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_2(X0,sK0,X1)
        | ~ m1_orders_2(X1,sK0,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0 )
    | ~ spl19_43 ),
    inference(avatar_component_clause,[],[f2488])).

fof(f2838,plain,
    ( m1_orders_2(sK2,sK0,sK2)
    | ~ spl19_93 ),
    inference(avatar_component_clause,[],[f2836])).

fof(f2847,plain,
    ( spl19_93
    | ~ spl19_2
    | ~ spl19_76 ),
    inference(avatar_split_clause,[],[f2846,f2698,f2232,f2836])).

fof(f2232,plain,
    ( spl19_2
  <=> m1_orders_2(sK2,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_2])])).

fof(f2698,plain,
    ( spl19_76
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_76])])).

fof(f2846,plain,
    ( m1_orders_2(sK2,sK0,sK2)
    | ~ spl19_2
    | ~ spl19_76 ),
    inference(forward_demodulation,[],[f2233,f2700])).

fof(f2700,plain,
    ( sK2 = sK3
    | ~ spl19_76 ),
    inference(avatar_component_clause,[],[f2698])).

fof(f2233,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | ~ spl19_2 ),
    inference(avatar_component_clause,[],[f2232])).

fof(f2774,plain,
    ( sK2 != sK3
    | r2_xboole_0(sK3,sK2)
    | ~ r2_xboole_0(sK2,sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2773,plain,
    ( spl19_76
    | spl19_2
    | ~ spl19_3
    | ~ spl19_4
    | ~ spl19_5
    | ~ spl19_6
    | ~ spl19_7
    | ~ spl19_8
    | ~ spl19_9
    | spl19_10
    | spl19_62 ),
    inference(avatar_split_clause,[],[f2770,f2616,f2273,f2268,f2263,f2258,f2253,f2248,f2243,f2238,f2232,f2698])).

fof(f2238,plain,
    ( spl19_3
  <=> m2_orders_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_3])])).

fof(f2616,plain,
    ( spl19_62
  <=> m1_orders_2(sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_62])])).

fof(f2770,plain,
    ( sK2 = sK3
    | spl19_2
    | ~ spl19_3
    | ~ spl19_4
    | ~ spl19_5
    | ~ spl19_6
    | ~ spl19_7
    | ~ spl19_8
    | ~ spl19_9
    | spl19_10
    | spl19_62 ),
    inference(unit_resulting_resolution,[],[f2275,f2270,f2265,f2260,f2255,f2234,f2240,f2245,f2250,f2618,f2196])).

fof(f2196,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | m1_orders_2(X3,X0,X2)
      | X2 = X3
      | ~ m2_orders_2(X3,X0,X1)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_tarski(k1_xboole_0)))
      | ~ l1_orders_2(X0)
      | m1_orders_2(X2,X0,X3)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f2132,f2175])).

fof(f2132,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_orders_2(X2,X0,X3)
      | m1_orders_2(X3,X0,X2)
      | X2 = X3
      | ~ m2_orders_2(X3,X0,X1)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2073])).

fof(f2073,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( m1_orders_2(X2,X0,X3)
                      | m1_orders_2(X3,X0,X2) )
                    & ( ~ m1_orders_2(X3,X0,X2)
                      | ~ m1_orders_2(X2,X0,X3) ) )
                  | X2 = X3
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f1987])).

fof(f1987,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( m1_orders_2(X2,X0,X3)
                  <=> ~ m1_orders_2(X3,X0,X2) )
                  | X2 = X3
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f1986])).

fof(f1986,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( m1_orders_2(X2,X0,X3)
                  <=> ~ m1_orders_2(X3,X0,X2) )
                  | X2 = X3
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1954])).

fof(f1954,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X1)
                 => ( X2 != X3
                   => ( m1_orders_2(X2,X0,X3)
                    <=> ~ m1_orders_2(X3,X0,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_orders_2)).

fof(f2618,plain,
    ( ~ m1_orders_2(sK3,sK0,sK2)
    | spl19_62 ),
    inference(avatar_component_clause,[],[f2616])).

fof(f2240,plain,
    ( m2_orders_2(sK3,sK0,sK1)
    | ~ spl19_3 ),
    inference(avatar_component_clause,[],[f2238])).

fof(f2234,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | spl19_2 ),
    inference(avatar_component_clause,[],[f2232])).

fof(f2701,plain,
    ( spl19_1
    | spl19_76
    | ~ spl19_51 ),
    inference(avatar_split_clause,[],[f2651,f2533,f2698,f2228])).

fof(f2228,plain,
    ( spl19_1
  <=> r2_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_1])])).

fof(f2533,plain,
    ( spl19_51
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_51])])).

fof(f2651,plain,
    ( sK2 = sK3
    | r2_xboole_0(sK2,sK3)
    | ~ spl19_51 ),
    inference(resolution,[],[f2535,f2146])).

fof(f2146,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2077])).

fof(f2077,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f2076])).

fof(f2076,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f2535,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl19_51 ),
    inference(avatar_component_clause,[],[f2533])).

fof(f2619,plain,
    ( ~ spl19_62
    | ~ spl19_6
    | ~ spl19_7
    | ~ spl19_8
    | ~ spl19_9
    | spl19_10
    | ~ spl19_40
    | spl19_57 ),
    inference(avatar_split_clause,[],[f2613,f2581,f2473,f2273,f2268,f2263,f2258,f2253,f2616])).

fof(f2581,plain,
    ( spl19_57
  <=> r1_tarski(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_57])])).

fof(f2613,plain,
    ( ~ m1_orders_2(sK3,sK0,sK2)
    | ~ spl19_6
    | ~ spl19_7
    | ~ spl19_8
    | ~ spl19_9
    | spl19_10
    | ~ spl19_40
    | spl19_57 ),
    inference(unit_resulting_resolution,[],[f2275,f2270,f2265,f2260,f2255,f2475,f2583,f2128])).

fof(f2128,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | r1_tarski(X2,X1)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f1983])).

fof(f1983,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X2,X1)
              | ~ m1_orders_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f1982])).

fof(f1982,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X2,X1)
              | ~ m1_orders_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1942])).

fof(f1942,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_orders_2(X2,X0,X1)
             => r1_tarski(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_orders_2)).

fof(f2583,plain,
    ( ~ r1_tarski(sK3,sK2)
    | spl19_57 ),
    inference(avatar_component_clause,[],[f2581])).

fof(f2595,plain,
    ( ~ spl19_53
    | ~ spl19_1 ),
    inference(avatar_split_clause,[],[f2557,f2228,f2560])).

fof(f2560,plain,
    ( spl19_53
  <=> r2_xboole_0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_53])])).

fof(f2557,plain,
    ( ~ r2_xboole_0(sK3,sK2)
    | ~ spl19_1 ),
    inference(resolution,[],[f2229,f2143])).

fof(f2143,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2003])).

fof(f2003,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f121])).

fof(f121,axiom,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_xboole_1)).

fof(f2229,plain,
    ( r2_xboole_0(sK2,sK3)
    | ~ spl19_1 ),
    inference(avatar_component_clause,[],[f2228])).

fof(f2593,plain,
    ( ~ spl19_57
    | ~ spl19_1 ),
    inference(avatar_split_clause,[],[f2542,f2228,f2581])).

fof(f2542,plain,
    ( ~ r1_tarski(sK3,sK2)
    | ~ spl19_1 ),
    inference(unit_resulting_resolution,[],[f2219,f2229,f2135])).

fof(f2135,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_xboole_0(X1,X2)
      | r2_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f1993])).

fof(f1993,plain,(
    ! [X0,X1,X2] :
      ( r2_xboole_0(X0,X2)
      | ~ r2_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f1992])).

fof(f1992,plain,(
    ! [X0,X1,X2] :
      ( r2_xboole_0(X0,X2)
      | ~ r2_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f123])).

fof(f123,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_xboole_1)).

fof(f2219,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f2145])).

fof(f2145,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2077])).

fof(f2536,plain,
    ( spl19_51
    | ~ spl19_2
    | ~ spl19_6
    | ~ spl19_7
    | ~ spl19_8
    | ~ spl19_9
    | spl19_10
    | ~ spl19_41 ),
    inference(avatar_split_clause,[],[f2531,f2478,f2273,f2268,f2263,f2258,f2253,f2232,f2533])).

fof(f2478,plain,
    ( spl19_41
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_41])])).

fof(f2531,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl19_2
    | ~ spl19_6
    | ~ spl19_7
    | ~ spl19_8
    | ~ spl19_9
    | spl19_10
    | ~ spl19_41 ),
    inference(unit_resulting_resolution,[],[f2275,f2270,f2265,f2260,f2255,f2233,f2480,f2128])).

fof(f2480,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl19_41 ),
    inference(avatar_component_clause,[],[f2478])).

fof(f2490,plain,
    ( spl19_10
    | ~ spl19_9
    | ~ spl19_8
    | ~ spl19_6
    | spl19_43
    | ~ spl19_7 ),
    inference(avatar_split_clause,[],[f2486,f2258,f2488,f2253,f2263,f2268,f2273])).

fof(f2486,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_2(X0,sK0,X1)
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | ~ m1_orders_2(X1,sK0,X0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl19_7 ),
    inference(resolution,[],[f2121,f2260])).

fof(f2121,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ m1_orders_2(X1,X0,X2)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ m1_orders_2(X2,X0,X1)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f1979])).

fof(f1979,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ m1_orders_2(X2,X0,X1)
              | ~ m1_orders_2(X1,X0,X2)
              | k1_xboole_0 = X1
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f1978])).

fof(f1978,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ m1_orders_2(X2,X0,X1)
              | ~ m1_orders_2(X1,X0,X2)
              | k1_xboole_0 = X1
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1944])).

fof(f1944,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( m1_orders_2(X2,X0,X1)
                  & m1_orders_2(X1,X0,X2)
                  & k1_xboole_0 != X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_orders_2)).

fof(f2481,plain,
    ( spl19_41
    | ~ spl19_3
    | ~ spl19_5
    | ~ spl19_6
    | ~ spl19_7
    | ~ spl19_8
    | ~ spl19_9
    | spl19_10 ),
    inference(avatar_split_clause,[],[f2469,f2273,f2268,f2263,f2258,f2253,f2248,f2238,f2478])).

fof(f2469,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl19_3
    | ~ spl19_5
    | ~ spl19_6
    | ~ spl19_7
    | ~ spl19_8
    | ~ spl19_9
    | spl19_10 ),
    inference(unit_resulting_resolution,[],[f2275,f2270,f2265,f2260,f2255,f2240,f2250,f2199])).

fof(f2199,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_tarski(k1_xboole_0)))
      | ~ l1_orders_2(X0)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f2154,f2175])).

fof(f2154,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2009])).

fof(f2009,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) )
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2008])).

fof(f2008,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) )
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1887])).

fof(f1887,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_orders_2(X2,X0,X1)
         => ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_orders_2)).

fof(f2476,plain,
    ( spl19_40
    | ~ spl19_4
    | ~ spl19_5
    | ~ spl19_6
    | ~ spl19_7
    | ~ spl19_8
    | ~ spl19_9
    | spl19_10 ),
    inference(avatar_split_clause,[],[f2470,f2273,f2268,f2263,f2258,f2253,f2248,f2243,f2473])).

fof(f2470,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl19_4
    | ~ spl19_5
    | ~ spl19_6
    | ~ spl19_7
    | ~ spl19_8
    | ~ spl19_9
    | spl19_10 ),
    inference(unit_resulting_resolution,[],[f2275,f2270,f2265,f2260,f2255,f2245,f2250,f2199])).

fof(f2455,plain,
    ( spl19_37
    | ~ spl19_4
    | ~ spl19_5
    | ~ spl19_6
    | ~ spl19_7
    | ~ spl19_8
    | ~ spl19_9
    | spl19_10 ),
    inference(avatar_split_clause,[],[f2450,f2273,f2268,f2263,f2258,f2253,f2248,f2243,f2452])).

fof(f2450,plain,
    ( v6_orders_2(sK2,sK0)
    | ~ spl19_4
    | ~ spl19_5
    | ~ spl19_6
    | ~ spl19_7
    | ~ spl19_8
    | ~ spl19_9
    | spl19_10 ),
    inference(unit_resulting_resolution,[],[f2275,f2270,f2265,f2260,f2255,f2245,f2250,f2200])).

fof(f2200,plain,(
    ! [X2,X0,X1] :
      ( v6_orders_2(X2,X0)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_tarski(k1_xboole_0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f2153,f2175])).

fof(f2153,plain,(
    ! [X2,X0,X1] :
      ( v6_orders_2(X2,X0)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2009])).

fof(f2276,plain,(
    ~ spl19_10 ),
    inference(avatar_split_clause,[],[f2098,f2273])).

fof(f2098,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f2060])).

fof(f2060,plain,
    ( ( ~ m1_orders_2(sK2,sK0,sK3)
      | ~ r2_xboole_0(sK2,sK3) )
    & ( m1_orders_2(sK2,sK0,sK3)
      | r2_xboole_0(sK2,sK3) )
    & m2_orders_2(sK3,sK0,sK1)
    & m2_orders_2(sK2,sK0,sK1)
    & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f2055,f2059,f2058,f2057,f2056])).

fof(f2056,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ m1_orders_2(X2,X0,X3)
                      | ~ r2_xboole_0(X2,X3) )
                    & ( m1_orders_2(X2,X0,X3)
                      | r2_xboole_0(X2,X3) )
                    & m2_orders_2(X3,X0,X1) )
                & m2_orders_2(X2,X0,X1) )
            & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_orders_2(X2,sK0,X3)
                    | ~ r2_xboole_0(X2,X3) )
                  & ( m1_orders_2(X2,sK0,X3)
                    | r2_xboole_0(X2,X3) )
                  & m2_orders_2(X3,sK0,X1) )
              & m2_orders_2(X2,sK0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2057,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ m1_orders_2(X2,sK0,X3)
                  | ~ r2_xboole_0(X2,X3) )
                & ( m1_orders_2(X2,sK0,X3)
                  | r2_xboole_0(X2,X3) )
                & m2_orders_2(X3,sK0,X1) )
            & m2_orders_2(X2,sK0,X1) )
        & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ m1_orders_2(X2,sK0,X3)
                | ~ r2_xboole_0(X2,X3) )
              & ( m1_orders_2(X2,sK0,X3)
                | r2_xboole_0(X2,X3) )
              & m2_orders_2(X3,sK0,sK1) )
          & m2_orders_2(X2,sK0,sK1) )
      & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f2058,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ m1_orders_2(X2,sK0,X3)
              | ~ r2_xboole_0(X2,X3) )
            & ( m1_orders_2(X2,sK0,X3)
              | r2_xboole_0(X2,X3) )
            & m2_orders_2(X3,sK0,sK1) )
        & m2_orders_2(X2,sK0,sK1) )
   => ( ? [X3] :
          ( ( ~ m1_orders_2(sK2,sK0,X3)
            | ~ r2_xboole_0(sK2,X3) )
          & ( m1_orders_2(sK2,sK0,X3)
            | r2_xboole_0(sK2,X3) )
          & m2_orders_2(X3,sK0,sK1) )
      & m2_orders_2(sK2,sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f2059,plain,
    ( ? [X3] :
        ( ( ~ m1_orders_2(sK2,sK0,X3)
          | ~ r2_xboole_0(sK2,X3) )
        & ( m1_orders_2(sK2,sK0,X3)
          | r2_xboole_0(sK2,X3) )
        & m2_orders_2(X3,sK0,sK1) )
   => ( ( ~ m1_orders_2(sK2,sK0,sK3)
        | ~ r2_xboole_0(sK2,sK3) )
      & ( m1_orders_2(sK2,sK0,sK3)
        | r2_xboole_0(sK2,sK3) )
      & m2_orders_2(sK3,sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f2055,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_orders_2(X2,X0,X3)
                    | ~ r2_xboole_0(X2,X3) )
                  & ( m1_orders_2(X2,X0,X3)
                    | r2_xboole_0(X2,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f2054])).

fof(f2054,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_orders_2(X2,X0,X3)
                    | ~ r2_xboole_0(X2,X3) )
                  & ( m1_orders_2(X2,X0,X3)
                    | r2_xboole_0(X2,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f1969])).

fof(f1969,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r2_xboole_0(X2,X3)
                  <~> m1_orders_2(X2,X0,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f1968])).

fof(f1968,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r2_xboole_0(X2,X3)
                  <~> m1_orders_2(X2,X0,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1956])).

fof(f1956,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m2_orders_2(X2,X0,X1)
               => ! [X3] :
                    ( m2_orders_2(X3,X0,X1)
                   => ( r2_xboole_0(X2,X3)
                    <=> m1_orders_2(X2,X0,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1955])).

fof(f1955,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X1)
                 => ( r2_xboole_0(X2,X3)
                  <=> m1_orders_2(X2,X0,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_orders_2)).

fof(f2271,plain,(
    spl19_9 ),
    inference(avatar_split_clause,[],[f2099,f2268])).

fof(f2099,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f2060])).

fof(f2266,plain,(
    spl19_8 ),
    inference(avatar_split_clause,[],[f2100,f2263])).

fof(f2100,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f2060])).

fof(f2261,plain,(
    spl19_7 ),
    inference(avatar_split_clause,[],[f2101,f2258])).

fof(f2101,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f2060])).

fof(f2256,plain,(
    spl19_6 ),
    inference(avatar_split_clause,[],[f2102,f2253])).

fof(f2102,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f2060])).

fof(f2251,plain,(
    spl19_5 ),
    inference(avatar_split_clause,[],[f2195,f2248])).

fof(f2195,plain,(
    m1_orders_1(sK1,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k9_setfam_1(u1_struct_0(sK0)),k1_tarski(k1_xboole_0))) ),
    inference(definition_unfolding,[],[f2103,f2175])).

fof(f2103,plain,(
    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f2060])).

fof(f2246,plain,(
    spl19_4 ),
    inference(avatar_split_clause,[],[f2104,f2243])).

fof(f2104,plain,(
    m2_orders_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f2060])).

fof(f2241,plain,(
    spl19_3 ),
    inference(avatar_split_clause,[],[f2105,f2238])).

fof(f2105,plain,(
    m2_orders_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f2060])).

fof(f2236,plain,
    ( spl19_1
    | spl19_2 ),
    inference(avatar_split_clause,[],[f2106,f2232,f2228])).

fof(f2106,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f2060])).

fof(f2235,plain,
    ( ~ spl19_1
    | ~ spl19_2 ),
    inference(avatar_split_clause,[],[f2107,f2232,f2228])).

fof(f2107,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f2060])).
%------------------------------------------------------------------------------
