%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1588+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:26 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 280 expanded)
%              Number of leaves         :   26 ( 122 expanded)
%              Depth                    :    9
%              Number of atoms          :  442 (1929 expanded)
%              Number of equality atoms :   29 ( 180 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6824,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f6089,f6094,f6099,f6104,f6109,f6114,f6119,f6124,f6139,f6144,f6158,f6485,f6675,f6810,f6822])).

fof(f6822,plain,
    ( spl339_1
    | ~ spl339_2
    | ~ spl339_3
    | spl339_4
    | ~ spl339_5
    | ~ spl339_6
    | ~ spl339_7
    | ~ spl339_8
    | ~ spl339_11
    | ~ spl339_12
    | spl339_15
    | spl339_72 ),
    inference(avatar_contradiction_clause,[],[f6821])).

fof(f6821,plain,
    ( $false
    | spl339_1
    | ~ spl339_2
    | ~ spl339_3
    | spl339_4
    | ~ spl339_5
    | ~ spl339_6
    | ~ spl339_7
    | ~ spl339_8
    | ~ spl339_11
    | ~ spl339_12
    | spl339_15
    | spl339_72 ),
    inference(subsumption_resolution,[],[f6820,f6808])).

fof(f6808,plain,
    ( m1_subset_1(k2_tarski(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl339_7
    | ~ spl339_8
    | spl339_72 ),
    inference(backward_demodulation,[],[f6768,f6807])).

fof(f6807,plain,
    ( k7_domain_1(u1_struct_0(sK3),sK5,sK4) = k2_tarski(sK4,sK5)
    | ~ spl339_7
    | ~ spl339_8
    | spl339_72 ),
    inference(forward_demodulation,[],[f6757,f4932])).

fof(f4932,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f173])).

fof(f173,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f6757,plain,
    ( k7_domain_1(u1_struct_0(sK3),sK5,sK4) = k2_tarski(sK5,sK4)
    | ~ spl339_7
    | ~ spl339_8
    | spl339_72 ),
    inference(unit_resulting_resolution,[],[f6123,f6118,f6674,f4404])).

fof(f4404,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | ~ m1_subset_1(X2,X0)
      | k2_tarski(X1,X2) = k7_domain_1(X0,X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f3133])).

fof(f3133,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X1,X2) = k7_domain_1(X0,X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f3132])).

fof(f3132,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X1,X2) = k7_domain_1(X0,X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1936])).

fof(f1936,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k2_tarski(X1,X2) = k7_domain_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_domain_1)).

fof(f6674,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3))
    | spl339_72 ),
    inference(avatar_component_clause,[],[f6672])).

fof(f6672,plain,
    ( spl339_72
  <=> v1_xboole_0(u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl339_72])])).

fof(f6118,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ spl339_7 ),
    inference(avatar_component_clause,[],[f6116])).

fof(f6116,plain,
    ( spl339_7
  <=> m1_subset_1(sK4,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl339_7])])).

fof(f6123,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl339_8 ),
    inference(avatar_component_clause,[],[f6121])).

fof(f6121,plain,
    ( spl339_8
  <=> m1_subset_1(sK5,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl339_8])])).

fof(f6768,plain,
    ( m1_subset_1(k7_domain_1(u1_struct_0(sK3),sK5,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl339_7
    | ~ spl339_8
    | spl339_72 ),
    inference(unit_resulting_resolution,[],[f6118,f6123,f6674,f4405])).

fof(f4405,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f3135])).

fof(f3135,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f3134])).

fof(f3134,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1894])).

fof(f1894,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_domain_1)).

fof(f6820,plain,
    ( ~ m1_subset_1(k2_tarski(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | spl339_1
    | ~ spl339_2
    | ~ spl339_3
    | spl339_4
    | ~ spl339_5
    | ~ spl339_6
    | ~ spl339_7
    | ~ spl339_8
    | ~ spl339_11
    | ~ spl339_12
    | spl339_15
    | spl339_72 ),
    inference(forward_demodulation,[],[f6367,f6759])).

fof(f6759,plain,
    ( k7_domain_1(u1_struct_0(sK3),sK4,sK5) = k2_tarski(sK4,sK5)
    | ~ spl339_7
    | ~ spl339_8
    | spl339_72 ),
    inference(unit_resulting_resolution,[],[f6118,f6123,f6674,f4404])).

fof(f6367,plain,
    ( ~ m1_subset_1(k7_domain_1(u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | spl339_1
    | ~ spl339_2
    | ~ spl339_3
    | spl339_4
    | ~ spl339_5
    | ~ spl339_6
    | ~ spl339_11
    | ~ spl339_12
    | spl339_15 ),
    inference(unit_resulting_resolution,[],[f6088,f6093,f6098,f6103,f6108,f6113,f6138,f6143,f6157,f4425])).

fof(f4425,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
      | k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
      | ~ r1_yellow_0(X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3154])).

fof(f3154,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
                & r1_yellow_0(X1,X2) )
              | ~ r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
              | ~ r1_yellow_0(X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3153])).

fof(f3153,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
                & r1_yellow_0(X1,X2) )
              | ~ r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
              | ~ r1_yellow_0(X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3057])).

fof(f3057,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
                  & r1_yellow_0(X0,X2) )
               => ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
                  & r1_yellow_0(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_yellow_0)).

fof(f6157,plain,
    ( k1_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),sK4,sK5)) != k1_yellow_0(sK3,k7_domain_1(u1_struct_0(sK3),sK4,sK5))
    | spl339_15 ),
    inference(avatar_component_clause,[],[f6155])).

fof(f6155,plain,
    ( spl339_15
  <=> k1_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),sK4,sK5)) = k1_yellow_0(sK3,k7_domain_1(u1_struct_0(sK3),sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl339_15])])).

fof(f6143,plain,
    ( r2_hidden(k1_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),sK4,sK5)),u1_struct_0(sK3))
    | ~ spl339_12 ),
    inference(avatar_component_clause,[],[f6141])).

fof(f6141,plain,
    ( spl339_12
  <=> r2_hidden(k1_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),sK4,sK5)),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl339_12])])).

fof(f6138,plain,
    ( r1_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),sK4,sK5))
    | ~ spl339_11 ),
    inference(avatar_component_clause,[],[f6136])).

fof(f6136,plain,
    ( spl339_11
  <=> r1_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl339_11])])).

fof(f6113,plain,
    ( m1_yellow_0(sK3,sK2)
    | ~ spl339_6 ),
    inference(avatar_component_clause,[],[f6111])).

fof(f6111,plain,
    ( spl339_6
  <=> m1_yellow_0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl339_6])])).

fof(f6108,plain,
    ( v4_yellow_0(sK3,sK2)
    | ~ spl339_5 ),
    inference(avatar_component_clause,[],[f6106])).

fof(f6106,plain,
    ( spl339_5
  <=> v4_yellow_0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl339_5])])).

fof(f6103,plain,
    ( ~ v2_struct_0(sK3)
    | spl339_4 ),
    inference(avatar_component_clause,[],[f6101])).

fof(f6101,plain,
    ( spl339_4
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl339_4])])).

fof(f6098,plain,
    ( l1_orders_2(sK2)
    | ~ spl339_3 ),
    inference(avatar_component_clause,[],[f6096])).

fof(f6096,plain,
    ( spl339_3
  <=> l1_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl339_3])])).

fof(f6093,plain,
    ( v4_orders_2(sK2)
    | ~ spl339_2 ),
    inference(avatar_component_clause,[],[f6091])).

fof(f6091,plain,
    ( spl339_2
  <=> v4_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl339_2])])).

fof(f6088,plain,
    ( ~ v2_struct_0(sK2)
    | spl339_1 ),
    inference(avatar_component_clause,[],[f6086])).

fof(f6086,plain,
    ( spl339_1
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl339_1])])).

fof(f6810,plain,
    ( spl339_1
    | ~ spl339_2
    | ~ spl339_3
    | spl339_4
    | ~ spl339_5
    | ~ spl339_6
    | ~ spl339_7
    | ~ spl339_8
    | ~ spl339_11
    | ~ spl339_12
    | spl339_14
    | spl339_72 ),
    inference(avatar_contradiction_clause,[],[f6809])).

fof(f6809,plain,
    ( $false
    | spl339_1
    | ~ spl339_2
    | ~ spl339_3
    | spl339_4
    | ~ spl339_5
    | ~ spl339_6
    | ~ spl339_7
    | ~ spl339_8
    | ~ spl339_11
    | ~ spl339_12
    | spl339_14
    | spl339_72 ),
    inference(subsumption_resolution,[],[f6808,f6797])).

fof(f6797,plain,
    ( ~ m1_subset_1(k2_tarski(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | spl339_1
    | ~ spl339_2
    | ~ spl339_3
    | spl339_4
    | ~ spl339_5
    | ~ spl339_6
    | ~ spl339_7
    | ~ spl339_8
    | ~ spl339_11
    | ~ spl339_12
    | spl339_14
    | spl339_72 ),
    inference(backward_demodulation,[],[f6334,f6759])).

fof(f6334,plain,
    ( ~ m1_subset_1(k7_domain_1(u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | spl339_1
    | ~ spl339_2
    | ~ spl339_3
    | spl339_4
    | ~ spl339_5
    | ~ spl339_6
    | ~ spl339_11
    | ~ spl339_12
    | spl339_14 ),
    inference(unit_resulting_resolution,[],[f6088,f6093,f6098,f6103,f6108,f6113,f6153,f6138,f6143,f4424])).

fof(f4424,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
      | r1_yellow_0(X1,X2)
      | ~ r1_yellow_0(X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3154])).

fof(f6153,plain,
    ( ~ r1_yellow_0(sK3,k7_domain_1(u1_struct_0(sK3),sK4,sK5))
    | spl339_14 ),
    inference(avatar_component_clause,[],[f6151])).

fof(f6151,plain,
    ( spl339_14
  <=> r1_yellow_0(sK3,k7_domain_1(u1_struct_0(sK3),sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl339_14])])).

fof(f6675,plain,
    ( ~ spl339_72
    | ~ spl339_60 ),
    inference(avatar_split_clause,[],[f6661,f6482,f6672])).

fof(f6482,plain,
    ( spl339_60
  <=> r2_hidden(sK6(u1_struct_0(sK3)),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl339_60])])).

fof(f6661,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3))
    | ~ spl339_60 ),
    inference(unit_resulting_resolution,[],[f6484,f4858])).

fof(f4858,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f3383])).

fof(f3383,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f148])).

fof(f148,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f6484,plain,
    ( r2_hidden(sK6(u1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ spl339_60 ),
    inference(avatar_component_clause,[],[f6482])).

fof(f6485,plain,
    ( spl339_60
    | ~ spl339_12 ),
    inference(avatar_split_clause,[],[f6185,f6141,f6482])).

fof(f6185,plain,
    ( r2_hidden(sK6(u1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ spl339_12 ),
    inference(unit_resulting_resolution,[],[f6143,f4312])).

fof(f4312,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(sK6(X1),X1) ) ),
    inference(cnf_transformation,[],[f3797])).

fof(f3797,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK6(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK6(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f3088,f3796])).

fof(f3796,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK6(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK6(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f3088,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f433])).

fof(f433,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

fof(f6158,plain,
    ( ~ spl339_14
    | ~ spl339_15 ),
    inference(avatar_split_clause,[],[f4306,f6155,f6151])).

fof(f4306,plain,
    ( k1_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),sK4,sK5)) != k1_yellow_0(sK3,k7_domain_1(u1_struct_0(sK3),sK4,sK5))
    | ~ r1_yellow_0(sK3,k7_domain_1(u1_struct_0(sK3),sK4,sK5)) ),
    inference(cnf_transformation,[],[f3795])).

fof(f3795,plain,
    ( ( k1_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),sK4,sK5)) != k1_yellow_0(sK3,k7_domain_1(u1_struct_0(sK3),sK4,sK5))
      | ~ r1_yellow_0(sK3,k7_domain_1(u1_struct_0(sK3),sK4,sK5)) )
    & r2_hidden(k1_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),sK4,sK5)),u1_struct_0(sK3))
    & r1_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),sK4,sK5))
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & m1_yellow_0(sK3,sK2)
    & v4_yellow_0(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_orders_2(sK2)
    & v4_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f3081,f3794,f3793,f3792,f3791])).

fof(f3791,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( k1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)) != k1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3))
                      | ~ r1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) )
                    & r2_hidden(k1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)),u1_struct_0(X1))
                    & r1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3))
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                & m1_subset_1(X2,u1_struct_0(X1)) )
            & m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( k1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) != k1_yellow_0(sK2,k7_domain_1(u1_struct_0(X1),X2,X3))
                    | ~ r1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) )
                  & r2_hidden(k1_yellow_0(sK2,k7_domain_1(u1_struct_0(X1),X2,X3)),u1_struct_0(X1))
                  & r1_yellow_0(sK2,k7_domain_1(u1_struct_0(X1),X2,X3))
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_yellow_0(X1,sK2)
          & v4_yellow_0(X1,sK2)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(sK2)
      & v4_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f3792,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( k1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) != k1_yellow_0(sK2,k7_domain_1(u1_struct_0(X1),X2,X3))
                  | ~ r1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) )
                & r2_hidden(k1_yellow_0(sK2,k7_domain_1(u1_struct_0(X1),X2,X3)),u1_struct_0(X1))
                & r1_yellow_0(sK2,k7_domain_1(u1_struct_0(X1),X2,X3))
                & m1_subset_1(X3,u1_struct_0(X1)) )
            & m1_subset_1(X2,u1_struct_0(X1)) )
        & m1_yellow_0(X1,sK2)
        & v4_yellow_0(X1,sK2)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( k1_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),X2,X3)) != k1_yellow_0(sK3,k7_domain_1(u1_struct_0(sK3),X2,X3))
                | ~ r1_yellow_0(sK3,k7_domain_1(u1_struct_0(sK3),X2,X3)) )
              & r2_hidden(k1_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),X2,X3)),u1_struct_0(sK3))
              & r1_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),X2,X3))
              & m1_subset_1(X3,u1_struct_0(sK3)) )
          & m1_subset_1(X2,u1_struct_0(sK3)) )
      & m1_yellow_0(sK3,sK2)
      & v4_yellow_0(sK3,sK2)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f3793,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( k1_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),X2,X3)) != k1_yellow_0(sK3,k7_domain_1(u1_struct_0(sK3),X2,X3))
              | ~ r1_yellow_0(sK3,k7_domain_1(u1_struct_0(sK3),X2,X3)) )
            & r2_hidden(k1_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),X2,X3)),u1_struct_0(sK3))
            & r1_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),X2,X3))
            & m1_subset_1(X3,u1_struct_0(sK3)) )
        & m1_subset_1(X2,u1_struct_0(sK3)) )
   => ( ? [X3] :
          ( ( k1_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),sK4,X3)) != k1_yellow_0(sK3,k7_domain_1(u1_struct_0(sK3),sK4,X3))
            | ~ r1_yellow_0(sK3,k7_domain_1(u1_struct_0(sK3),sK4,X3)) )
          & r2_hidden(k1_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),sK4,X3)),u1_struct_0(sK3))
          & r1_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),sK4,X3))
          & m1_subset_1(X3,u1_struct_0(sK3)) )
      & m1_subset_1(sK4,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f3794,plain,
    ( ? [X3] :
        ( ( k1_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),sK4,X3)) != k1_yellow_0(sK3,k7_domain_1(u1_struct_0(sK3),sK4,X3))
          | ~ r1_yellow_0(sK3,k7_domain_1(u1_struct_0(sK3),sK4,X3)) )
        & r2_hidden(k1_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),sK4,X3)),u1_struct_0(sK3))
        & r1_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),sK4,X3))
        & m1_subset_1(X3,u1_struct_0(sK3)) )
   => ( ( k1_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),sK4,sK5)) != k1_yellow_0(sK3,k7_domain_1(u1_struct_0(sK3),sK4,sK5))
        | ~ r1_yellow_0(sK3,k7_domain_1(u1_struct_0(sK3),sK4,sK5)) )
      & r2_hidden(k1_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),sK4,sK5)),u1_struct_0(sK3))
      & r1_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),sK4,sK5))
      & m1_subset_1(sK5,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f3081,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( k1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)) != k1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3))
                    | ~ r1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) )
                  & r2_hidden(k1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)),u1_struct_0(X1))
                  & r1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3))
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3080])).

fof(f3080,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( k1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)) != k1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3))
                    | ~ r1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) )
                  & r2_hidden(k1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)),u1_struct_0(X1))
                  & r1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3))
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3060])).

fof(f3060,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_yellow_0(X1,X0)
              & v4_yellow_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => ( ( r2_hidden(k1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)),u1_struct_0(X1))
                        & r1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)) )
                     => ( k1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)) = k1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3))
                        & r1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3059])).

fof(f3059,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ( ( r2_hidden(k1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)),u1_struct_0(X1))
                      & r1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)) )
                   => ( k1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)) = k1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3))
                      & r1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_yellow_0)).

fof(f6144,plain,(
    spl339_12 ),
    inference(avatar_split_clause,[],[f4305,f6141])).

fof(f4305,plain,(
    r2_hidden(k1_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),sK4,sK5)),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f3795])).

fof(f6139,plain,(
    spl339_11 ),
    inference(avatar_split_clause,[],[f4304,f6136])).

fof(f4304,plain,(
    r1_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),sK4,sK5)) ),
    inference(cnf_transformation,[],[f3795])).

fof(f6124,plain,(
    spl339_8 ),
    inference(avatar_split_clause,[],[f4303,f6121])).

fof(f4303,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f3795])).

fof(f6119,plain,(
    spl339_7 ),
    inference(avatar_split_clause,[],[f4302,f6116])).

fof(f4302,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f3795])).

fof(f6114,plain,(
    spl339_6 ),
    inference(avatar_split_clause,[],[f4301,f6111])).

fof(f4301,plain,(
    m1_yellow_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f3795])).

fof(f6109,plain,(
    spl339_5 ),
    inference(avatar_split_clause,[],[f4300,f6106])).

fof(f4300,plain,(
    v4_yellow_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f3795])).

fof(f6104,plain,(
    ~ spl339_4 ),
    inference(avatar_split_clause,[],[f4299,f6101])).

fof(f4299,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f3795])).

fof(f6099,plain,(
    spl339_3 ),
    inference(avatar_split_clause,[],[f4298,f6096])).

fof(f4298,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f3795])).

fof(f6094,plain,(
    spl339_2 ),
    inference(avatar_split_clause,[],[f4297,f6091])).

fof(f4297,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f3795])).

fof(f6089,plain,(
    ~ spl339_1 ),
    inference(avatar_split_clause,[],[f4296,f6086])).

fof(f4296,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f3795])).
%------------------------------------------------------------------------------
