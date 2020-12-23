%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1587+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:26 EST 2020

% Result     : Theorem 3.42s
% Output     : Refutation 3.42s
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
fof(f6740,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f6067,f6072,f6077,f6082,f6087,f6092,f6097,f6102,f6117,f6122,f6136,f6440,f6626,f6726,f6738])).

fof(f6738,plain,
    ( spl336_1
    | ~ spl336_2
    | ~ spl336_3
    | spl336_4
    | ~ spl336_5
    | ~ spl336_6
    | ~ spl336_7
    | ~ spl336_8
    | ~ spl336_11
    | ~ spl336_12
    | spl336_15
    | spl336_65 ),
    inference(avatar_contradiction_clause,[],[f6737])).

fof(f6737,plain,
    ( $false
    | spl336_1
    | ~ spl336_2
    | ~ spl336_3
    | spl336_4
    | ~ spl336_5
    | ~ spl336_6
    | ~ spl336_7
    | ~ spl336_8
    | ~ spl336_11
    | ~ spl336_12
    | spl336_15
    | spl336_65 ),
    inference(subsumption_resolution,[],[f6736,f6724])).

fof(f6724,plain,
    ( m1_subset_1(k2_tarski(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl336_7
    | ~ spl336_8
    | spl336_65 ),
    inference(backward_demodulation,[],[f6684,f6723])).

fof(f6723,plain,
    ( k7_domain_1(u1_struct_0(sK3),sK5,sK4) = k2_tarski(sK4,sK5)
    | ~ spl336_7
    | ~ spl336_8
    | spl336_65 ),
    inference(forward_demodulation,[],[f6673,f4862])).

fof(f4862,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f173])).

fof(f173,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f6673,plain,
    ( k7_domain_1(u1_struct_0(sK3),sK5,sK4) = k2_tarski(sK5,sK4)
    | ~ spl336_7
    | ~ spl336_8
    | spl336_65 ),
    inference(unit_resulting_resolution,[],[f6101,f6096,f6625,f4395])).

fof(f4395,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | ~ m1_subset_1(X2,X0)
      | k2_tarski(X1,X2) = k7_domain_1(X0,X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f3130])).

fof(f3130,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X1,X2) = k7_domain_1(X0,X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f3129])).

fof(f3129,plain,(
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

fof(f6625,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3))
    | spl336_65 ),
    inference(avatar_component_clause,[],[f6623])).

fof(f6623,plain,
    ( spl336_65
  <=> v1_xboole_0(u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl336_65])])).

fof(f6096,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ spl336_7 ),
    inference(avatar_component_clause,[],[f6094])).

fof(f6094,plain,
    ( spl336_7
  <=> m1_subset_1(sK4,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl336_7])])).

fof(f6101,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl336_8 ),
    inference(avatar_component_clause,[],[f6099])).

fof(f6099,plain,
    ( spl336_8
  <=> m1_subset_1(sK5,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl336_8])])).

fof(f6684,plain,
    ( m1_subset_1(k7_domain_1(u1_struct_0(sK3),sK5,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl336_7
    | ~ spl336_8
    | spl336_65 ),
    inference(unit_resulting_resolution,[],[f6096,f6101,f6625,f4396])).

fof(f4396,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f3132])).

fof(f3132,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f3131])).

fof(f3131,plain,(
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

fof(f6736,plain,
    ( ~ m1_subset_1(k2_tarski(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | spl336_1
    | ~ spl336_2
    | ~ spl336_3
    | spl336_4
    | ~ spl336_5
    | ~ spl336_6
    | ~ spl336_7
    | ~ spl336_8
    | ~ spl336_11
    | ~ spl336_12
    | spl336_15
    | spl336_65 ),
    inference(forward_demodulation,[],[f6341,f6675])).

fof(f6675,plain,
    ( k7_domain_1(u1_struct_0(sK3),sK4,sK5) = k2_tarski(sK4,sK5)
    | ~ spl336_7
    | ~ spl336_8
    | spl336_65 ),
    inference(unit_resulting_resolution,[],[f6096,f6101,f6625,f4395])).

fof(f6341,plain,
    ( ~ m1_subset_1(k7_domain_1(u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | spl336_1
    | ~ spl336_2
    | ~ spl336_3
    | spl336_4
    | ~ spl336_5
    | ~ spl336_6
    | ~ spl336_11
    | ~ spl336_12
    | spl336_15 ),
    inference(unit_resulting_resolution,[],[f6066,f6071,f6076,f6081,f6086,f6091,f6116,f6121,f6135,f4416])).

fof(f4416,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
      | k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
      | ~ r2_yellow_0(X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3151])).

fof(f3151,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
                & r2_yellow_0(X1,X2) )
              | ~ r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
              | ~ r2_yellow_0(X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3150])).

fof(f3150,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
                & r2_yellow_0(X1,X2) )
              | ~ r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
              | ~ r2_yellow_0(X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3056])).

fof(f3056,axiom,(
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
             => ( ( r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
                  & r2_yellow_0(X0,X2) )
               => ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
                  & r2_yellow_0(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_yellow_0)).

fof(f6135,plain,
    ( k2_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),sK4,sK5)) != k2_yellow_0(sK3,k7_domain_1(u1_struct_0(sK3),sK4,sK5))
    | spl336_15 ),
    inference(avatar_component_clause,[],[f6133])).

fof(f6133,plain,
    ( spl336_15
  <=> k2_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),sK4,sK5)) = k2_yellow_0(sK3,k7_domain_1(u1_struct_0(sK3),sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl336_15])])).

fof(f6121,plain,
    ( r2_hidden(k2_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),sK4,sK5)),u1_struct_0(sK3))
    | ~ spl336_12 ),
    inference(avatar_component_clause,[],[f6119])).

fof(f6119,plain,
    ( spl336_12
  <=> r2_hidden(k2_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),sK4,sK5)),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl336_12])])).

fof(f6116,plain,
    ( r2_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),sK4,sK5))
    | ~ spl336_11 ),
    inference(avatar_component_clause,[],[f6114])).

fof(f6114,plain,
    ( spl336_11
  <=> r2_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl336_11])])).

fof(f6091,plain,
    ( m1_yellow_0(sK3,sK2)
    | ~ spl336_6 ),
    inference(avatar_component_clause,[],[f6089])).

fof(f6089,plain,
    ( spl336_6
  <=> m1_yellow_0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl336_6])])).

fof(f6086,plain,
    ( v4_yellow_0(sK3,sK2)
    | ~ spl336_5 ),
    inference(avatar_component_clause,[],[f6084])).

fof(f6084,plain,
    ( spl336_5
  <=> v4_yellow_0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl336_5])])).

fof(f6081,plain,
    ( ~ v2_struct_0(sK3)
    | spl336_4 ),
    inference(avatar_component_clause,[],[f6079])).

fof(f6079,plain,
    ( spl336_4
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl336_4])])).

fof(f6076,plain,
    ( l1_orders_2(sK2)
    | ~ spl336_3 ),
    inference(avatar_component_clause,[],[f6074])).

fof(f6074,plain,
    ( spl336_3
  <=> l1_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl336_3])])).

fof(f6071,plain,
    ( v4_orders_2(sK2)
    | ~ spl336_2 ),
    inference(avatar_component_clause,[],[f6069])).

fof(f6069,plain,
    ( spl336_2
  <=> v4_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl336_2])])).

fof(f6066,plain,
    ( ~ v2_struct_0(sK2)
    | spl336_1 ),
    inference(avatar_component_clause,[],[f6064])).

fof(f6064,plain,
    ( spl336_1
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl336_1])])).

fof(f6726,plain,
    ( spl336_1
    | ~ spl336_2
    | ~ spl336_3
    | spl336_4
    | ~ spl336_5
    | ~ spl336_6
    | ~ spl336_7
    | ~ spl336_8
    | ~ spl336_11
    | ~ spl336_12
    | spl336_14
    | spl336_65 ),
    inference(avatar_contradiction_clause,[],[f6725])).

fof(f6725,plain,
    ( $false
    | spl336_1
    | ~ spl336_2
    | ~ spl336_3
    | spl336_4
    | ~ spl336_5
    | ~ spl336_6
    | ~ spl336_7
    | ~ spl336_8
    | ~ spl336_11
    | ~ spl336_12
    | spl336_14
    | spl336_65 ),
    inference(subsumption_resolution,[],[f6724,f6715])).

fof(f6715,plain,
    ( ~ m1_subset_1(k2_tarski(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | spl336_1
    | ~ spl336_2
    | ~ spl336_3
    | spl336_4
    | ~ spl336_5
    | ~ spl336_6
    | ~ spl336_7
    | ~ spl336_8
    | ~ spl336_11
    | ~ spl336_12
    | spl336_14
    | spl336_65 ),
    inference(backward_demodulation,[],[f6312,f6675])).

fof(f6312,plain,
    ( ~ m1_subset_1(k7_domain_1(u1_struct_0(sK3),sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | spl336_1
    | ~ spl336_2
    | ~ spl336_3
    | spl336_4
    | ~ spl336_5
    | ~ spl336_6
    | ~ spl336_11
    | ~ spl336_12
    | spl336_14 ),
    inference(unit_resulting_resolution,[],[f6066,f6071,f6076,f6081,f6086,f6091,f6131,f6116,f6121,f4415])).

fof(f4415,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
      | r2_yellow_0(X1,X2)
      | ~ r2_yellow_0(X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3151])).

fof(f6131,plain,
    ( ~ r2_yellow_0(sK3,k7_domain_1(u1_struct_0(sK3),sK4,sK5))
    | spl336_14 ),
    inference(avatar_component_clause,[],[f6129])).

fof(f6129,plain,
    ( spl336_14
  <=> r2_yellow_0(sK3,k7_domain_1(u1_struct_0(sK3),sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl336_14])])).

fof(f6626,plain,
    ( ~ spl336_65
    | ~ spl336_53 ),
    inference(avatar_split_clause,[],[f6619,f6437,f6623])).

fof(f6437,plain,
    ( spl336_53
  <=> r2_hidden(sK6(u1_struct_0(sK3)),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl336_53])])).

fof(f6619,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3))
    | ~ spl336_53 ),
    inference(unit_resulting_resolution,[],[f6439,f4788])).

fof(f4788,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f3337])).

fof(f3337,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f148])).

fof(f148,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f6439,plain,
    ( r2_hidden(sK6(u1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ spl336_53 ),
    inference(avatar_component_clause,[],[f6437])).

fof(f6440,plain,
    ( spl336_53
    | ~ spl336_12 ),
    inference(avatar_split_clause,[],[f6163,f6119,f6437])).

fof(f6163,plain,
    ( r2_hidden(sK6(u1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ spl336_12 ),
    inference(unit_resulting_resolution,[],[f6121,f4303])).

fof(f4303,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(sK6(X1),X1) ) ),
    inference(cnf_transformation,[],[f3794])).

fof(f3794,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK6(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK6(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f3087,f3793])).

fof(f3793,plain,(
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

fof(f3087,plain,(
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

fof(f6136,plain,
    ( ~ spl336_14
    | ~ spl336_15 ),
    inference(avatar_split_clause,[],[f4297,f6133,f6129])).

fof(f4297,plain,
    ( k2_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),sK4,sK5)) != k2_yellow_0(sK3,k7_domain_1(u1_struct_0(sK3),sK4,sK5))
    | ~ r2_yellow_0(sK3,k7_domain_1(u1_struct_0(sK3),sK4,sK5)) ),
    inference(cnf_transformation,[],[f3792])).

fof(f3792,plain,
    ( ( k2_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),sK4,sK5)) != k2_yellow_0(sK3,k7_domain_1(u1_struct_0(sK3),sK4,sK5))
      | ~ r2_yellow_0(sK3,k7_domain_1(u1_struct_0(sK3),sK4,sK5)) )
    & r2_hidden(k2_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),sK4,sK5)),u1_struct_0(sK3))
    & r2_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),sK4,sK5))
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & m1_yellow_0(sK3,sK2)
    & v4_yellow_0(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_orders_2(sK2)
    & v4_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f3080,f3791,f3790,f3789,f3788])).

fof(f3788,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( k2_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)) != k2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3))
                      | ~ r2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) )
                    & r2_hidden(k2_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)),u1_struct_0(X1))
                    & r2_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3))
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
                  ( ( k2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) != k2_yellow_0(sK2,k7_domain_1(u1_struct_0(X1),X2,X3))
                    | ~ r2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) )
                  & r2_hidden(k2_yellow_0(sK2,k7_domain_1(u1_struct_0(X1),X2,X3)),u1_struct_0(X1))
                  & r2_yellow_0(sK2,k7_domain_1(u1_struct_0(X1),X2,X3))
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_yellow_0(X1,sK2)
          & v4_yellow_0(X1,sK2)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(sK2)
      & v4_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f3789,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( k2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) != k2_yellow_0(sK2,k7_domain_1(u1_struct_0(X1),X2,X3))
                  | ~ r2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) )
                & r2_hidden(k2_yellow_0(sK2,k7_domain_1(u1_struct_0(X1),X2,X3)),u1_struct_0(X1))
                & r2_yellow_0(sK2,k7_domain_1(u1_struct_0(X1),X2,X3))
                & m1_subset_1(X3,u1_struct_0(X1)) )
            & m1_subset_1(X2,u1_struct_0(X1)) )
        & m1_yellow_0(X1,sK2)
        & v4_yellow_0(X1,sK2)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( k2_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),X2,X3)) != k2_yellow_0(sK3,k7_domain_1(u1_struct_0(sK3),X2,X3))
                | ~ r2_yellow_0(sK3,k7_domain_1(u1_struct_0(sK3),X2,X3)) )
              & r2_hidden(k2_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),X2,X3)),u1_struct_0(sK3))
              & r2_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),X2,X3))
              & m1_subset_1(X3,u1_struct_0(sK3)) )
          & m1_subset_1(X2,u1_struct_0(sK3)) )
      & m1_yellow_0(sK3,sK2)
      & v4_yellow_0(sK3,sK2)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f3790,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( k2_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),X2,X3)) != k2_yellow_0(sK3,k7_domain_1(u1_struct_0(sK3),X2,X3))
              | ~ r2_yellow_0(sK3,k7_domain_1(u1_struct_0(sK3),X2,X3)) )
            & r2_hidden(k2_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),X2,X3)),u1_struct_0(sK3))
            & r2_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),X2,X3))
            & m1_subset_1(X3,u1_struct_0(sK3)) )
        & m1_subset_1(X2,u1_struct_0(sK3)) )
   => ( ? [X3] :
          ( ( k2_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),sK4,X3)) != k2_yellow_0(sK3,k7_domain_1(u1_struct_0(sK3),sK4,X3))
            | ~ r2_yellow_0(sK3,k7_domain_1(u1_struct_0(sK3),sK4,X3)) )
          & r2_hidden(k2_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),sK4,X3)),u1_struct_0(sK3))
          & r2_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),sK4,X3))
          & m1_subset_1(X3,u1_struct_0(sK3)) )
      & m1_subset_1(sK4,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f3791,plain,
    ( ? [X3] :
        ( ( k2_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),sK4,X3)) != k2_yellow_0(sK3,k7_domain_1(u1_struct_0(sK3),sK4,X3))
          | ~ r2_yellow_0(sK3,k7_domain_1(u1_struct_0(sK3),sK4,X3)) )
        & r2_hidden(k2_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),sK4,X3)),u1_struct_0(sK3))
        & r2_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),sK4,X3))
        & m1_subset_1(X3,u1_struct_0(sK3)) )
   => ( ( k2_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),sK4,sK5)) != k2_yellow_0(sK3,k7_domain_1(u1_struct_0(sK3),sK4,sK5))
        | ~ r2_yellow_0(sK3,k7_domain_1(u1_struct_0(sK3),sK4,sK5)) )
      & r2_hidden(k2_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),sK4,sK5)),u1_struct_0(sK3))
      & r2_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),sK4,sK5))
      & m1_subset_1(sK5,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f3080,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( k2_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)) != k2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3))
                    | ~ r2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) )
                  & r2_hidden(k2_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)),u1_struct_0(X1))
                  & r2_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3))
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3079])).

fof(f3079,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( k2_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)) != k2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3))
                    | ~ r2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) )
                  & r2_hidden(k2_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)),u1_struct_0(X1))
                  & r2_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3))
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3059])).

fof(f3059,negated_conjecture,(
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
                   => ( ( r2_hidden(k2_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)),u1_struct_0(X1))
                        & r2_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)) )
                     => ( k2_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)) = k2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3))
                        & r2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3058])).

fof(f3058,conjecture,(
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
                 => ( ( r2_hidden(k2_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)),u1_struct_0(X1))
                      & r2_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)) )
                   => ( k2_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)) = k2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3))
                      & r2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_yellow_0)).

fof(f6122,plain,(
    spl336_12 ),
    inference(avatar_split_clause,[],[f4296,f6119])).

fof(f4296,plain,(
    r2_hidden(k2_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),sK4,sK5)),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f3792])).

fof(f6117,plain,(
    spl336_11 ),
    inference(avatar_split_clause,[],[f4295,f6114])).

fof(f4295,plain,(
    r2_yellow_0(sK2,k7_domain_1(u1_struct_0(sK3),sK4,sK5)) ),
    inference(cnf_transformation,[],[f3792])).

fof(f6102,plain,(
    spl336_8 ),
    inference(avatar_split_clause,[],[f4294,f6099])).

fof(f4294,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f3792])).

fof(f6097,plain,(
    spl336_7 ),
    inference(avatar_split_clause,[],[f4293,f6094])).

fof(f4293,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f3792])).

fof(f6092,plain,(
    spl336_6 ),
    inference(avatar_split_clause,[],[f4292,f6089])).

fof(f4292,plain,(
    m1_yellow_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f3792])).

fof(f6087,plain,(
    spl336_5 ),
    inference(avatar_split_clause,[],[f4291,f6084])).

fof(f4291,plain,(
    v4_yellow_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f3792])).

fof(f6082,plain,(
    ~ spl336_4 ),
    inference(avatar_split_clause,[],[f4290,f6079])).

fof(f4290,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f3792])).

fof(f6077,plain,(
    spl336_3 ),
    inference(avatar_split_clause,[],[f4289,f6074])).

fof(f4289,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f3792])).

fof(f6072,plain,(
    spl336_2 ),
    inference(avatar_split_clause,[],[f4288,f6069])).

fof(f4288,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f3792])).

fof(f6067,plain,(
    ~ spl336_1 ),
    inference(avatar_split_clause,[],[f4287,f6064])).

fof(f4287,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f3792])).
%------------------------------------------------------------------------------
