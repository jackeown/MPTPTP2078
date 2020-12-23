%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : orders_2__t49_orders_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:21 EDT 2019

% Result     : Theorem 0.73s
% Output     : Refutation 0.73s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 330 expanded)
%              Number of leaves         :   35 ( 121 expanded)
%              Depth                    :   20
%              Number of atoms          :  638 (1429 expanded)
%              Number of equality atoms :   26 (  41 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f510,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f93,f100,f107,f114,f121,f128,f135,f142,f149,f162,f187,f208,f226,f233,f240,f251,f264,f271,f318,f416,f503,f504])).

fof(f504,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_40
    | ~ spl8_44 ),
    inference(avatar_contradiction_clause,[],[f496])).

fof(f496,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_40
    | ~ spl8_44 ),
    inference(resolution,[],[f448,f127])).

fof(f127,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl8_12
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f448,plain,
    ( ! [X0] : ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_40
    | ~ spl8_44 ),
    inference(subsumption_resolution,[],[f447,f141])).

fof(f141,plain,
    ( r2_hidden(sK1,k2_orders_2(sK0,sK2))
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl8_16
  <=> r2_hidden(sK1,k2_orders_2(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f447,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,k2_orders_2(sK0,sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_40
    | ~ spl8_44 ),
    inference(forward_demodulation,[],[f446,f270])).

fof(f270,plain,
    ( k2_orders_2(sK0,sK2) = a_2_1_orders_2(sK0,sK2)
    | ~ spl8_40 ),
    inference(avatar_component_clause,[],[f269])).

fof(f269,plain,
    ( spl8_40
  <=> k2_orders_2(sK0,sK2) = a_2_1_orders_2(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f446,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,a_2_1_orders_2(sK0,sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_44 ),
    inference(subsumption_resolution,[],[f445,f85])).

fof(f85,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl8_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f445,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ r2_hidden(sK1,a_2_1_orders_2(sK0,sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_44 ),
    inference(subsumption_resolution,[],[f444,f92])).

fof(f92,plain,
    ( v3_orders_2(sK0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl8_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f444,plain,
    ( ! [X0] :
        ( ~ v3_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ r2_hidden(sK1,a_2_1_orders_2(sK0,sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_44 ),
    inference(subsumption_resolution,[],[f443,f134])).

fof(f134,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl8_14
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f443,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ r2_hidden(sK1,a_2_1_orders_2(sK0,sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_44 ),
    inference(subsumption_resolution,[],[f442,f113])).

fof(f113,plain,
    ( l1_orders_2(sK0)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl8_8
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f442,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ r2_hidden(sK1,a_2_1_orders_2(sK0,sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_10
    | ~ spl8_44 ),
    inference(subsumption_resolution,[],[f441,f106])).

fof(f106,plain,
    ( v5_orders_2(sK0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl8_6
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f441,plain,
    ( ! [X0] :
        ( ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ r2_hidden(sK1,a_2_1_orders_2(sK0,sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_4
    | ~ spl8_10
    | ~ spl8_44 ),
    inference(subsumption_resolution,[],[f440,f99])).

fof(f99,plain,
    ( v4_orders_2(sK0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl8_4
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f440,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ r2_hidden(sK1,a_2_1_orders_2(sK0,sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_10
    | ~ spl8_44 ),
    inference(subsumption_resolution,[],[f439,f120])).

fof(f120,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl8_10
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f439,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,sK2)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ r2_hidden(sK1,a_2_1_orders_2(sK0,sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_44 ),
    inference(superposition,[],[f215,f415])).

fof(f415,plain,
    ( sK1 = sK3(sK1,sK0,sK2)
    | ~ spl8_44 ),
    inference(avatar_component_clause,[],[f414])).

fof(f414,plain,
    ( spl8_44
  <=> sK1 = sK3(sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_44])])).

fof(f215,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK3(X2,X0,X1),X1)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ r2_hidden(X2,a_2_1_orders_2(X0,X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f214,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t49_orders_2.p',t4_subset)).

fof(f214,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(sK3(X2,X0,X1),X1)
      | v2_struct_0(X0)
      | ~ r2_hidden(X2,a_2_1_orders_2(X0,X1))
      | ~ m1_subset_1(sK3(X2,X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f213])).

fof(f213,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(sK3(X2,X0,X1),X1)
      | v2_struct_0(X0)
      | ~ r2_hidden(X2,a_2_1_orders_2(X0,X1))
      | ~ m1_subset_1(sK3(X2,X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f79,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => ~ r2_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t49_orders_2.p',irreflexivity_r2_orders_2)).

fof(f79,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_orders_2(X1,sK3(X0,X1,X2),X4)
      | ~ v3_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(X4,X2)
      | v2_struct_0(X1)
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) ),
    inference(subsumption_resolution,[],[f63,f59])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( v2_struct_0(X1)
      | ~ v3_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ r2_hidden(X4,X2)
      | r2_orders_2(X1,sK3(X0,X1,X2),X4)
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X3,X4)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X3,X4)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & v5_orders_2(X1)
        & v4_orders_2(X1)
        & v3_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r2_orders_2(X1,X3,X4) ) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t49_orders_2.p',fraenkel_a_2_1_orders_2)).

fof(f503,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_40
    | ~ spl8_44 ),
    inference(avatar_contradiction_clause,[],[f502])).

fof(f502,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_40
    | ~ spl8_44 ),
    inference(resolution,[],[f448,f72])).

fof(f72,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t49_orders_2.p',existence_m1_subset_1)).

fof(f416,plain,
    ( spl8_44
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_40 ),
    inference(avatar_split_clause,[],[f372,f269,f140,f133,f112,f105,f98,f91,f84,f414])).

fof(f372,plain,
    ( sK1 = sK3(sK1,sK0,sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_40 ),
    inference(resolution,[],[f278,f141])).

fof(f278,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_orders_2(sK0,sK2))
        | sK3(X0,sK0,sK2) = X0 )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f277,f85])).

fof(f277,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_orders_2(sK0,sK2))
        | sK3(X0,sK0,sK2) = X0
        | v2_struct_0(sK0) )
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f276,f134])).

fof(f276,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_orders_2(sK0,sK2))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
        | sK3(X0,sK0,sK2) = X0
        | v2_struct_0(sK0) )
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f275,f113])).

fof(f275,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_orders_2(sK0,sK2))
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
        | sK3(X0,sK0,sK2) = X0
        | v2_struct_0(sK0) )
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f274,f106])).

fof(f274,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_orders_2(sK0,sK2))
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
        | sK3(X0,sK0,sK2) = X0
        | v2_struct_0(sK0) )
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f273,f99])).

fof(f273,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_orders_2(sK0,sK2))
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
        | sK3(X0,sK0,sK2) = X0
        | v2_struct_0(sK0) )
    | ~ spl8_2
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f272,f92])).

fof(f272,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_orders_2(sK0,sK2))
        | ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
        | sK3(X0,sK0,sK2) = X0
        | v2_struct_0(sK0) )
    | ~ spl8_40 ),
    inference(superposition,[],[f65,f270])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ v3_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | sK3(X0,X1,X2) = X0
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f318,plain,
    ( ~ spl8_43
    | spl8_38
    | spl8_31 ),
    inference(avatar_split_clause,[],[f241,f238,f262,f316])).

fof(f316,plain,
    ( spl8_43
  <=> ~ m1_subset_1(k2_orders_2(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_43])])).

fof(f262,plain,
    ( spl8_38
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f238,plain,
    ( spl8_31
  <=> ~ r2_hidden(k2_orders_2(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f241,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(k2_orders_2(sK0,sK2),sK1)
    | ~ spl8_31 ),
    inference(resolution,[],[f239,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t49_orders_2.p',t2_subset)).

fof(f239,plain,
    ( ~ r2_hidden(k2_orders_2(sK0,sK2),sK1)
    | ~ spl8_31 ),
    inference(avatar_component_clause,[],[f238])).

fof(f271,plain,
    ( spl8_40
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f198,f133,f112,f105,f98,f91,f84,f269])).

fof(f198,plain,
    ( k2_orders_2(sK0,sK2) = a_2_1_orders_2(sK0,sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f197,f85])).

fof(f197,plain,
    ( v2_struct_0(sK0)
    | k2_orders_2(sK0,sK2) = a_2_1_orders_2(sK0,sK2)
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f196,f113])).

fof(f196,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | k2_orders_2(sK0,sK2) = a_2_1_orders_2(sK0,sK2)
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f195,f106])).

fof(f195,plain,
    ( ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | k2_orders_2(sK0,sK2) = a_2_1_orders_2(sK0,sK2)
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f194,f99])).

fof(f194,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | k2_orders_2(sK0,sK2) = a_2_1_orders_2(sK0,sK2)
    | ~ spl8_2
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f191,f92])).

fof(f191,plain,
    ( ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | k2_orders_2(sK0,sK2) = a_2_1_orders_2(sK0,sK2)
    | ~ spl8_14 ),
    inference(resolution,[],[f57,f134])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t49_orders_2.p',d13_orders_2)).

fof(f264,plain,
    ( ~ spl8_37
    | spl8_38
    | spl8_25 ),
    inference(avatar_split_clause,[],[f219,f206,f262,f256])).

fof(f256,plain,
    ( spl8_37
  <=> ~ m1_subset_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f206,plain,
    ( spl8_25
  <=> ~ r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f219,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK2,sK1)
    | ~ spl8_25 ),
    inference(resolution,[],[f207,f69])).

fof(f207,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f206])).

fof(f251,plain,
    ( ~ spl8_33
    | spl8_34
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f166,f133,f249,f246])).

fof(f246,plain,
    ( spl8_33
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f249,plain,
    ( spl8_34
  <=> ! [X0] : ~ r2_hidden(X0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f166,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl8_14 ),
    inference(resolution,[],[f58,f134])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t49_orders_2.p',t5_subset)).

fof(f240,plain,
    ( ~ spl8_31
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f155,f140,f238])).

fof(f155,plain,
    ( ~ r2_hidden(k2_orders_2(sK0,sK2),sK1)
    | ~ spl8_16 ),
    inference(resolution,[],[f71,f141])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t49_orders_2.p',antisymmetry_r2_hidden)).

fof(f233,plain,
    ( spl8_28
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f153,f140,f231])).

fof(f231,plain,
    ( spl8_28
  <=> m1_subset_1(sK1,k2_orders_2(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f153,plain,
    ( m1_subset_1(sK1,k2_orders_2(sK0,sK2))
    | ~ spl8_16 ),
    inference(resolution,[],[f70,f141])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t49_orders_2.p',t1_subset)).

fof(f226,plain,
    ( ~ spl8_27
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f151,f140,f224])).

fof(f224,plain,
    ( spl8_27
  <=> ~ v1_xboole_0(k2_orders_2(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f151,plain,
    ( ~ v1_xboole_0(k2_orders_2(sK0,sK2))
    | ~ spl8_16 ),
    inference(resolution,[],[f66,f141])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t49_orders_2.p',t7_boole)).

fof(f208,plain,
    ( ~ spl8_25
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f154,f119,f206])).

fof(f154,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ spl8_10 ),
    inference(resolution,[],[f71,f120])).

fof(f187,plain,
    ( spl8_22
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f152,f119,f185])).

fof(f185,plain,
    ( spl8_22
  <=> m1_subset_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f152,plain,
    ( m1_subset_1(sK1,sK2)
    | ~ spl8_10 ),
    inference(resolution,[],[f70,f120])).

fof(f162,plain,
    ( ~ spl8_21
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f150,f119,f160])).

fof(f160,plain,
    ( spl8_21
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f150,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl8_10 ),
    inference(resolution,[],[f66,f120])).

fof(f149,plain,(
    spl8_18 ),
    inference(avatar_split_clause,[],[f74,f147])).

fof(f147,plain,
    ( spl8_18
  <=> l1_orders_2(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f74,plain,(
    l1_orders_2(sK7) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ? [X0] : l1_orders_2(X0) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t49_orders_2.p',existence_l1_orders_2)).

fof(f142,plain,(
    spl8_16 ),
    inference(avatar_split_clause,[],[f49,f140])).

fof(f49,plain,(
    r2_hidden(sK1,k2_orders_2(sK0,sK2)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r2_hidden(X1,k2_orders_2(X0,X2))
              & r2_hidden(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r2_hidden(X1,k2_orders_2(X0,X2))
              & r2_hidden(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( r2_hidden(X1,k2_orders_2(X0,X2))
                    & r2_hidden(X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( r2_hidden(X1,k2_orders_2(X0,X2))
                  & r2_hidden(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t49_orders_2.p',t49_orders_2)).

fof(f135,plain,(
    spl8_14 ),
    inference(avatar_split_clause,[],[f47,f133])).

fof(f47,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f128,plain,(
    spl8_12 ),
    inference(avatar_split_clause,[],[f50,f126])).

fof(f50,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f121,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f48,f119])).

fof(f48,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f114,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f55,f112])).

fof(f55,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f107,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f54,f105])).

fof(f54,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f100,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f53,f98])).

fof(f53,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f93,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f52,f91])).

fof(f52,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f86,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f51,f84])).

fof(f51,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
