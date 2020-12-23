%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:47 EST 2020

% Result     : Theorem 1.72s
% Output     : Refutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :  196 ( 432 expanded)
%              Number of leaves         :   36 ( 155 expanded)
%              Depth                    :   35
%              Number of atoms          : 1100 (1952 expanded)
%              Number of equality atoms :   72 ( 176 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f773,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f100,f105,f110,f115,f120,f125,f134,f193,f198,f209,f277,f282,f329,f746,f758,f772])).

fof(f772,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_14
    | spl5_15
    | ~ spl5_16
    | spl5_30 ),
    inference(avatar_contradiction_clause,[],[f770])).

fof(f770,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_14
    | spl5_15
    | ~ spl5_16
    | spl5_30 ),
    inference(subsumption_resolution,[],[f324,f762])).

fof(f762,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0)))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_14
    | ~ spl5_16
    | spl5_30 ),
    inference(subsumption_resolution,[],[f413,f638])).

fof(f638,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | spl5_30 ),
    inference(avatar_component_clause,[],[f637])).

fof(f637,plain,
    ( spl5_30
  <=> v1_xboole_0(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f413,plain,
    ( ! [X0] :
        ( v1_xboole_0(k2_struct_0(sK0))
        | ~ r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0))) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_14
    | ~ spl5_16 ),
    inference(forward_demodulation,[],[f412,f276])).

fof(f276,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f274])).

fof(f274,plain,
    ( spl5_14
  <=> k2_struct_0(sK0) = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f412,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0)))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_14
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f411,f328])).

fof(f328,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f326])).

fof(f326,plain,
    ( spl5_16
  <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f411,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0)))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_14
    | ~ spl5_16 ),
    inference(forward_demodulation,[],[f410,f276])).

fof(f410,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0)))
        | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_14
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f409,f328])).

fof(f409,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0)))
        | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_14
    | ~ spl5_16 ),
    inference(forward_demodulation,[],[f408,f276])).

fof(f408,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0)))
        | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_14
    | ~ spl5_16 ),
    inference(forward_demodulation,[],[f407,f330])).

fof(f330,plain,
    ( k2_orders_2(sK0,k2_struct_0(sK0)) = a_2_1_orders_2(sK0,k2_struct_0(sK0))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_16 ),
    inference(unit_resulting_resolution,[],[f328,f159])).

fof(f159,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f158,f140])).

fof(f140,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f133,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f133,plain,
    ( l1_struct_0(sK0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl5_7
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f158,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f157,f99])).

fof(f99,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl5_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f157,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0)
        | v2_struct_0(sK0) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f156,f104])).

fof(f104,plain,
    ( v3_orders_2(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl5_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f156,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f155,f109])).

fof(f109,plain,
    ( v4_orders_2(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl5_3
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f155,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f154,f119])).

fof(f119,plain,
    ( l1_orders_2(sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl5_5
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f154,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_4 ),
    inference(resolution,[],[f67,f114])).

fof(f114,plain,
    ( v5_orders_2(sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl5_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_orders_2)).

fof(f407,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0)))
        | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f406,f276])).

fof(f406,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,u1_struct_0(sK0)))
        | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f405,f99])).

fof(f405,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,u1_struct_0(sK0)))
        | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0)
        | v1_xboole_0(u1_struct_0(sK0)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f404,f104])).

fof(f404,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,u1_struct_0(sK0)))
        | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0)
        | v1_xboole_0(u1_struct_0(sK0)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f403,f109])).

fof(f403,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,u1_struct_0(sK0)))
        | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0)
        | v1_xboole_0(u1_struct_0(sK0)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f402,f114])).

fof(f402,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,u1_struct_0(sK0)))
        | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0)
        | v1_xboole_0(u1_struct_0(sK0)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f401,f119])).

fof(f401,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,u1_struct_0(sK0)))
        | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0)
        | v1_xboole_0(u1_struct_0(sK0)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(duplicate_literal_removal,[],[f400])).

fof(f400,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,u1_struct_0(sK0)))
        | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ r2_hidden(X0,a_2_1_orders_2(sK0,u1_struct_0(sK0)))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(resolution,[],[f257,f173])).

fof(f173,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1)
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | v1_xboole_0(u1_struct_0(X1)) ) ),
    inference(resolution,[],[f80,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ! [X3] :
              ( ( ~ r2_orders_2(X1,X3,sK3(X1,X2,X3))
                & r2_hidden(sK3(X1,X2,X3),X2)
                & m1_subset_1(sK3(X1,X2,X3),u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( ! [X6] :
                ( r2_orders_2(X1,sK4(X0,X1,X2),X6)
                | ~ r2_hidden(X6,X2)
                | ~ m1_subset_1(X6,u1_struct_0(X1)) )
            & sK4(X0,X1,X2) = X0
            & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f50,f52,f51])).

fof(f51,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X3,X4)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,X3,sK3(X1,X2,X3))
        & r2_hidden(sK3(X1,X2,X3),X2)
        & m1_subset_1(sK3(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_orders_2(X1,X5,X6)
              | ~ r2_hidden(X6,X2)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_orders_2(X1,sK4(X0,X1,X2),X6)
            | ~ r2_hidden(X6,X2)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & sK4(X0,X1,X2) = X0
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r2_orders_2(X1,X3,X4)
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( ! [X6] :
                  ( r2_orders_2(X1,X5,X6)
                  | ~ r2_hidden(X6,X2)
                  | ~ m1_subset_1(X6,u1_struct_0(X1)) )
              & X0 = X5
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r2_orders_2(X1,X3,X4)
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( ! [X4] :
                  ( r2_orders_2(X1,X3,X4)
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

fof(f257,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK4(X0,sK0,X1),X1)
        | ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f256,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f256,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4(X0,sK0,X1),k2_struct_0(sK0))
        | ~ r2_hidden(sK4(X0,sK0,X1),X1)
        | ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f255,f140])).

fof(f255,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK4(X0,sK0,X1),X1)
        | ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(sK4(X0,sK0,X1),u1_struct_0(sK0)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f253,f119])).

fof(f253,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK4(X0,sK0,X1),X1)
        | ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(sK4(X0,sK0,X1),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(resolution,[],[f188,f94])).

fof(f94,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f88])).

fof(f88,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).

fof(f188,plain,
    ( ! [X2,X0,X1] :
        ( r2_orders_2(sK0,sK4(X2,sK0,X1),X0)
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f187,f140])).

fof(f187,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,sK4(X2,sK0,X1),X0) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f186,f86])).

fof(f186,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,sK4(X2,sK0,X1),X0) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f185,f99])).

fof(f185,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,sK4(X2,sK0,X1),X0)
        | v2_struct_0(sK0) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f184,f104])).

fof(f184,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,sK4(X2,sK0,X1),X0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f183,f109])).

fof(f183,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,sK4(X2,sK0,X1),X0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f182,f119])).

fof(f182,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | r2_orders_2(sK0,sK4(X2,sK0,X1),X0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_4 ),
    inference(resolution,[],[f82,f114])).

fof(f82,plain,(
    ! [X6,X2,X0,X1] :
      ( ~ v5_orders_2(X1)
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | r2_orders_2(X1,sK4(X0,X1,X2),X6)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f324,plain,
    ( r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0)))
    | spl5_15 ),
    inference(unit_resulting_resolution,[],[f281,f69])).

fof(f69,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK1(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f41,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f281,plain,
    ( ~ v1_xboole_0(k2_orders_2(sK0,k2_struct_0(sK0)))
    | spl5_15 ),
    inference(avatar_component_clause,[],[f279])).

fof(f279,plain,
    ( spl5_15
  <=> v1_xboole_0(k2_orders_2(sK0,k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f758,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_30
    | ~ spl5_34 ),
    inference(avatar_contradiction_clause,[],[f757])).

fof(f757,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_30
    | ~ spl5_34 ),
    inference(subsumption_resolution,[],[f756,f644])).

fof(f644,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_orders_2(sK0,k1_xboole_0))
    | ~ spl5_9
    | ~ spl5_30 ),
    inference(unit_resulting_resolution,[],[f197,f639,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f639,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f637])).

fof(f197,plain,
    ( m1_subset_1(k2_orders_2(sK0,k1_xboole_0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl5_9
  <=> m1_subset_1(k2_orders_2(sK0,k1_xboole_0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f756,plain,
    ( r2_hidden(sK2(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k1_xboole_0))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_34 ),
    inference(forward_demodulation,[],[f752,f192])).

fof(f192,plain,
    ( k2_orders_2(sK0,k1_xboole_0) = a_2_1_orders_2(sK0,k1_xboole_0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl5_8
  <=> k2_orders_2(sK0,k1_xboole_0) = a_2_1_orders_2(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f752,plain,
    ( r2_hidden(sK2(k2_orders_2(sK0,k2_struct_0(sK0))),a_2_1_orders_2(sK0,k1_xboole_0))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_34 ),
    inference(unit_resulting_resolution,[],[f60,f128,f745,f180])).

fof(f180,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k2_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | r2_hidden(sK3(sK0,X0,X1),X0)
        | r2_hidden(X1,a_2_1_orders_2(sK0,X0)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f179,f140])).

fof(f179,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k2_struct_0(sK0))
        | r2_hidden(sK3(sK0,X0,X1),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,a_2_1_orders_2(sK0,X0)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f178,f140])).

fof(f178,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(sK0,X0,X1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,a_2_1_orders_2(sK0,X0)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f177,f99])).

fof(f177,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(sK0,X0,X1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,a_2_1_orders_2(sK0,X0))
        | v2_struct_0(sK0) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f176,f104])).

fof(f176,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(sK0,X0,X1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,a_2_1_orders_2(sK0,X0))
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f175,f109])).

fof(f175,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(sK0,X0,X1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,a_2_1_orders_2(sK0,X0))
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f174,f119])).

fof(f174,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(sK0,X0,X1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | r2_hidden(X1,a_2_1_orders_2(sK0,X0))
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_4 ),
    inference(resolution,[],[f92,f114])).

fof(f92,plain,(
    ! [X2,X3,X1] :
      ( ~ v5_orders_2(X1)
      | r2_hidden(sK3(X1,X2,X3),X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | r2_hidden(X3,a_2_1_orders_2(X1,X2))
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | r2_hidden(sK3(X1,X2,X3),X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f745,plain,
    ( m1_subset_1(sK2(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f743])).

fof(f743,plain,
    ( spl5_34
  <=> m1_subset_1(sK2(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f128,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f71,f89])).

fof(f89,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f71,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f60,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f746,plain,
    ( spl5_34
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_11
    | ~ spl5_14
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f382,f326,f274,f206,f117,f112,f107,f102,f97,f743])).

fof(f206,plain,
    ( spl5_11
  <=> r2_hidden(sK2(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f382,plain,
    ( m1_subset_1(sK2(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_11
    | ~ spl5_14
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f381,f328])).

fof(f381,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | m1_subset_1(sK2(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_11
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f380,f276])).

fof(f380,plain,
    ( m1_subset_1(sK2(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_11
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f379,f276])).

fof(f379,plain,
    ( m1_subset_1(sK2(k2_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f378,f99])).

fof(f378,plain,
    ( m1_subset_1(sK2(k2_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f377,f104])).

fof(f377,plain,
    ( m1_subset_1(sK2(k2_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f376,f109])).

fof(f376,plain,
    ( m1_subset_1(sK2(k2_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f375,f114])).

fof(f375,plain,
    ( m1_subset_1(sK2(k2_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_5
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f373,f119])).

fof(f373,plain,
    ( m1_subset_1(sK2(k2_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_11 ),
    inference(resolution,[],[f212,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_orders_2)).

fof(f212,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_orders_2(sK0,k2_struct_0(sK0)),k1_zfmisc_1(X0))
        | m1_subset_1(sK2(k2_orders_2(sK0,k2_struct_0(sK0))),X0) )
    | ~ spl5_11 ),
    inference(resolution,[],[f208,f86])).

fof(f208,plain,
    ( r2_hidden(sK2(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0)))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f206])).

fof(f329,plain,
    ( spl5_16
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f142,f131,f326])).

fof(f142,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f139,f140])).

fof(f139,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f133,f62])).

fof(f62,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f282,plain,
    ( ~ spl5_15
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f211,f206,f279])).

fof(f211,plain,
    ( ~ v1_xboole_0(k2_orders_2(sK0,k2_struct_0(sK0)))
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f208,f68])).

fof(f68,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f277,plain,
    ( spl5_14
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f140,f131,f274])).

fof(f209,plain,
    ( spl5_11
    | spl5_6 ),
    inference(avatar_split_clause,[],[f135,f122,f206])).

fof(f122,plain,
    ( spl5_6
  <=> k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f135,plain,
    ( r2_hidden(sK2(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0)))
    | spl5_6 ),
    inference(unit_resulting_resolution,[],[f124,f70])).

fof(f70,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5,X6] :
                  ( ( r2_hidden(X6,X1)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X3,X4)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).

fof(f124,plain,
    ( k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0))
    | spl5_6 ),
    inference(avatar_component_clause,[],[f122])).

fof(f198,plain,
    ( spl5_9
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f162,f131,f117,f112,f107,f102,f97,f195])).

fof(f162,plain,
    ( m1_subset_1(k2_orders_2(sK0,k1_xboole_0),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f160,f140])).

fof(f160,plain,
    ( m1_subset_1(k2_orders_2(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f99,f104,f109,f114,f119,f60,f76])).

fof(f193,plain,
    ( spl5_8
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f153,f117,f112,f107,f102,f97,f190])).

fof(f153,plain,
    ( k2_orders_2(sK0,k1_xboole_0) = a_2_1_orders_2(sK0,k1_xboole_0)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f99,f104,f109,f114,f119,f60,f67])).

fof(f134,plain,
    ( spl5_7
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f126,f117,f131])).

fof(f126,plain,
    ( l1_struct_0(sK0)
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f119,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f125,plain,(
    ~ spl5_6 ),
    inference(avatar_split_clause,[],[f59,f122])).

fof(f59,plain,(
    k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f36])).

fof(f36,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0))
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_orders_2)).

fof(f120,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f58,f117])).

fof(f58,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f115,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f57,f112])).

fof(f57,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f110,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f56,f107])).

fof(f56,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f105,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f55,f102])).

fof(f55,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f100,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f54,f97])).

fof(f54,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:50:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (5021)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (5013)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (5007)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (5016)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.51  % (5014)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  % (5026)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.52  % (5030)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.52  % (5008)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (5020)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (5009)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.53  % (5015)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.53  % (5010)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.53  % (5011)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.54  % (5018)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.54  % (5018)Refutation not found, incomplete strategy% (5018)------------------------------
% 0.21/0.54  % (5018)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (5018)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (5018)Memory used [KB]: 10618
% 0.21/0.54  % (5018)Time elapsed: 0.126 s
% 0.21/0.54  % (5018)------------------------------
% 0.21/0.54  % (5018)------------------------------
% 0.21/0.54  % (5023)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.54  % (5025)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.54  % (5022)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.55  % (5031)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.55  % (5017)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.55  % (5012)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.55  % (5029)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.55  % (5019)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.57/0.56  % (5028)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.57/0.57  % (5027)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.57/0.57  % (5032)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.57/0.57  % (5024)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.72/0.58  % (5030)Refutation found. Thanks to Tanya!
% 1.72/0.58  % SZS status Theorem for theBenchmark
% 1.72/0.58  % SZS output start Proof for theBenchmark
% 1.72/0.58  fof(f773,plain,(
% 1.72/0.58    $false),
% 1.72/0.58    inference(avatar_sat_refutation,[],[f100,f105,f110,f115,f120,f125,f134,f193,f198,f209,f277,f282,f329,f746,f758,f772])).
% 1.72/0.58  fof(f772,plain,(
% 1.72/0.58    spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_14 | spl5_15 | ~spl5_16 | spl5_30),
% 1.72/0.58    inference(avatar_contradiction_clause,[],[f770])).
% 1.72/0.58  fof(f770,plain,(
% 1.72/0.58    $false | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_14 | spl5_15 | ~spl5_16 | spl5_30)),
% 1.72/0.58    inference(subsumption_resolution,[],[f324,f762])).
% 1.72/0.58  fof(f762,plain,(
% 1.72/0.58    ( ! [X0] : (~r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0)))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_14 | ~spl5_16 | spl5_30)),
% 1.72/0.58    inference(subsumption_resolution,[],[f413,f638])).
% 1.72/0.58  fof(f638,plain,(
% 1.72/0.58    ~v1_xboole_0(k2_struct_0(sK0)) | spl5_30),
% 1.72/0.58    inference(avatar_component_clause,[],[f637])).
% 1.72/0.58  fof(f637,plain,(
% 1.72/0.58    spl5_30 <=> v1_xboole_0(k2_struct_0(sK0))),
% 1.72/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 1.72/0.58  fof(f413,plain,(
% 1.72/0.58    ( ! [X0] : (v1_xboole_0(k2_struct_0(sK0)) | ~r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0)))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_14 | ~spl5_16)),
% 1.72/0.58    inference(forward_demodulation,[],[f412,f276])).
% 1.72/0.58  fof(f276,plain,(
% 1.72/0.58    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl5_14),
% 1.72/0.58    inference(avatar_component_clause,[],[f274])).
% 1.72/0.58  fof(f274,plain,(
% 1.72/0.58    spl5_14 <=> k2_struct_0(sK0) = u1_struct_0(sK0)),
% 1.72/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 1.72/0.58  fof(f412,plain,(
% 1.72/0.58    ( ! [X0] : (~r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0))) | v1_xboole_0(u1_struct_0(sK0))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_14 | ~spl5_16)),
% 1.72/0.58    inference(subsumption_resolution,[],[f411,f328])).
% 1.72/0.58  fof(f328,plain,(
% 1.72/0.58    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl5_16),
% 1.72/0.58    inference(avatar_component_clause,[],[f326])).
% 1.72/0.58  fof(f326,plain,(
% 1.72/0.58    spl5_16 <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.72/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 1.72/0.58  fof(f411,plain,(
% 1.72/0.58    ( ! [X0] : (~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0))) | v1_xboole_0(u1_struct_0(sK0))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_14 | ~spl5_16)),
% 1.72/0.58    inference(forward_demodulation,[],[f410,f276])).
% 1.72/0.58  fof(f410,plain,(
% 1.72/0.58    ( ! [X0] : (~r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0))) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(sK0))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_14 | ~spl5_16)),
% 1.72/0.58    inference(subsumption_resolution,[],[f409,f328])).
% 1.72/0.58  fof(f409,plain,(
% 1.72/0.58    ( ! [X0] : (~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0))) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(sK0))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_14 | ~spl5_16)),
% 1.72/0.58    inference(forward_demodulation,[],[f408,f276])).
% 1.72/0.58  fof(f408,plain,(
% 1.72/0.58    ( ! [X0] : (~r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0))) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(sK0))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_14 | ~spl5_16)),
% 1.72/0.58    inference(forward_demodulation,[],[f407,f330])).
% 1.72/0.58  fof(f330,plain,(
% 1.72/0.58    k2_orders_2(sK0,k2_struct_0(sK0)) = a_2_1_orders_2(sK0,k2_struct_0(sK0)) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_16)),
% 1.72/0.58    inference(unit_resulting_resolution,[],[f328,f159])).
% 1.72/0.58  fof(f159,plain,(
% 1.72/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0)) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7)),
% 1.72/0.58    inference(forward_demodulation,[],[f158,f140])).
% 1.72/0.58  fof(f140,plain,(
% 1.72/0.58    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl5_7),
% 1.72/0.58    inference(unit_resulting_resolution,[],[f133,f61])).
% 1.72/0.58  fof(f61,plain,(
% 1.72/0.58    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f21])).
% 1.72/0.58  fof(f21,plain,(
% 1.72/0.58    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.72/0.58    inference(ennf_transformation,[],[f9])).
% 1.72/0.58  fof(f9,axiom,(
% 1.72/0.58    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.72/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 1.72/0.58  fof(f133,plain,(
% 1.72/0.58    l1_struct_0(sK0) | ~spl5_7),
% 1.72/0.58    inference(avatar_component_clause,[],[f131])).
% 1.72/0.58  fof(f131,plain,(
% 1.72/0.58    spl5_7 <=> l1_struct_0(sK0)),
% 1.72/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.72/0.58  fof(f158,plain,(
% 1.72/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0)) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 1.72/0.58    inference(subsumption_resolution,[],[f157,f99])).
% 1.72/0.58  fof(f99,plain,(
% 1.72/0.58    ~v2_struct_0(sK0) | spl5_1),
% 1.72/0.58    inference(avatar_component_clause,[],[f97])).
% 1.72/0.58  fof(f97,plain,(
% 1.72/0.58    spl5_1 <=> v2_struct_0(sK0)),
% 1.72/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.72/0.58  fof(f157,plain,(
% 1.72/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) | v2_struct_0(sK0)) ) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 1.72/0.58    inference(subsumption_resolution,[],[f156,f104])).
% 1.72/0.58  fof(f104,plain,(
% 1.72/0.58    v3_orders_2(sK0) | ~spl5_2),
% 1.72/0.58    inference(avatar_component_clause,[],[f102])).
% 1.72/0.58  fof(f102,plain,(
% 1.72/0.58    spl5_2 <=> v3_orders_2(sK0)),
% 1.72/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.72/0.58  fof(f156,plain,(
% 1.72/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl5_3 | ~spl5_4 | ~spl5_5)),
% 1.72/0.58    inference(subsumption_resolution,[],[f155,f109])).
% 1.72/0.58  fof(f109,plain,(
% 1.72/0.58    v4_orders_2(sK0) | ~spl5_3),
% 1.72/0.58    inference(avatar_component_clause,[],[f107])).
% 1.72/0.58  fof(f107,plain,(
% 1.72/0.58    spl5_3 <=> v4_orders_2(sK0)),
% 1.72/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.72/0.58  fof(f155,plain,(
% 1.72/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl5_4 | ~spl5_5)),
% 1.72/0.58    inference(subsumption_resolution,[],[f154,f119])).
% 1.72/0.58  fof(f119,plain,(
% 1.72/0.58    l1_orders_2(sK0) | ~spl5_5),
% 1.72/0.58    inference(avatar_component_clause,[],[f117])).
% 1.72/0.58  fof(f117,plain,(
% 1.72/0.58    spl5_5 <=> l1_orders_2(sK0)),
% 1.72/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.72/0.58  fof(f154,plain,(
% 1.72/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl5_4),
% 1.72/0.58    inference(resolution,[],[f67,f114])).
% 1.72/0.58  fof(f114,plain,(
% 1.72/0.58    v5_orders_2(sK0) | ~spl5_4),
% 1.72/0.58    inference(avatar_component_clause,[],[f112])).
% 1.72/0.58  fof(f112,plain,(
% 1.72/0.58    spl5_4 <=> v5_orders_2(sK0)),
% 1.72/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.72/0.58  fof(f67,plain,(
% 1.72/0.58    ( ! [X0,X1] : (~v5_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f26])).
% 1.72/0.58  fof(f26,plain,(
% 1.72/0.58    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.72/0.58    inference(flattening,[],[f25])).
% 1.72/0.58  fof(f25,plain,(
% 1.72/0.58    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.72/0.58    inference(ennf_transformation,[],[f12])).
% 1.72/0.58  fof(f12,axiom,(
% 1.72/0.58    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)))),
% 1.72/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_orders_2)).
% 1.72/0.58  fof(f407,plain,(
% 1.72/0.58    ( ! [X0] : (~r2_hidden(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0))) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(sK0))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_14)),
% 1.72/0.58    inference(forward_demodulation,[],[f406,f276])).
% 1.72/0.58  fof(f406,plain,(
% 1.72/0.58    ( ! [X0] : (~r2_hidden(X0,a_2_1_orders_2(sK0,u1_struct_0(sK0))) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(sK0))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7)),
% 1.72/0.58    inference(subsumption_resolution,[],[f405,f99])).
% 1.72/0.58  fof(f405,plain,(
% 1.72/0.58    ( ! [X0] : (~r2_hidden(X0,a_2_1_orders_2(sK0,u1_struct_0(sK0))) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | v1_xboole_0(u1_struct_0(sK0))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7)),
% 1.72/0.58    inference(subsumption_resolution,[],[f404,f104])).
% 1.72/0.58  fof(f404,plain,(
% 1.72/0.58    ( ! [X0] : (~r2_hidden(X0,a_2_1_orders_2(sK0,u1_struct_0(sK0))) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | v1_xboole_0(u1_struct_0(sK0))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7)),
% 1.72/0.58    inference(subsumption_resolution,[],[f403,f109])).
% 1.72/0.58  fof(f403,plain,(
% 1.72/0.58    ( ! [X0] : (~r2_hidden(X0,a_2_1_orders_2(sK0,u1_struct_0(sK0))) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | v1_xboole_0(u1_struct_0(sK0))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7)),
% 1.72/0.58    inference(subsumption_resolution,[],[f402,f114])).
% 1.72/0.58  fof(f402,plain,(
% 1.72/0.58    ( ! [X0] : (~r2_hidden(X0,a_2_1_orders_2(sK0,u1_struct_0(sK0))) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | v1_xboole_0(u1_struct_0(sK0))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7)),
% 1.72/0.58    inference(subsumption_resolution,[],[f401,f119])).
% 1.72/0.58  fof(f401,plain,(
% 1.72/0.58    ( ! [X0] : (~r2_hidden(X0,a_2_1_orders_2(sK0,u1_struct_0(sK0))) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | v1_xboole_0(u1_struct_0(sK0))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7)),
% 1.72/0.58    inference(duplicate_literal_removal,[],[f400])).
% 1.72/0.58  fof(f400,plain,(
% 1.72/0.58    ( ! [X0] : (~r2_hidden(X0,a_2_1_orders_2(sK0,u1_struct_0(sK0))) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~r2_hidden(X0,a_2_1_orders_2(sK0,u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(sK0))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7)),
% 1.72/0.58    inference(resolution,[],[f257,f173])).
% 1.72/0.58  fof(f173,plain,(
% 1.72/0.58    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | v1_xboole_0(u1_struct_0(X1))) )),
% 1.72/0.58    inference(resolution,[],[f80,f72])).
% 1.72/0.58  fof(f72,plain,(
% 1.72/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f46])).
% 1.72/0.58  fof(f46,plain,(
% 1.72/0.58    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.72/0.58    inference(nnf_transformation,[],[f28])).
% 1.72/0.58  fof(f28,plain,(
% 1.72/0.58    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.72/0.58    inference(ennf_transformation,[],[f4])).
% 1.72/0.58  fof(f4,axiom,(
% 1.72/0.58    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.72/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.72/0.58  fof(f80,plain,(
% 1.72/0.58    ( ! [X2,X0,X1] : (m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f53])).
% 1.72/0.58  fof(f53,plain,(
% 1.72/0.58    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,X3,sK3(X1,X2,X3)) & r2_hidden(sK3(X1,X2,X3),X2) & m1_subset_1(sK3(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,sK4(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK4(X0,X1,X2) = X0 & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 1.72/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f50,f52,f51])).
% 1.72/0.58  fof(f51,plain,(
% 1.72/0.58    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,X3,sK3(X1,X2,X3)) & r2_hidden(sK3(X1,X2,X3),X2) & m1_subset_1(sK3(X1,X2,X3),u1_struct_0(X1))))),
% 1.72/0.58    introduced(choice_axiom,[])).
% 1.72/0.58  fof(f52,plain,(
% 1.72/0.58    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,sK4(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK4(X0,X1,X2) = X0 & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))))),
% 1.72/0.58    introduced(choice_axiom,[])).
% 1.72/0.58  fof(f50,plain,(
% 1.72/0.58    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 1.72/0.58    inference(rectify,[],[f49])).
% 1.72/0.58  fof(f49,plain,(
% 1.72/0.58    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 1.72/0.58    inference(nnf_transformation,[],[f32])).
% 1.72/0.58  fof(f32,plain,(
% 1.72/0.58    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 1.72/0.58    inference(flattening,[],[f31])).
% 1.72/0.58  fof(f31,plain,(
% 1.72/0.58    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 1.72/0.58    inference(ennf_transformation,[],[f15])).
% 1.72/0.58  fof(f15,axiom,(
% 1.72/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X3,X4))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 1.72/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).
% 1.72/0.58  fof(f257,plain,(
% 1.72/0.58    ( ! [X0,X1] : (~r2_hidden(sK4(X0,sK0,X1),X1) | ~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7)),
% 1.72/0.58    inference(subsumption_resolution,[],[f256,f86])).
% 1.72/0.58  fof(f86,plain,(
% 1.72/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f34])).
% 1.72/0.58  fof(f34,plain,(
% 1.72/0.58    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.72/0.58    inference(flattening,[],[f33])).
% 1.72/0.58  fof(f33,plain,(
% 1.72/0.58    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.72/0.58    inference(ennf_transformation,[],[f6])).
% 1.72/0.58  fof(f6,axiom,(
% 1.72/0.58    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.72/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 1.72/0.58  fof(f256,plain,(
% 1.72/0.58    ( ! [X0,X1] : (~m1_subset_1(sK4(X0,sK0,X1),k2_struct_0(sK0)) | ~r2_hidden(sK4(X0,sK0,X1),X1) | ~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7)),
% 1.72/0.58    inference(forward_demodulation,[],[f255,f140])).
% 1.72/0.58  fof(f255,plain,(
% 1.72/0.58    ( ! [X0,X1] : (~r2_hidden(sK4(X0,sK0,X1),X1) | ~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK4(X0,sK0,X1),u1_struct_0(sK0))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7)),
% 1.72/0.58    inference(subsumption_resolution,[],[f253,f119])).
% 1.72/0.58  fof(f253,plain,(
% 1.72/0.58    ( ! [X0,X1] : (~r2_hidden(sK4(X0,sK0,X1),X1) | ~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK4(X0,sK0,X1),u1_struct_0(sK0)) | ~l1_orders_2(sK0)) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7)),
% 1.72/0.58    inference(resolution,[],[f188,f94])).
% 1.72/0.58  fof(f94,plain,(
% 1.72/0.58    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.72/0.58    inference(duplicate_literal_removal,[],[f88])).
% 1.72/0.58  fof(f88,plain,(
% 1.72/0.58    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.72/0.58    inference(equality_resolution,[],[f65])).
% 1.72/0.58  fof(f65,plain,(
% 1.72/0.58    ( ! [X2,X0,X1] : (X1 != X2 | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f39])).
% 1.72/0.58  fof(f39,plain,(
% 1.72/0.58    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.72/0.58    inference(flattening,[],[f38])).
% 1.72/0.58  fof(f38,plain,(
% 1.72/0.58    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.72/0.58    inference(nnf_transformation,[],[f24])).
% 1.72/0.58  fof(f24,plain,(
% 1.72/0.58    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.72/0.58    inference(ennf_transformation,[],[f11])).
% 1.72/0.58  fof(f11,axiom,(
% 1.72/0.58    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 1.72/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).
% 1.72/0.58  fof(f188,plain,(
% 1.72/0.58    ( ! [X2,X0,X1] : (r2_orders_2(sK0,sK4(X2,sK0,X1),X0) | ~r2_hidden(X0,X1) | ~r2_hidden(X2,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7)),
% 1.72/0.58    inference(forward_demodulation,[],[f187,f140])).
% 1.72/0.58  fof(f187,plain,(
% 1.72/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X2,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,sK4(X2,sK0,X1),X0)) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 1.72/0.58    inference(subsumption_resolution,[],[f186,f86])).
% 1.72/0.58  fof(f186,plain,(
% 1.72/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X2,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,sK4(X2,sK0,X1),X0)) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 1.72/0.58    inference(subsumption_resolution,[],[f185,f99])).
% 1.72/0.58  fof(f185,plain,(
% 1.72/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X2,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,sK4(X2,sK0,X1),X0) | v2_struct_0(sK0)) ) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 1.72/0.58    inference(subsumption_resolution,[],[f184,f104])).
% 1.72/0.58  fof(f184,plain,(
% 1.72/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X2,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,sK4(X2,sK0,X1),X0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl5_3 | ~spl5_4 | ~spl5_5)),
% 1.72/0.58    inference(subsumption_resolution,[],[f183,f109])).
% 1.72/0.58  fof(f183,plain,(
% 1.72/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X2,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,sK4(X2,sK0,X1),X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl5_4 | ~spl5_5)),
% 1.72/0.58    inference(subsumption_resolution,[],[f182,f119])).
% 1.72/0.58  fof(f182,plain,(
% 1.72/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X2,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | r2_orders_2(sK0,sK4(X2,sK0,X1),X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl5_4),
% 1.72/0.58    inference(resolution,[],[f82,f114])).
% 1.72/0.58  fof(f82,plain,(
% 1.72/0.58    ( ! [X6,X2,X0,X1] : (~v5_orders_2(X1) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | r2_orders_2(X1,sK4(X0,X1,X2),X6) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f53])).
% 1.72/0.58  fof(f324,plain,(
% 1.72/0.58    r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0))) | spl5_15),
% 1.72/0.58    inference(unit_resulting_resolution,[],[f281,f69])).
% 1.72/0.58  fof(f69,plain,(
% 1.72/0.58    ( ! [X0] : (r2_hidden(sK1(X0),X0) | v1_xboole_0(X0)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f43])).
% 1.72/0.58  fof(f43,plain,(
% 1.72/0.58    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.72/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f41,f42])).
% 1.72/0.58  fof(f42,plain,(
% 1.72/0.58    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 1.72/0.58    introduced(choice_axiom,[])).
% 1.72/0.58  fof(f41,plain,(
% 1.72/0.58    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.72/0.58    inference(rectify,[],[f40])).
% 1.72/0.58  fof(f40,plain,(
% 1.72/0.58    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.72/0.58    inference(nnf_transformation,[],[f1])).
% 1.72/0.58  fof(f1,axiom,(
% 1.72/0.58    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.72/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.72/0.58  fof(f281,plain,(
% 1.72/0.58    ~v1_xboole_0(k2_orders_2(sK0,k2_struct_0(sK0))) | spl5_15),
% 1.72/0.58    inference(avatar_component_clause,[],[f279])).
% 1.72/0.58  fof(f279,plain,(
% 1.72/0.58    spl5_15 <=> v1_xboole_0(k2_orders_2(sK0,k2_struct_0(sK0)))),
% 1.72/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 1.72/0.58  fof(f758,plain,(
% 1.72/0.58    spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_30 | ~spl5_34),
% 1.72/0.58    inference(avatar_contradiction_clause,[],[f757])).
% 1.72/0.58  fof(f757,plain,(
% 1.72/0.58    $false | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_30 | ~spl5_34)),
% 1.72/0.58    inference(subsumption_resolution,[],[f756,f644])).
% 1.72/0.58  fof(f644,plain,(
% 1.72/0.58    ( ! [X0] : (~r2_hidden(X0,k2_orders_2(sK0,k1_xboole_0))) ) | (~spl5_9 | ~spl5_30)),
% 1.72/0.58    inference(unit_resulting_resolution,[],[f197,f639,f87])).
% 1.72/0.58  fof(f87,plain,(
% 1.72/0.58    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f35])).
% 1.72/0.58  fof(f35,plain,(
% 1.72/0.58    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.72/0.58    inference(ennf_transformation,[],[f7])).
% 1.72/0.58  fof(f7,axiom,(
% 1.72/0.58    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.72/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 1.72/0.58  fof(f639,plain,(
% 1.72/0.58    v1_xboole_0(k2_struct_0(sK0)) | ~spl5_30),
% 1.72/0.58    inference(avatar_component_clause,[],[f637])).
% 1.72/0.58  fof(f197,plain,(
% 1.72/0.58    m1_subset_1(k2_orders_2(sK0,k1_xboole_0),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl5_9),
% 1.72/0.58    inference(avatar_component_clause,[],[f195])).
% 1.72/0.58  fof(f195,plain,(
% 1.72/0.58    spl5_9 <=> m1_subset_1(k2_orders_2(sK0,k1_xboole_0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.72/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.72/0.58  fof(f756,plain,(
% 1.72/0.58    r2_hidden(sK2(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k1_xboole_0)) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_8 | ~spl5_34)),
% 1.72/0.58    inference(forward_demodulation,[],[f752,f192])).
% 1.72/0.58  fof(f192,plain,(
% 1.72/0.58    k2_orders_2(sK0,k1_xboole_0) = a_2_1_orders_2(sK0,k1_xboole_0) | ~spl5_8),
% 1.72/0.58    inference(avatar_component_clause,[],[f190])).
% 1.72/0.58  fof(f190,plain,(
% 1.72/0.58    spl5_8 <=> k2_orders_2(sK0,k1_xboole_0) = a_2_1_orders_2(sK0,k1_xboole_0)),
% 1.72/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.72/0.58  fof(f752,plain,(
% 1.72/0.58    r2_hidden(sK2(k2_orders_2(sK0,k2_struct_0(sK0))),a_2_1_orders_2(sK0,k1_xboole_0)) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_34)),
% 1.72/0.58    inference(unit_resulting_resolution,[],[f60,f128,f745,f180])).
% 1.72/0.58  fof(f180,plain,(
% 1.72/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k2_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | r2_hidden(sK3(sK0,X0,X1),X0) | r2_hidden(X1,a_2_1_orders_2(sK0,X0))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7)),
% 1.72/0.58    inference(forward_demodulation,[],[f179,f140])).
% 1.72/0.58  fof(f179,plain,(
% 1.72/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k2_struct_0(sK0)) | r2_hidden(sK3(sK0,X0,X1),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,a_2_1_orders_2(sK0,X0))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7)),
% 1.72/0.58    inference(forward_demodulation,[],[f178,f140])).
% 1.72/0.58  fof(f178,plain,(
% 1.72/0.58    ( ! [X0,X1] : (r2_hidden(sK3(sK0,X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,a_2_1_orders_2(sK0,X0))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 1.72/0.58    inference(subsumption_resolution,[],[f177,f99])).
% 1.72/0.58  fof(f177,plain,(
% 1.72/0.58    ( ! [X0,X1] : (r2_hidden(sK3(sK0,X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,a_2_1_orders_2(sK0,X0)) | v2_struct_0(sK0)) ) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 1.72/0.58    inference(subsumption_resolution,[],[f176,f104])).
% 1.72/0.58  fof(f176,plain,(
% 1.72/0.58    ( ! [X0,X1] : (r2_hidden(sK3(sK0,X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,a_2_1_orders_2(sK0,X0)) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl5_3 | ~spl5_4 | ~spl5_5)),
% 1.72/0.58    inference(subsumption_resolution,[],[f175,f109])).
% 1.72/0.58  fof(f175,plain,(
% 1.72/0.58    ( ! [X0,X1] : (r2_hidden(sK3(sK0,X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,a_2_1_orders_2(sK0,X0)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl5_4 | ~spl5_5)),
% 1.72/0.58    inference(subsumption_resolution,[],[f174,f119])).
% 1.72/0.58  fof(f174,plain,(
% 1.72/0.58    ( ! [X0,X1] : (r2_hidden(sK3(sK0,X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | r2_hidden(X1,a_2_1_orders_2(sK0,X0)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl5_4),
% 1.72/0.58    inference(resolution,[],[f92,f114])).
% 1.72/0.58  fof(f92,plain,(
% 1.72/0.58    ( ! [X2,X3,X1] : (~v5_orders_2(X1) | r2_hidden(sK3(X1,X2,X3),X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | r2_hidden(X3,a_2_1_orders_2(X1,X2)) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 1.72/0.58    inference(equality_resolution,[],[f84])).
% 1.72/0.58  fof(f84,plain,(
% 1.72/0.58    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_1_orders_2(X1,X2)) | r2_hidden(sK3(X1,X2,X3),X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f53])).
% 1.72/0.58  fof(f745,plain,(
% 1.72/0.58    m1_subset_1(sK2(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | ~spl5_34),
% 1.72/0.58    inference(avatar_component_clause,[],[f743])).
% 1.72/0.58  fof(f743,plain,(
% 1.72/0.58    spl5_34 <=> m1_subset_1(sK2(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))),
% 1.72/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).
% 1.72/0.58  fof(f128,plain,(
% 1.72/0.58    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.72/0.58    inference(superposition,[],[f71,f89])).
% 1.72/0.58  fof(f89,plain,(
% 1.72/0.58    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.72/0.58    inference(equality_resolution,[],[f79])).
% 1.72/0.58  fof(f79,plain,(
% 1.72/0.58    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 1.72/0.58    inference(cnf_transformation,[],[f48])).
% 1.72/0.58  fof(f48,plain,(
% 1.72/0.58    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.72/0.58    inference(flattening,[],[f47])).
% 1.72/0.58  fof(f47,plain,(
% 1.72/0.58    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.72/0.58    inference(nnf_transformation,[],[f2])).
% 1.72/0.58  fof(f2,axiom,(
% 1.72/0.58    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.72/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.72/0.58  fof(f71,plain,(
% 1.72/0.58    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 1.72/0.58    inference(cnf_transformation,[],[f3])).
% 1.72/0.58  fof(f3,axiom,(
% 1.72/0.58    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 1.72/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 1.72/0.58  fof(f60,plain,(
% 1.72/0.58    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.72/0.58    inference(cnf_transformation,[],[f5])).
% 1.72/0.58  fof(f5,axiom,(
% 1.72/0.58    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.72/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.72/0.58  fof(f746,plain,(
% 1.72/0.58    spl5_34 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_11 | ~spl5_14 | ~spl5_16),
% 1.72/0.58    inference(avatar_split_clause,[],[f382,f326,f274,f206,f117,f112,f107,f102,f97,f743])).
% 1.72/0.58  fof(f206,plain,(
% 1.72/0.58    spl5_11 <=> r2_hidden(sK2(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0)))),
% 1.72/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.72/0.58  fof(f382,plain,(
% 1.72/0.58    m1_subset_1(sK2(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_11 | ~spl5_14 | ~spl5_16)),
% 1.72/0.58    inference(subsumption_resolution,[],[f381,f328])).
% 1.72/0.58  fof(f381,plain,(
% 1.72/0.58    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(sK2(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_11 | ~spl5_14)),
% 1.72/0.58    inference(forward_demodulation,[],[f380,f276])).
% 1.72/0.58  fof(f380,plain,(
% 1.72/0.58    m1_subset_1(sK2(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_11 | ~spl5_14)),
% 1.72/0.58    inference(forward_demodulation,[],[f379,f276])).
% 1.72/0.58  fof(f379,plain,(
% 1.72/0.58    m1_subset_1(sK2(k2_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_11)),
% 1.72/0.58    inference(subsumption_resolution,[],[f378,f99])).
% 1.72/0.58  fof(f378,plain,(
% 1.72/0.58    m1_subset_1(sK2(k2_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_11)),
% 1.72/0.58    inference(subsumption_resolution,[],[f377,f104])).
% 1.72/0.58  fof(f377,plain,(
% 1.72/0.58    m1_subset_1(sK2(k2_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | (~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_11)),
% 1.72/0.58    inference(subsumption_resolution,[],[f376,f109])).
% 1.72/0.58  fof(f376,plain,(
% 1.72/0.58    m1_subset_1(sK2(k2_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | (~spl5_4 | ~spl5_5 | ~spl5_11)),
% 1.72/0.58    inference(subsumption_resolution,[],[f375,f114])).
% 1.72/0.58  fof(f375,plain,(
% 1.72/0.58    m1_subset_1(sK2(k2_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | (~spl5_5 | ~spl5_11)),
% 1.72/0.58    inference(subsumption_resolution,[],[f373,f119])).
% 1.72/0.58  fof(f373,plain,(
% 1.72/0.58    m1_subset_1(sK2(k2_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~spl5_11),
% 1.72/0.58    inference(resolution,[],[f212,f76])).
% 1.72/0.58  fof(f76,plain,(
% 1.72/0.58    ( ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f30])).
% 1.72/0.58  fof(f30,plain,(
% 1.72/0.58    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.72/0.58    inference(flattening,[],[f29])).
% 1.72/0.58  fof(f29,plain,(
% 1.72/0.58    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.72/0.58    inference(ennf_transformation,[],[f13])).
% 1.72/0.58  fof(f13,axiom,(
% 1.72/0.58    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.72/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_orders_2)).
% 1.72/0.58  fof(f212,plain,(
% 1.72/0.58    ( ! [X0] : (~m1_subset_1(k2_orders_2(sK0,k2_struct_0(sK0)),k1_zfmisc_1(X0)) | m1_subset_1(sK2(k2_orders_2(sK0,k2_struct_0(sK0))),X0)) ) | ~spl5_11),
% 1.72/0.58    inference(resolution,[],[f208,f86])).
% 1.72/0.58  fof(f208,plain,(
% 1.72/0.58    r2_hidden(sK2(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0))) | ~spl5_11),
% 1.72/0.58    inference(avatar_component_clause,[],[f206])).
% 1.72/0.58  fof(f329,plain,(
% 1.72/0.58    spl5_16 | ~spl5_7),
% 1.72/0.58    inference(avatar_split_clause,[],[f142,f131,f326])).
% 1.72/0.58  fof(f142,plain,(
% 1.72/0.58    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl5_7),
% 1.72/0.58    inference(forward_demodulation,[],[f139,f140])).
% 1.72/0.58  fof(f139,plain,(
% 1.72/0.58    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_7),
% 1.72/0.58    inference(unit_resulting_resolution,[],[f133,f62])).
% 1.72/0.58  fof(f62,plain,(
% 1.72/0.58    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f22])).
% 1.72/0.58  fof(f22,plain,(
% 1.72/0.58    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 1.72/0.58    inference(ennf_transformation,[],[f10])).
% 1.72/0.58  fof(f10,axiom,(
% 1.72/0.58    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.72/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).
% 1.72/0.58  fof(f282,plain,(
% 1.72/0.58    ~spl5_15 | ~spl5_11),
% 1.72/0.58    inference(avatar_split_clause,[],[f211,f206,f279])).
% 1.72/0.58  fof(f211,plain,(
% 1.72/0.58    ~v1_xboole_0(k2_orders_2(sK0,k2_struct_0(sK0))) | ~spl5_11),
% 1.72/0.58    inference(unit_resulting_resolution,[],[f208,f68])).
% 1.72/0.58  fof(f68,plain,(
% 1.72/0.58    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f43])).
% 1.72/0.58  fof(f277,plain,(
% 1.72/0.58    spl5_14 | ~spl5_7),
% 1.72/0.58    inference(avatar_split_clause,[],[f140,f131,f274])).
% 1.72/0.58  fof(f209,plain,(
% 1.72/0.58    spl5_11 | spl5_6),
% 1.72/0.58    inference(avatar_split_clause,[],[f135,f122,f206])).
% 1.72/0.58  fof(f122,plain,(
% 1.72/0.58    spl5_6 <=> k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0))),
% 1.72/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.72/0.58  fof(f135,plain,(
% 1.72/0.58    r2_hidden(sK2(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0))) | spl5_6),
% 1.72/0.58    inference(unit_resulting_resolution,[],[f124,f70])).
% 1.72/0.58  fof(f70,plain,(
% 1.72/0.58    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 1.72/0.58    inference(cnf_transformation,[],[f45])).
% 1.72/0.58  fof(f45,plain,(
% 1.72/0.58    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 1.72/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f44])).
% 1.72/0.58  fof(f44,plain,(
% 1.72/0.58    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 1.72/0.58    introduced(choice_axiom,[])).
% 1.72/0.58  fof(f27,plain,(
% 1.72/0.58    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.72/0.58    inference(ennf_transformation,[],[f18])).
% 1.72/0.58  fof(f18,plain,(
% 1.72/0.58    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.72/0.58    inference(pure_predicate_removal,[],[f8])).
% 1.72/0.58  fof(f8,axiom,(
% 1.72/0.58    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.72/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).
% 1.72/0.58  fof(f124,plain,(
% 1.72/0.58    k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0)) | spl5_6),
% 1.72/0.58    inference(avatar_component_clause,[],[f122])).
% 1.72/0.58  fof(f198,plain,(
% 1.72/0.58    spl5_9 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7),
% 1.72/0.58    inference(avatar_split_clause,[],[f162,f131,f117,f112,f107,f102,f97,f195])).
% 1.72/0.58  fof(f162,plain,(
% 1.72/0.58    m1_subset_1(k2_orders_2(sK0,k1_xboole_0),k1_zfmisc_1(k2_struct_0(sK0))) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7)),
% 1.72/0.58    inference(forward_demodulation,[],[f160,f140])).
% 1.72/0.58  fof(f160,plain,(
% 1.72/0.58    m1_subset_1(k2_orders_2(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 1.72/0.58    inference(unit_resulting_resolution,[],[f99,f104,f109,f114,f119,f60,f76])).
% 1.72/0.58  fof(f193,plain,(
% 1.72/0.58    spl5_8 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5),
% 1.72/0.58    inference(avatar_split_clause,[],[f153,f117,f112,f107,f102,f97,f190])).
% 1.72/0.58  fof(f153,plain,(
% 1.72/0.58    k2_orders_2(sK0,k1_xboole_0) = a_2_1_orders_2(sK0,k1_xboole_0) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 1.72/0.58    inference(unit_resulting_resolution,[],[f99,f104,f109,f114,f119,f60,f67])).
% 1.72/0.58  fof(f134,plain,(
% 1.72/0.58    spl5_7 | ~spl5_5),
% 1.72/0.58    inference(avatar_split_clause,[],[f126,f117,f131])).
% 1.72/0.59  fof(f126,plain,(
% 1.72/0.59    l1_struct_0(sK0) | ~spl5_5),
% 1.72/0.59    inference(unit_resulting_resolution,[],[f119,f63])).
% 1.72/0.59  fof(f63,plain,(
% 1.72/0.59    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 1.72/0.59    inference(cnf_transformation,[],[f23])).
% 1.72/0.59  fof(f23,plain,(
% 1.72/0.59    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 1.72/0.59    inference(ennf_transformation,[],[f14])).
% 1.72/0.59  fof(f14,axiom,(
% 1.72/0.59    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 1.72/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 1.72/0.59  fof(f125,plain,(
% 1.72/0.59    ~spl5_6),
% 1.72/0.59    inference(avatar_split_clause,[],[f59,f122])).
% 1.72/0.59  fof(f59,plain,(
% 1.72/0.59    k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0))),
% 1.72/0.59    inference(cnf_transformation,[],[f37])).
% 1.72/0.59  fof(f37,plain,(
% 1.72/0.59    k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0)) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 1.72/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f36])).
% 1.72/0.59  fof(f36,plain,(
% 1.72/0.59    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0)) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 1.72/0.59    introduced(choice_axiom,[])).
% 1.72/0.59  fof(f20,plain,(
% 1.72/0.59    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.72/0.59    inference(flattening,[],[f19])).
% 1.72/0.59  fof(f19,plain,(
% 1.72/0.59    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.72/0.59    inference(ennf_transformation,[],[f17])).
% 1.72/0.59  fof(f17,negated_conjecture,(
% 1.72/0.59    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 1.72/0.59    inference(negated_conjecture,[],[f16])).
% 1.72/0.59  fof(f16,conjecture,(
% 1.72/0.59    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 1.72/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_orders_2)).
% 1.72/0.59  fof(f120,plain,(
% 1.72/0.59    spl5_5),
% 1.72/0.59    inference(avatar_split_clause,[],[f58,f117])).
% 1.72/0.59  fof(f58,plain,(
% 1.72/0.59    l1_orders_2(sK0)),
% 1.72/0.59    inference(cnf_transformation,[],[f37])).
% 1.72/0.59  fof(f115,plain,(
% 1.72/0.59    spl5_4),
% 1.72/0.59    inference(avatar_split_clause,[],[f57,f112])).
% 1.72/0.59  fof(f57,plain,(
% 1.72/0.59    v5_orders_2(sK0)),
% 1.72/0.59    inference(cnf_transformation,[],[f37])).
% 1.72/0.59  fof(f110,plain,(
% 1.72/0.59    spl5_3),
% 1.72/0.59    inference(avatar_split_clause,[],[f56,f107])).
% 1.72/0.59  fof(f56,plain,(
% 1.72/0.59    v4_orders_2(sK0)),
% 1.72/0.59    inference(cnf_transformation,[],[f37])).
% 1.72/0.59  fof(f105,plain,(
% 1.72/0.59    spl5_2),
% 1.72/0.59    inference(avatar_split_clause,[],[f55,f102])).
% 1.72/0.59  fof(f55,plain,(
% 1.72/0.59    v3_orders_2(sK0)),
% 1.72/0.59    inference(cnf_transformation,[],[f37])).
% 1.72/0.59  fof(f100,plain,(
% 1.72/0.59    ~spl5_1),
% 1.72/0.59    inference(avatar_split_clause,[],[f54,f97])).
% 1.72/0.59  fof(f54,plain,(
% 1.72/0.59    ~v2_struct_0(sK0)),
% 1.72/0.59    inference(cnf_transformation,[],[f37])).
% 1.72/0.59  % SZS output end Proof for theBenchmark
% 1.72/0.59  % (5030)------------------------------
% 1.72/0.59  % (5030)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.59  % (5030)Termination reason: Refutation
% 1.72/0.59  
% 1.72/0.59  % (5030)Memory used [KB]: 11129
% 1.72/0.59  % (5030)Time elapsed: 0.170 s
% 1.72/0.59  % (5030)------------------------------
% 1.72/0.59  % (5030)------------------------------
% 1.72/0.59  % (5006)Success in time 0.214 s
%------------------------------------------------------------------------------
