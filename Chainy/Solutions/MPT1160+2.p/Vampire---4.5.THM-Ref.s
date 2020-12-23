%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1160+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:10 EST 2020

% Result     : Theorem 2.20s
% Output     : Refutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 173 expanded)
%              Number of leaves         :   24 (  74 expanded)
%              Depth                    :    8
%              Number of atoms          :  257 ( 649 expanded)
%              Number of equality atoms :   46 ( 106 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4072,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3149,f3154,f3159,f3164,f3169,f3174,f3184,f3323,f3355,f3545,f3890,f3970,f4071])).

fof(f4071,plain,
    ( spl89_20
    | ~ spl89_39 ),
    inference(avatar_contradiction_clause,[],[f4070])).

fof(f4070,plain,
    ( $false
    | spl89_20
    | ~ spl89_39 ),
    inference(subsumption_resolution,[],[f4043,f3354])).

fof(f3354,plain,
    ( k1_xboole_0 != k3_orders_2(sK0,k1_xboole_0,sK1)
    | spl89_20 ),
    inference(avatar_component_clause,[],[f3352])).

fof(f3352,plain,
    ( spl89_20
  <=> k1_xboole_0 = k3_orders_2(sK0,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl89_20])])).

fof(f4043,plain,
    ( k1_xboole_0 = k3_orders_2(sK0,k1_xboole_0,sK1)
    | ~ spl89_39 ),
    inference(backward_demodulation,[],[f3969,f4040])).

fof(f4040,plain,(
    ! [X0,X1] : k1_xboole_0 = k9_subset_1(X1,X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f4026,f2701])).

fof(f2701,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f4026,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k1_xboole_0) = k9_subset_1(X1,X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f2498,f2507])).

fof(f2507,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f1959])).

fof(f1959,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f496])).

fof(f496,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f2498,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f522])).

fof(f522,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f3969,plain,
    ( k3_orders_2(sK0,k1_xboole_0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k1_tarski(sK1)),k1_xboole_0)
    | ~ spl89_39 ),
    inference(avatar_component_clause,[],[f3967])).

fof(f3967,plain,
    ( spl89_39
  <=> k3_orders_2(sK0,k1_xboole_0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k1_tarski(sK1)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl89_39])])).

fof(f3970,plain,
    ( spl89_39
    | ~ spl89_6
    | spl89_29
    | ~ spl89_37 ),
    inference(avatar_split_clause,[],[f3956,f3887,f3542,f3171,f3967])).

fof(f3171,plain,
    ( spl89_6
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl89_6])])).

fof(f3542,plain,
    ( spl89_29
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl89_29])])).

fof(f3887,plain,
    ( spl89_37
  <=> k3_orders_2(sK0,k1_xboole_0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl89_37])])).

fof(f3956,plain,
    ( k3_orders_2(sK0,k1_xboole_0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k1_tarski(sK1)),k1_xboole_0)
    | ~ spl89_6
    | spl89_29
    | ~ spl89_37 ),
    inference(backward_demodulation,[],[f3889,f3926])).

fof(f3926,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)
    | ~ spl89_6
    | spl89_29 ),
    inference(unit_resulting_resolution,[],[f3544,f3173,f2532])).

fof(f2532,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k1_tarski(X1) = k6_domain_1(X0,X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1979])).

fof(f1979,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f1978])).

fof(f1978,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1889])).

fof(f1889,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f3173,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl89_6 ),
    inference(avatar_component_clause,[],[f3171])).

fof(f3544,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl89_29 ),
    inference(avatar_component_clause,[],[f3542])).

fof(f3889,plain,
    ( k3_orders_2(sK0,k1_xboole_0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k1_xboole_0)
    | ~ spl89_37 ),
    inference(avatar_component_clause,[],[f3887])).

fof(f3890,plain,
    ( spl89_37
    | spl89_1
    | ~ spl89_2
    | ~ spl89_3
    | ~ spl89_4
    | ~ spl89_5
    | ~ spl89_6 ),
    inference(avatar_split_clause,[],[f3287,f3171,f3166,f3161,f3156,f3151,f3146,f3887])).

fof(f3146,plain,
    ( spl89_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl89_1])])).

fof(f3151,plain,
    ( spl89_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl89_2])])).

fof(f3156,plain,
    ( spl89_3
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl89_3])])).

fof(f3161,plain,
    ( spl89_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl89_4])])).

fof(f3166,plain,
    ( spl89_5
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl89_5])])).

fof(f3287,plain,
    ( k3_orders_2(sK0,k1_xboole_0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k1_xboole_0)
    | spl89_1
    | ~ spl89_2
    | ~ spl89_3
    | ~ spl89_4
    | ~ spl89_5
    | ~ spl89_6 ),
    inference(unit_resulting_resolution,[],[f3148,f3153,f3158,f3163,f3168,f3173,f2498,f2469])).

fof(f2469,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | k3_orders_2(X0,X1,X2) = k9_subset_1(u1_struct_0(X0),k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)),X1)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f1931])).

fof(f1931,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k3_orders_2(X0,X1,X2) = k9_subset_1(u1_struct_0(X0),k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)),X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f1930])).

fof(f1930,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k3_orders_2(X0,X1,X2) = k9_subset_1(u1_struct_0(X0),k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)),X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1867])).

fof(f1867,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k3_orders_2(X0,X1,X2) = k9_subset_1(u1_struct_0(X0),k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_orders_2)).

fof(f3168,plain,
    ( l1_orders_2(sK0)
    | ~ spl89_5 ),
    inference(avatar_component_clause,[],[f3166])).

fof(f3163,plain,
    ( v5_orders_2(sK0)
    | ~ spl89_4 ),
    inference(avatar_component_clause,[],[f3161])).

fof(f3158,plain,
    ( v4_orders_2(sK0)
    | ~ spl89_3 ),
    inference(avatar_component_clause,[],[f3156])).

fof(f3153,plain,
    ( v3_orders_2(sK0)
    | ~ spl89_2 ),
    inference(avatar_component_clause,[],[f3151])).

fof(f3148,plain,
    ( ~ v2_struct_0(sK0)
    | spl89_1 ),
    inference(avatar_component_clause,[],[f3146])).

fof(f3545,plain,
    ( ~ spl89_29
    | spl89_1
    | ~ spl89_19 ),
    inference(avatar_split_clause,[],[f3538,f3320,f3146,f3542])).

fof(f3320,plain,
    ( spl89_19
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl89_19])])).

fof(f3538,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl89_1
    | ~ spl89_19 ),
    inference(backward_demodulation,[],[f3535,f3537])).

fof(f3537,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl89_19 ),
    inference(unit_resulting_resolution,[],[f3322,f2586])).

fof(f2586,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2036])).

fof(f2036,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1773])).

fof(f1773,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f3322,plain,
    ( l1_struct_0(sK0)
    | ~ spl89_19 ),
    inference(avatar_component_clause,[],[f3320])).

fof(f3535,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | spl89_1
    | ~ spl89_19 ),
    inference(unit_resulting_resolution,[],[f3148,f3322,f2584])).

fof(f2584,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2034])).

fof(f2034,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2033])).

fof(f2033,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1800])).

fof(f1800,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f3355,plain,
    ( ~ spl89_20
    | spl89_8
    | ~ spl89_19 ),
    inference(avatar_split_clause,[],[f3340,f3320,f3181,f3352])).

fof(f3181,plain,
    ( spl89_8
  <=> k1_xboole_0 = k3_orders_2(sK0,k1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl89_8])])).

fof(f3340,plain,
    ( k1_xboole_0 != k3_orders_2(sK0,k1_xboole_0,sK1)
    | spl89_8
    | ~ spl89_19 ),
    inference(backward_demodulation,[],[f3183,f3338])).

fof(f3338,plain,
    ( k1_xboole_0 = k1_struct_0(sK0)
    | ~ spl89_19 ),
    inference(unit_resulting_resolution,[],[f3322,f2476])).

fof(f2476,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k1_xboole_0 = k1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f1938])).

fof(f1938,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1772])).

fof(f1772,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k1_xboole_0 = k1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_struct_0)).

fof(f3183,plain,
    ( k1_xboole_0 != k3_orders_2(sK0,k1_struct_0(sK0),sK1)
    | spl89_8 ),
    inference(avatar_component_clause,[],[f3181])).

fof(f3323,plain,
    ( spl89_19
    | ~ spl89_5 ),
    inference(avatar_split_clause,[],[f3311,f3166,f3320])).

fof(f3311,plain,
    ( l1_struct_0(sK0)
    | ~ spl89_5 ),
    inference(unit_resulting_resolution,[],[f3168,f2593])).

fof(f2593,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2044])).

fof(f2044,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1879])).

fof(f1879,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f3184,plain,(
    ~ spl89_8 ),
    inference(avatar_split_clause,[],[f2467,f3181])).

fof(f2467,plain,(
    k1_xboole_0 != k3_orders_2(sK0,k1_struct_0(sK0),sK1) ),
    inference(cnf_transformation,[],[f2272])).

fof(f2272,plain,
    ( k1_xboole_0 != k3_orders_2(sK0,k1_struct_0(sK0),sK1)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f1927,f2271,f2270])).

fof(f2270,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k1_xboole_0 != k3_orders_2(sK0,k1_struct_0(sK0),X1)
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2271,plain,
    ( ? [X1] :
        ( k1_xboole_0 != k3_orders_2(sK0,k1_struct_0(sK0),X1)
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( k1_xboole_0 != k3_orders_2(sK0,k1_struct_0(sK0),sK1)
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f1927,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f1926])).

fof(f1926,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1918])).

fof(f1918,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k1_xboole_0 = k3_orders_2(X0,k1_struct_0(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f1917])).

fof(f1917,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k1_xboole_0 = k3_orders_2(X0,k1_struct_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_orders_2)).

fof(f3174,plain,(
    spl89_6 ),
    inference(avatar_split_clause,[],[f2466,f3171])).

fof(f2466,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f2272])).

fof(f3169,plain,(
    spl89_5 ),
    inference(avatar_split_clause,[],[f2465,f3166])).

fof(f2465,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f2272])).

fof(f3164,plain,(
    spl89_4 ),
    inference(avatar_split_clause,[],[f2464,f3161])).

fof(f2464,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f2272])).

fof(f3159,plain,(
    spl89_3 ),
    inference(avatar_split_clause,[],[f2463,f3156])).

fof(f2463,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f2272])).

fof(f3154,plain,(
    spl89_2 ),
    inference(avatar_split_clause,[],[f2462,f3151])).

fof(f2462,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f2272])).

fof(f3149,plain,(
    ~ spl89_1 ),
    inference(avatar_split_clause,[],[f2461,f3146])).

fof(f2461,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f2272])).
%------------------------------------------------------------------------------
