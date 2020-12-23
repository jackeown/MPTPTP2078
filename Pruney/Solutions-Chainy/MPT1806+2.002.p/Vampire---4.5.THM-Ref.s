%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:40 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :  394 (1011 expanded)
%              Number of leaves         :   60 ( 412 expanded)
%              Depth                    :   26
%              Number of atoms          : 2220 (4261 expanded)
%              Number of equality atoms :  142 ( 301 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2324,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f105,f110,f115,f121,f156,f161,f170,f187,f201,f231,f260,f270,f299,f302,f321,f328,f336,f343,f352,f389,f433,f491,f554,f559,f655,f707,f807,f816,f820,f869,f925,f1072,f1165,f1186,f1192,f1833,f1923,f2004,f2017,f2020,f2027,f2035,f2100,f2125,f2323])).

fof(f2323,plain,
    ( ~ spl6_6
    | spl6_61
    | ~ spl6_96 ),
    inference(avatar_contradiction_clause,[],[f2322])).

fof(f2322,plain,
    ( $false
    | ~ spl6_6
    | spl6_61
    | ~ spl6_96 ),
    inference(subsumption_resolution,[],[f2225,f1184])).

fof(f1184,plain,
    ( ~ v5_pre_topc(k6_partfun1(u1_struct_0(sK0)),sK0,k8_tmap_1(sK0,sK1))
    | spl6_61 ),
    inference(avatar_component_clause,[],[f1183])).

fof(f1183,plain,
    ( spl6_61
  <=> v5_pre_topc(k6_partfun1(u1_struct_0(sK0)),sK0,k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).

fof(f2225,plain,
    ( v5_pre_topc(k6_partfun1(u1_struct_0(sK0)),sK0,k8_tmap_1(sK0,sK1))
    | ~ spl6_6
    | ~ spl6_96 ),
    inference(subsumption_resolution,[],[f2214,f155])).

fof(f155,plain,
    ( sP2(sK1,sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl6_6
  <=> sP2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f2214,plain,
    ( v5_pre_topc(k6_partfun1(u1_struct_0(sK0)),sK0,k8_tmap_1(sK0,sK1))
    | ~ sP2(sK1,sK0)
    | ~ spl6_96 ),
    inference(superposition,[],[f50,f2040])).

fof(f2040,plain,
    ( k6_partfun1(u1_struct_0(sK0)) = k9_tmap_1(sK0,sK1)
    | ~ spl6_96 ),
    inference(avatar_component_clause,[],[f2038])).

fof(f2038,plain,
    ( spl6_96
  <=> k6_partfun1(u1_struct_0(sK0)) = k9_tmap_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_96])])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1))
      | ~ sP2(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <~> ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1))
              & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              & v1_funct_1(k9_tmap_1(X0,X1)) ) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <~> ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1))
              & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              & v1_funct_1(k9_tmap_1(X0,X1)) ) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ( ( m1_pre_topc(X1,X0)
                & v1_tsep_1(X1,X0) )
            <=> ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
                & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1))
                & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
                & v1_funct_1(k9_tmap_1(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <=> ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1))
              & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              & v1_funct_1(k9_tmap_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t122_tmap_1)).

fof(f2125,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_16
    | ~ spl6_21
    | ~ spl6_23
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_38
    | ~ spl6_52
    | ~ spl6_61 ),
    inference(avatar_contradiction_clause,[],[f2124])).

fof(f2124,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_16
    | ~ spl6_21
    | ~ spl6_23
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_38
    | ~ spl6_52
    | ~ spl6_61 ),
    inference(subsumption_resolution,[],[f2123,f553])).

fof(f553,plain,
    ( v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f551])).

fof(f551,plain,
    ( spl6_26
  <=> v1_funct_1(k6_partfun1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f2123,plain,
    ( ~ v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_16
    | ~ spl6_21
    | ~ spl6_23
    | ~ spl6_25
    | ~ spl6_38
    | ~ spl6_52
    | ~ spl6_61 ),
    inference(forward_demodulation,[],[f2122,f351])).

fof(f351,plain,
    ( k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f349])).

fof(f349,plain,
    ( spl6_21
  <=> k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f2122,plain,
    ( ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_16
    | ~ spl6_21
    | ~ spl6_23
    | ~ spl6_25
    | ~ spl6_38
    | ~ spl6_52
    | ~ spl6_61 ),
    inference(subsumption_resolution,[],[f2121,f1071])).

fof(f1071,plain,
    ( v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl6_52 ),
    inference(avatar_component_clause,[],[f1069])).

fof(f1069,plain,
    ( spl6_52
  <=> v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f2121,plain,
    ( ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_16
    | ~ spl6_21
    | ~ spl6_23
    | ~ spl6_25
    | ~ spl6_38
    | ~ spl6_61 ),
    inference(forward_demodulation,[],[f2120,f351])).

fof(f2120,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_16
    | ~ spl6_21
    | ~ spl6_23
    | ~ spl6_25
    | ~ spl6_38
    | ~ spl6_61 ),
    inference(forward_demodulation,[],[f2119,f432])).

fof(f432,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f430])).

fof(f430,plain,
    ( spl6_23
  <=> u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f2119,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))))
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_16
    | ~ spl6_21
    | ~ spl6_25
    | ~ spl6_38
    | ~ spl6_61 ),
    inference(subsumption_resolution,[],[f2118,f1185])).

fof(f1185,plain,
    ( v5_pre_topc(k6_partfun1(u1_struct_0(sK0)),sK0,k8_tmap_1(sK0,sK1))
    | ~ spl6_61 ),
    inference(avatar_component_clause,[],[f1183])).

fof(f2118,plain,
    ( ~ v5_pre_topc(k6_partfun1(u1_struct_0(sK0)),sK0,k8_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))))
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_16
    | ~ spl6_21
    | ~ spl6_25
    | ~ spl6_38 ),
    inference(forward_demodulation,[],[f2117,f351])).

fof(f2117,plain,
    ( ~ v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k8_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))))
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_16
    | ~ spl6_25
    | ~ spl6_38 ),
    inference(forward_demodulation,[],[f2116,f654])).

fof(f654,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f652])).

fof(f652,plain,
    ( spl6_38
  <=> k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f2116,plain,
    ( ~ v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))))
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_16
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f2115,f150])).

fof(f150,plain,
    ( ~ v1_tsep_1(sK1,sK0)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl6_5
  <=> v1_tsep_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f2115,plain,
    ( ~ v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))))
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | v1_tsep_1(sK1,sK0)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_16
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f2114,f119])).

fof(f119,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl6_4
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f2114,plain,
    ( ~ v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))))
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ m1_pre_topc(sK1,sK0)
    | v1_tsep_1(sK1,sK0)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_16
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f2111,f548])).

fof(f548,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f547])).

fof(f547,plain,
    ( spl6_25
  <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f2111,plain,
    ( ~ v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))))
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_pre_topc(sK1,sK0)
    | v1_tsep_1(sK1,sK0)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_16 ),
    inference(superposition,[],[f434,f298])).

fof(f298,plain,
    ( u1_struct_0(sK1) = sK3(sK0,sK1)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f296])).

fof(f296,plain,
    ( spl6_16
  <=> u1_struct_0(sK1) = sK3(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f434,plain,
    ( ! [X0] :
        ( ~ v5_pre_topc(k7_tmap_1(sK0,sK3(sK0,X0)),sK0,k6_tmap_1(sK0,sK3(sK0,X0)))
        | ~ v1_funct_2(k7_tmap_1(sK0,sK3(sK0,X0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK3(sK0,X0))))
        | ~ v1_funct_1(k7_tmap_1(sK0,sK3(sK0,X0)))
        | ~ m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_pre_topc(X0,sK0)
        | v1_tsep_1(X0,sK0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(resolution,[],[f285,f146])).

fof(f146,plain,
    ( ! [X2] :
        ( ~ v3_pre_topc(sK3(sK0,X2),sK0)
        | ~ m1_pre_topc(X2,sK0)
        | v1_tsep_1(X2,sK0) )
    | ~ spl6_3 ),
    inference(resolution,[],[f114,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v3_pre_topc(sK3(X0,X1),X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tsep_1)).

fof(f114,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl6_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f285,plain,
    ( ! [X0] :
        ( v3_pre_topc(X0,sK0)
        | ~ v1_funct_1(k7_tmap_1(sK0,X0))
        | ~ v1_funct_2(k7_tmap_1(sK0,X0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X0)))
        | ~ v5_pre_topc(k7_tmap_1(sK0,X0),sK0,k6_tmap_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f284,f104])).

fof(f104,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl6_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f284,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_funct_1(k7_tmap_1(sK0,X0))
        | ~ v1_funct_2(k7_tmap_1(sK0,X0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X0)))
        | ~ v5_pre_topc(k7_tmap_1(sK0,X0),sK0,k6_tmap_1(sK0,X0))
        | v2_struct_0(sK0)
        | v3_pre_topc(X0,sK0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f283,f114])).

fof(f283,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(k7_tmap_1(sK0,X0))
        | ~ v1_funct_2(k7_tmap_1(sK0,X0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X0)))
        | ~ v5_pre_topc(k7_tmap_1(sK0,X0),sK0,k6_tmap_1(sK0,X0))
        | v2_struct_0(sK0)
        | v3_pre_topc(X0,sK0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f282,f109])).

fof(f109,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl6_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f282,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(k7_tmap_1(sK0,X0))
        | ~ v1_funct_2(k7_tmap_1(sK0,X0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X0)))
        | ~ v5_pre_topc(k7_tmap_1(sK0,X0),sK0,k6_tmap_1(sK0,X0))
        | v2_struct_0(sK0)
        | v3_pre_topc(X0,sK0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(duplicate_literal_removal,[],[f281])).

fof(f281,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_funct_1(k7_tmap_1(sK0,X0))
        | ~ v1_funct_2(k7_tmap_1(sK0,X0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X0)))
        | ~ v5_pre_topc(k7_tmap_1(sK0,X0),sK0,k6_tmap_1(sK0,X0))
        | v2_struct_0(sK0)
        | v3_pre_topc(X0,sK0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(resolution,[],[f275,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_funct_1(k7_tmap_1(X0,X1))
      | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
      | v2_struct_0(X0)
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_tmap_1)).

fof(f275,plain,
    ( ! [X12] :
        ( m1_subset_1(k7_tmap_1(sK0,X12),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X12)))))
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f143,f114])).

fof(f143,plain,
    ( ! [X12] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(k7_tmap_1(sK0,X12),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X12))))) )
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f132,f104])).

fof(f132,plain,
    ( ! [X12] :
        ( v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(k7_tmap_1(sK0,X12),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X12))))) )
    | ~ spl6_2 ),
    inference(resolution,[],[f109,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).

fof(f2100,plain,
    ( k9_tmap_1(sK0,sK1) != k9_tmap_1(sK0,sK0)
    | k6_partfun1(u1_struct_0(sK0)) != k9_tmap_1(sK0,sK0)
    | k6_partfun1(u1_struct_0(sK0)) = k9_tmap_1(sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2035,plain,
    ( k9_tmap_1(sK0,sK1) != k9_tmap_1(sK0,sK0)
    | k6_partfun1(u1_struct_0(sK0)) != k9_tmap_1(sK0,sK0)
    | v5_pre_topc(k9_tmap_1(sK0,sK1),sK0,k8_tmap_1(sK0,sK1))
    | ~ v5_pre_topc(k6_partfun1(u1_struct_0(sK0)),sK0,k8_tmap_1(sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2027,plain,
    ( ~ spl6_17
    | ~ spl6_41
    | ~ spl6_45
    | ~ spl6_93 ),
    inference(avatar_contradiction_clause,[],[f2026])).

fof(f2026,plain,
    ( $false
    | ~ spl6_17
    | ~ spl6_41
    | ~ spl6_45
    | ~ spl6_93 ),
    inference(subsumption_resolution,[],[f2025,f806])).

fof(f806,plain,
    ( v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl6_41 ),
    inference(avatar_component_clause,[],[f804])).

fof(f804,plain,
    ( spl6_41
  <=> v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f2025,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl6_17
    | ~ spl6_45
    | ~ spl6_93 ),
    inference(subsumption_resolution,[],[f2022,f307])).

fof(f307,plain,
    ( v1_funct_1(k9_tmap_1(sK0,sK1))
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f306])).

fof(f306,plain,
    ( spl6_17
  <=> v1_funct_1(k9_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f2022,plain,
    ( ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl6_45
    | ~ spl6_93 ),
    inference(resolution,[],[f1999,f924])).

fof(f924,plain,
    ( m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl6_45 ),
    inference(avatar_component_clause,[],[f922])).

fof(f922,plain,
    ( spl6_45
  <=> m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f1999,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) )
    | ~ spl6_93 ),
    inference(avatar_component_clause,[],[f1998])).

fof(f1998,plain,
    ( spl6_93
  <=> ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_93])])).

fof(f2020,plain,
    ( ~ spl6_3
    | spl6_95 ),
    inference(avatar_contradiction_clause,[],[f2019])).

fof(f2019,plain,
    ( $false
    | ~ spl6_3
    | spl6_95 ),
    inference(subsumption_resolution,[],[f2018,f114])).

fof(f2018,plain,
    ( ~ l1_pre_topc(sK0)
    | spl6_95 ),
    inference(resolution,[],[f2016,f59])).

fof(f59,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f2016,plain,
    ( ~ l1_struct_0(sK0)
    | spl6_95 ),
    inference(avatar_component_clause,[],[f2014])).

fof(f2014,plain,
    ( spl6_95
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_95])])).

fof(f2017,plain,
    ( ~ spl6_95
    | spl6_1
    | ~ spl6_37 ),
    inference(avatar_split_clause,[],[f2012,f639,f102,f2014])).

fof(f639,plain,
    ( spl6_37
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f2012,plain,
    ( ~ l1_struct_0(sK0)
    | spl6_1
    | ~ spl6_37 ),
    inference(subsumption_resolution,[],[f2011,f104])).

fof(f2011,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_37 ),
    inference(resolution,[],[f640,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f640,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f639])).

fof(f2004,plain,
    ( spl6_93
    | spl6_94
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_21
    | ~ spl6_23
    | ~ spl6_26
    | spl6_37
    | ~ spl6_39
    | ~ spl6_52
    | ~ spl6_59
    | ~ spl6_90 ),
    inference(avatar_split_clause,[],[f1991,f1920,f1162,f1069,f658,f639,f551,f430,f349,f117,f112,f107,f102,f2001,f1998])).

fof(f2001,plain,
    ( spl6_94
  <=> k6_partfun1(u1_struct_0(sK0)) = k9_tmap_1(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_94])])).

fof(f658,plain,
    ( spl6_39
  <=> u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f1162,plain,
    ( spl6_59
  <=> m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).

fof(f1920,plain,
    ( spl6_90
  <=> k9_tmap_1(sK0,sK1) = k9_tmap_1(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_90])])).

fof(f1991,plain,
    ( ! [X0] :
        ( k6_partfun1(u1_struct_0(sK0)) = k9_tmap_1(sK0,sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_21
    | ~ spl6_23
    | ~ spl6_26
    | spl6_37
    | ~ spl6_39
    | ~ spl6_52
    | ~ spl6_59
    | ~ spl6_90 ),
    inference(forward_demodulation,[],[f1990,f1922])).

fof(f1922,plain,
    ( k9_tmap_1(sK0,sK1) = k9_tmap_1(sK0,sK0)
    | ~ spl6_90 ),
    inference(avatar_component_clause,[],[f1920])).

fof(f1990,plain,
    ( ! [X0] :
        ( k6_partfun1(u1_struct_0(sK0)) = k9_tmap_1(sK0,sK1)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_21
    | ~ spl6_23
    | ~ spl6_26
    | spl6_37
    | ~ spl6_39
    | ~ spl6_52
    | ~ spl6_59 ),
    inference(subsumption_resolution,[],[f1130,f1164])).

fof(f1164,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl6_59 ),
    inference(avatar_component_clause,[],[f1162])).

fof(f1130,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | k6_partfun1(u1_struct_0(sK0)) = k9_tmap_1(sK0,sK1)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_21
    | ~ spl6_23
    | ~ spl6_26
    | spl6_37
    | ~ spl6_39
    | ~ spl6_52 ),
    inference(subsumption_resolution,[],[f1129,f641])).

fof(f641,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl6_37 ),
    inference(avatar_component_clause,[],[f639])).

fof(f1129,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | k6_partfun1(u1_struct_0(sK0)) = k9_tmap_1(sK0,sK1)
        | v1_xboole_0(u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_21
    | ~ spl6_23
    | ~ spl6_26
    | ~ spl6_39
    | ~ spl6_52 ),
    inference(subsumption_resolution,[],[f1128,f553])).

fof(f1128,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
        | k6_partfun1(u1_struct_0(sK0)) = k9_tmap_1(sK0,sK1)
        | v1_xboole_0(u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_21
    | ~ spl6_23
    | ~ spl6_39
    | ~ spl6_52 ),
    inference(subsumption_resolution,[],[f1127,f1071])).

fof(f1127,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
        | k6_partfun1(u1_struct_0(sK0)) = k9_tmap_1(sK0,sK1)
        | v1_xboole_0(u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_21
    | ~ spl6_23
    | ~ spl6_39 ),
    inference(duplicate_literal_removal,[],[f1126])).

fof(f1126,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
        | k6_partfun1(u1_struct_0(sK0)) = k9_tmap_1(sK0,sK1)
        | v1_xboole_0(u1_struct_0(sK0))
        | ~ v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
        | ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_21
    | ~ spl6_23
    | ~ spl6_39 ),
    inference(resolution,[],[f1121,f93])).

fof(f93,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | v1_xboole_0(X3)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X0,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => r1_funct_2(X0,X1,X2,X3,X4,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r1_funct_2)).

fof(f1121,plain,
    ( ! [X0] :
        ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),X0,k6_partfun1(u1_struct_0(sK0)))
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0)
        | k9_tmap_1(sK0,sK1) = X0 )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_21
    | ~ spl6_23
    | ~ spl6_39 ),
    inference(forward_demodulation,[],[f1120,f660])).

fof(f660,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))
    | ~ spl6_39 ),
    inference(avatar_component_clause,[],[f658])).

fof(f1120,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),X0,k6_partfun1(u1_struct_0(sK0)))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
        | k9_tmap_1(sK0,sK1) = X0 )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_21
    | ~ spl6_23
    | ~ spl6_39 ),
    inference(forward_demodulation,[],[f1119,f660])).

fof(f1119,plain,
    ( ! [X0] :
        ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),X0,k6_partfun1(u1_struct_0(sK0)))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
        | k9_tmap_1(sK0,sK1) = X0 )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_21
    | ~ spl6_23
    | ~ spl6_39 ),
    inference(forward_demodulation,[],[f497,f660])).

fof(f497,plain,
    ( ! [X0] :
        ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(sK0),X0,k6_partfun1(u1_struct_0(sK0)))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
        | k9_tmap_1(sK0,sK1) = X0 )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_21
    | ~ spl6_23 ),
    inference(forward_demodulation,[],[f496,f432])).

fof(f496,plain,
    ( ! [X0] :
        ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),X0,k6_partfun1(u1_struct_0(sK0)))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
        | k9_tmap_1(sK0,sK1) = X0 )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_21 ),
    inference(forward_demodulation,[],[f494,f351])).

fof(f494,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
        | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),X0,k7_tmap_1(sK0,u1_struct_0(sK1)))
        | k9_tmap_1(sK0,sK1) = X0 )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(resolution,[],[f347,f119])).

fof(f347,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0)))))
        | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0))),X1,k7_tmap_1(sK0,u1_struct_0(X0)))
        | k9_tmap_1(sK0,X0) = X1 )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(duplicate_literal_removal,[],[f346])).

fof(f346,plain,
    ( ! [X0,X1] :
        ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0))),X1,k7_tmap_1(sK0,u1_struct_0(X0)))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0)))))
        | ~ m1_pre_topc(X0,sK0)
        | k9_tmap_1(sK0,X0) = X1
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0)))))
        | ~ m1_pre_topc(X0,sK0)
        | k9_tmap_1(sK0,X0) = X1 )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(superposition,[],[f294,f291])).

fof(f291,plain,
    ( ! [X0,X1] :
        ( u1_struct_0(X0) = sK5(sK0,X0,X1)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0)))))
        | ~ m1_pre_topc(X0,sK0)
        | k9_tmap_1(sK0,X0) = X1 )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f133,f114])).

fof(f133,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0)))))
        | u1_struct_0(X0) = sK5(sK0,X0,X1)
        | k9_tmap_1(sK0,X0) = X1 )
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f122,f104])).

fof(f122,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0)))))
        | u1_struct_0(X0) = sK5(sK0,X0,X1)
        | k9_tmap_1(sK0,X0) = X1 )
    | ~ spl6_2 ),
    inference(resolution,[],[f109,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | u1_struct_0(X1) = sK5(X0,X1,X2)
      | k9_tmap_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
                & v1_funct_1(X2) )
             => ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( u1_struct_0(X1) = X3
                     => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_tmap_1)).

fof(f294,plain,
    ( ! [X2,X3] :
        ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X2)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK5(sK0,X2,X3))),X3,k7_tmap_1(sK0,sK5(sK0,X2,X3)))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X2)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X2)))))
        | ~ m1_pre_topc(X2,sK0)
        | k9_tmap_1(sK0,X2) = X3 )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f134,f114])).

fof(f134,plain,
    ( ! [X2,X3] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X2,sK0)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X2)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X2)))))
        | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X2)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK5(sK0,X2,X3))),X3,k7_tmap_1(sK0,sK5(sK0,X2,X3)))
        | k9_tmap_1(sK0,X2) = X3 )
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f123,f104])).

fof(f123,plain,
    ( ! [X2,X3] :
        ( v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X2,sK0)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X2)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X2)))))
        | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X2)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK5(sK0,X2,X3))),X3,k7_tmap_1(sK0,sK5(sK0,X2,X3)))
        | k9_tmap_1(sK0,X2) = X3 )
    | ~ spl6_2 ),
    inference(resolution,[],[f109,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK5(X0,X1,X2))),X2,k7_tmap_1(X0,sK5(X0,X1,X2)))
      | k9_tmap_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1923,plain,
    ( spl6_90
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_7
    | ~ spl6_17
    | ~ spl6_22
    | ~ spl6_24
    | ~ spl6_41
    | ~ spl6_44
    | ~ spl6_45
    | ~ spl6_88 ),
    inference(avatar_split_clause,[],[f1839,f1830,f922,f822,f804,f488,f386,f306,f158,f112,f107,f102,f1920])).

fof(f158,plain,
    ( spl6_7
  <=> m1_pre_topc(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f386,plain,
    ( spl6_22
  <=> k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f488,plain,
    ( spl6_24
  <=> u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f822,plain,
    ( spl6_44
  <=> u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f1830,plain,
    ( spl6_88
  <=> r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_88])])).

fof(f1839,plain,
    ( k9_tmap_1(sK0,sK1) = k9_tmap_1(sK0,sK0)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_7
    | ~ spl6_17
    | ~ spl6_22
    | ~ spl6_24
    | ~ spl6_41
    | ~ spl6_44
    | ~ spl6_45
    | ~ spl6_88 ),
    inference(subsumption_resolution,[],[f1838,f307])).

fof(f1838,plain,
    ( ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | k9_tmap_1(sK0,sK1) = k9_tmap_1(sK0,sK0)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_7
    | ~ spl6_22
    | ~ spl6_24
    | ~ spl6_41
    | ~ spl6_44
    | ~ spl6_45
    | ~ spl6_88 ),
    inference(subsumption_resolution,[],[f1837,f924])).

fof(f1837,plain,
    ( ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | k9_tmap_1(sK0,sK1) = k9_tmap_1(sK0,sK0)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_7
    | ~ spl6_22
    | ~ spl6_24
    | ~ spl6_41
    | ~ spl6_44
    | ~ spl6_88 ),
    inference(subsumption_resolution,[],[f1835,f806])).

fof(f1835,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | k9_tmap_1(sK0,sK1) = k9_tmap_1(sK0,sK0)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_7
    | ~ spl6_22
    | ~ spl6_24
    | ~ spl6_44
    | ~ spl6_88 ),
    inference(resolution,[],[f1832,f1136])).

fof(f1136,plain,
    ( ! [X1] :
        ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),X1,k6_partfun1(u1_struct_0(sK0)))
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X1)
        | k9_tmap_1(sK0,sK0) = X1 )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_7
    | ~ spl6_22
    | ~ spl6_24
    | ~ spl6_44 ),
    inference(forward_demodulation,[],[f1135,f824])).

fof(f824,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK0))
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f822])).

fof(f1135,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),X1,k6_partfun1(u1_struct_0(sK0)))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK0)))))
        | k9_tmap_1(sK0,sK0) = X1 )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_7
    | ~ spl6_22
    | ~ spl6_24
    | ~ spl6_44 ),
    inference(forward_demodulation,[],[f1134,f824])).

fof(f1134,plain,
    ( ! [X1] :
        ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),X1,k6_partfun1(u1_struct_0(sK0)))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK0)))))
        | k9_tmap_1(sK0,sK0) = X1 )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_7
    | ~ spl6_22
    | ~ spl6_24
    | ~ spl6_44 ),
    inference(forward_demodulation,[],[f1133,f824])).

fof(f1133,plain,
    ( ! [X1] :
        ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK0)),u1_struct_0(sK0),u1_struct_0(sK0),X1,k6_partfun1(u1_struct_0(sK0)))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK0)))))
        | k9_tmap_1(sK0,sK0) = X1 )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_7
    | ~ spl6_22
    | ~ spl6_24 ),
    inference(forward_demodulation,[],[f498,f490])).

fof(f490,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0)))
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f488])).

fof(f498,plain,
    ( ! [X1] :
        ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))),X1,k6_partfun1(u1_struct_0(sK0)))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK0)))))
        | k9_tmap_1(sK0,sK0) = X1 )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_7
    | ~ spl6_22 ),
    inference(forward_demodulation,[],[f495,f388])).

fof(f388,plain,
    ( k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK0))
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f386])).

fof(f495,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK0)))))
        | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))),X1,k7_tmap_1(sK0,u1_struct_0(sK0)))
        | k9_tmap_1(sK0,sK0) = X1 )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_7 ),
    inference(resolution,[],[f347,f160])).

fof(f160,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f158])).

fof(f1832,plain,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)))
    | ~ spl6_88 ),
    inference(avatar_component_clause,[],[f1830])).

fof(f1833,plain,
    ( spl6_88
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_20
    | ~ spl6_21
    | ~ spl6_25
    | ~ spl6_38
    | ~ spl6_39 ),
    inference(avatar_split_clause,[],[f1828,f658,f652,f547,f349,f318,f310,f306,f117,f112,f107,f102,f1830])).

fof(f310,plain,
    ( spl6_18
  <=> m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f318,plain,
    ( spl6_20
  <=> v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f1828,plain,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_20
    | ~ spl6_21
    | ~ spl6_25
    | ~ spl6_38
    | ~ spl6_39 ),
    inference(forward_demodulation,[],[f684,f660])).

fof(f684,plain,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k9_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_20
    | ~ spl6_21
    | ~ spl6_25
    | ~ spl6_38 ),
    inference(forward_demodulation,[],[f683,f351])).

fof(f683,plain,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_20
    | ~ spl6_25
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f682,f104])).

fof(f682,plain,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_20
    | ~ spl6_25
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f681,f548])).

fof(f681,plain,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_20
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f680,f311])).

fof(f311,plain,
    ( m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f310])).

fof(f680,plain,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_17
    | ~ spl6_20
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f679,f319])).

fof(f319,plain,
    ( v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f318])).

fof(f679,plain,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_17
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f678,f307])).

fof(f678,plain,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f677,f119])).

fof(f677,plain,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f676,f114])).

fof(f676,plain,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f667,f109])).

fof(f667,plain,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl6_38 ),
    inference(superposition,[],[f98,f654])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(k9_tmap_1(X0,X1))
      | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),X2,k7_tmap_1(X0,u1_struct_0(X1)))
      | k9_tmap_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X3
      | r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
      | k9_tmap_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1192,plain,
    ( ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_25
    | spl6_60 ),
    inference(avatar_contradiction_clause,[],[f1191])).

fof(f1191,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_25
    | spl6_60 ),
    inference(subsumption_resolution,[],[f1190,f151])).

fof(f151,plain,
    ( v1_tsep_1(sK1,sK0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f149])).

fof(f1190,plain,
    ( ~ v1_tsep_1(sK1,sK0)
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_25
    | spl6_60 ),
    inference(subsumption_resolution,[],[f1189,f119])).

fof(f1189,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ v1_tsep_1(sK1,sK0)
    | ~ spl6_3
    | ~ spl6_25
    | spl6_60 ),
    inference(subsumption_resolution,[],[f1187,f548])).

fof(f1187,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v1_tsep_1(sK1,sK0)
    | ~ spl6_3
    | spl6_60 ),
    inference(resolution,[],[f1181,f144])).

fof(f144,plain,
    ( ! [X0] :
        ( v3_pre_topc(u1_struct_0(X0),sK0)
        | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_tsep_1(X0,sK0) )
    | ~ spl6_3 ),
    inference(resolution,[],[f114,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(u1_struct_0(X1),X0)
      | ~ v1_tsep_1(X1,X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | v3_pre_topc(X2,X0)
      | ~ v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1181,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | spl6_60 ),
    inference(avatar_component_clause,[],[f1179])).

fof(f1179,plain,
    ( spl6_60
  <=> v3_pre_topc(u1_struct_0(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).

fof(f1186,plain,
    ( ~ spl6_60
    | spl6_61
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_21
    | ~ spl6_25
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f674,f652,f547,f349,f112,f107,f102,f1183,f1179])).

fof(f674,plain,
    ( v5_pre_topc(k6_partfun1(u1_struct_0(sK0)),sK0,k8_tmap_1(sK0,sK1))
    | ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_21
    | ~ spl6_25
    | ~ spl6_38 ),
    inference(forward_demodulation,[],[f673,f351])).

fof(f673,plain,
    ( v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k8_tmap_1(sK0,sK1))
    | ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_25
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f665,f548])).

fof(f665,plain,
    ( v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k8_tmap_1(sK0,sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_38 ),
    inference(superposition,[],[f265,f654])).

fof(f265,plain,
    ( ! [X7] :
        ( v5_pre_topc(k7_tmap_1(sK0,X7),sK0,k6_tmap_1(sK0,X7))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X7,sK0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f138,f114])).

fof(f138,plain,
    ( ! [X7] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
        | v5_pre_topc(k7_tmap_1(sK0,X7),sK0,k6_tmap_1(sK0,X7))
        | ~ v3_pre_topc(X7,sK0) )
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f127,f104])).

fof(f127,plain,
    ( ! [X7] :
        ( v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
        | v5_pre_topc(k7_tmap_1(sK0,X7),sK0,k6_tmap_1(sK0,X7))
        | ~ v3_pre_topc(X7,sK0) )
    | ~ spl6_2 ),
    inference(resolution,[],[f109,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1165,plain,
    ( spl6_59
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_21
    | ~ spl6_25
    | ~ spl6_38
    | ~ spl6_39 ),
    inference(avatar_split_clause,[],[f1160,f658,f652,f547,f349,f112,f107,f102,f1162])).

fof(f1160,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_21
    | ~ spl6_25
    | ~ spl6_38
    | ~ spl6_39 ),
    inference(forward_demodulation,[],[f672,f660])).

fof(f672,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_21
    | ~ spl6_25
    | ~ spl6_38 ),
    inference(forward_demodulation,[],[f671,f351])).

fof(f671,plain,
    ( m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_25
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f664,f548])).

fof(f664,plain,
    ( m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_38 ),
    inference(superposition,[],[f275,f654])).

fof(f1072,plain,
    ( spl6_52
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_21
    | ~ spl6_25
    | ~ spl6_38
    | ~ spl6_39 ),
    inference(avatar_split_clause,[],[f1067,f658,f652,f547,f349,f112,f107,f102,f1069])).

fof(f1067,plain,
    ( v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_21
    | ~ spl6_25
    | ~ spl6_38
    | ~ spl6_39 ),
    inference(forward_demodulation,[],[f689,f660])).

fof(f689,plain,
    ( v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_21
    | ~ spl6_25
    | ~ spl6_38 ),
    inference(forward_demodulation,[],[f688,f351])).

fof(f688,plain,
    ( v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_25
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f687,f104])).

fof(f687,plain,
    ( v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_25
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f686,f548])).

fof(f686,plain,
    ( v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f685,f114])).

fof(f685,plain,
    ( v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f668,f109])).

fof(f668,plain,
    ( v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl6_38 ),
    inference(superposition,[],[f91,f654])).

fof(f91,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f925,plain,
    ( spl6_45
    | ~ spl6_18
    | ~ spl6_39 ),
    inference(avatar_split_clause,[],[f709,f658,f310,f922])).

fof(f709,plain,
    ( m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl6_18
    | ~ spl6_39 ),
    inference(superposition,[],[f311,f660])).

fof(f869,plain,
    ( spl6_44
    | ~ spl6_24
    | ~ spl6_42 ),
    inference(avatar_split_clause,[],[f827,f809,f488,f822])).

fof(f809,plain,
    ( spl6_42
  <=> k8_tmap_1(sK0,sK0) = k6_tmap_1(sK0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f827,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK0))
    | ~ spl6_24
    | ~ spl6_42 ),
    inference(superposition,[],[f490,f811])).

fof(f811,plain,
    ( k8_tmap_1(sK0,sK0) = k6_tmap_1(sK0,u1_struct_0(sK0))
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f809])).

fof(f820,plain,
    ( ~ spl6_3
    | ~ spl6_7
    | spl6_43 ),
    inference(avatar_contradiction_clause,[],[f819])).

fof(f819,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_7
    | spl6_43 ),
    inference(subsumption_resolution,[],[f818,f114])).

fof(f818,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl6_7
    | spl6_43 ),
    inference(subsumption_resolution,[],[f817,f160])).

fof(f817,plain,
    ( ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | spl6_43 ),
    inference(resolution,[],[f815,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f815,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_43 ),
    inference(avatar_component_clause,[],[f813])).

fof(f813,plain,
    ( spl6_43
  <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f816,plain,
    ( spl6_42
    | ~ spl6_43
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f802,f267,f228,f184,f158,f112,f107,f102,f813,f809])).

fof(f184,plain,
    ( spl6_9
  <=> v1_pre_topc(k8_tmap_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f228,plain,
    ( spl6_11
  <=> v2_pre_topc(k8_tmap_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f267,plain,
    ( spl6_13
  <=> l1_pre_topc(k8_tmap_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f802,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | k8_tmap_1(sK0,sK0) = k6_tmap_1(sK0,u1_struct_0(sK0))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f801,f269])).

fof(f269,plain,
    ( l1_pre_topc(k8_tmap_1(sK0,sK0))
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f267])).

fof(f801,plain,
    ( ~ l1_pre_topc(k8_tmap_1(sK0,sK0))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | k8_tmap_1(sK0,sK0) = k6_tmap_1(sK0,u1_struct_0(sK0))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f194,f230])).

fof(f230,plain,
    ( v2_pre_topc(k8_tmap_1(sK0,sK0))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f228])).

fof(f194,plain,
    ( ~ v2_pre_topc(k8_tmap_1(sK0,sK0))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK0))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | k8_tmap_1(sK0,sK0) = k6_tmap_1(sK0,u1_struct_0(sK0))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f193,f104])).

fof(f193,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(k8_tmap_1(sK0,sK0))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK0))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | k8_tmap_1(sK0,sK0) = k6_tmap_1(sK0,u1_struct_0(sK0))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f192,f160])).

fof(f192,plain,
    ( ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(k8_tmap_1(sK0,sK0))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK0))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | k8_tmap_1(sK0,sK0) = k6_tmap_1(sK0,u1_struct_0(sK0))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f191,f114])).

fof(f191,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(k8_tmap_1(sK0,sK0))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK0))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | k8_tmap_1(sK0,sK0) = k6_tmap_1(sK0,u1_struct_0(sK0))
    | ~ spl6_2
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f188,f109])).

fof(f188,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(k8_tmap_1(sK0,sK0))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK0))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | k8_tmap_1(sK0,sK0) = k6_tmap_1(sK0,u1_struct_0(sK0))
    | ~ spl6_9 ),
    inference(resolution,[],[f186,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) ) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k6_tmap_1(X0,u1_struct_0(X1)) = X2
      | k8_tmap_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X3
      | k6_tmap_1(X0,X3) = X2
      | k8_tmap_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & v1_pre_topc(X2) )
             => ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( u1_struct_0(X1) = X3
                     => k6_tmap_1(X0,X3) = X2 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_tmap_1)).

fof(f186,plain,
    ( v1_pre_topc(k8_tmap_1(sK0,sK0))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f184])).

fof(f807,plain,
    ( spl6_41
    | ~ spl6_20
    | ~ spl6_39 ),
    inference(avatar_split_clause,[],[f710,f658,f318,f804])).

fof(f710,plain,
    ( v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl6_20
    | ~ spl6_39 ),
    inference(superposition,[],[f319,f660])).

fof(f707,plain,
    ( k8_tmap_1(sK0,sK1) != k6_tmap_1(sK0,u1_struct_0(sK1))
    | u1_struct_0(sK0) != u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f655,plain,
    ( spl6_38
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f650,f547,f257,f198,f167,f117,f112,f107,f102,f652])).

fof(f167,plain,
    ( spl6_8
  <=> v1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f198,plain,
    ( spl6_10
  <=> v2_pre_topc(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f257,plain,
    ( spl6_12
  <=> l1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f650,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f649,f548])).

fof(f649,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f648,f259])).

fof(f259,plain,
    ( l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f257])).

fof(f648,plain,
    ( ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f179,f200])).

fof(f200,plain,
    ( v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f198])).

fof(f179,plain,
    ( ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f178,f104])).

fof(f178,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f177,f119])).

fof(f177,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f176,f114])).

fof(f176,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl6_2
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f173,f109])).

fof(f173,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl6_8 ),
    inference(resolution,[],[f169,f96])).

fof(f169,plain,
    ( v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f167])).

fof(f559,plain,
    ( ~ spl6_3
    | ~ spl6_4
    | spl6_25 ),
    inference(avatar_contradiction_clause,[],[f558])).

fof(f558,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_4
    | spl6_25 ),
    inference(subsumption_resolution,[],[f557,f114])).

fof(f557,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl6_4
    | spl6_25 ),
    inference(subsumption_resolution,[],[f556,f119])).

fof(f556,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | spl6_25 ),
    inference(resolution,[],[f549,f61])).

fof(f549,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_25 ),
    inference(avatar_component_clause,[],[f547])).

fof(f554,plain,
    ( ~ spl6_25
    | spl6_26
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f372,f349,f112,f107,f102,f551,f547])).

fof(f372,plain,
    ( v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f371,f104])).

fof(f371,plain,
    ( v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f370,f114])).

fof(f370,plain,
    ( v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f358,f109])).

fof(f358,plain,
    ( v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl6_21 ),
    inference(superposition,[],[f90,f351])).

fof(f90,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_tmap_1(X0,X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f491,plain,
    ( spl6_24
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f354,f158,f112,f107,f102,f488])).

fof(f354,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_7 ),
    inference(resolution,[],[f236,f160])).

fof(f236,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0))) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f232,f114])).

fof(f232,plain,
    ( ! [X0] :
        ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0)))
        | ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(resolution,[],[f226,f61])).

fof(f226,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X5)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f136,f114])).

fof(f136,plain,
    ( ! [X5] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X5)) )
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f125,f104])).

fof(f125,plain,
    ( ! [X5] :
        ( v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X5)) )
    | ~ spl6_2 ),
    inference(resolution,[],[f109,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

fof(f433,plain,
    ( spl6_23
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f353,f117,f112,f107,f102,f430])).

fof(f353,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(resolution,[],[f236,f119])).

fof(f389,plain,
    ( spl6_22
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f345,f158,f112,f107,f102,f386])).

fof(f345,plain,
    ( k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK0))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_7 ),
    inference(resolution,[],[f218,f160])).

fof(f218,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(X0)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f214,f114])).

fof(f214,plain,
    ( ! [X0] :
        ( k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(resolution,[],[f202,f61])).

fof(f202,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | k7_tmap_1(sK0,X4) = k6_partfun1(u1_struct_0(sK0)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f135,f114])).

fof(f135,plain,
    ( ! [X4] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | k7_tmap_1(sK0,X4) = k6_partfun1(u1_struct_0(sK0)) )
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f124,f104])).

fof(f124,plain,
    ( ! [X4] :
        ( v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | k7_tmap_1(sK0,X4) = k6_partfun1(u1_struct_0(sK0)) )
    | ~ spl6_2 ),
    inference(resolution,[],[f109,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_tmap_1)).

fof(f352,plain,
    ( spl6_21
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f344,f117,f112,f107,f102,f349])).

fof(f344,plain,
    ( k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(resolution,[],[f218,f119])).

fof(f343,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_18 ),
    inference(avatar_contradiction_clause,[],[f342])).

fof(f342,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_18 ),
    inference(subsumption_resolution,[],[f341,f104])).

fof(f341,plain,
    ( v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_18 ),
    inference(subsumption_resolution,[],[f340,f119])).

fof(f340,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | spl6_18 ),
    inference(subsumption_resolution,[],[f339,f114])).

fof(f339,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl6_2
    | spl6_18 ),
    inference(subsumption_resolution,[],[f338,f109])).

fof(f338,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | spl6_18 ),
    inference(resolution,[],[f312,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_tmap_1)).

fof(f312,plain,
    ( ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | spl6_18 ),
    inference(avatar_component_clause,[],[f310])).

fof(f336,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_20 ),
    inference(avatar_contradiction_clause,[],[f335])).

fof(f335,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_20 ),
    inference(subsumption_resolution,[],[f334,f104])).

fof(f334,plain,
    ( v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_20 ),
    inference(subsumption_resolution,[],[f333,f119])).

fof(f333,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | spl6_20 ),
    inference(subsumption_resolution,[],[f332,f114])).

fof(f332,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl6_2
    | spl6_20 ),
    inference(subsumption_resolution,[],[f331,f109])).

fof(f331,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | spl6_20 ),
    inference(resolution,[],[f320,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f320,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | spl6_20 ),
    inference(avatar_component_clause,[],[f318])).

fof(f328,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_17 ),
    inference(avatar_contradiction_clause,[],[f327])).

fof(f327,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_17 ),
    inference(subsumption_resolution,[],[f326,f104])).

fof(f326,plain,
    ( v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_17 ),
    inference(subsumption_resolution,[],[f325,f119])).

fof(f325,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | spl6_17 ),
    inference(subsumption_resolution,[],[f324,f114])).

fof(f324,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl6_2
    | spl6_17 ),
    inference(subsumption_resolution,[],[f323,f109])).

fof(f323,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | spl6_17 ),
    inference(resolution,[],[f308,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k9_tmap_1(X0,X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f308,plain,
    ( ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | spl6_17 ),
    inference(avatar_component_clause,[],[f306])).

fof(f321,plain,
    ( ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | spl6_6 ),
    inference(avatar_split_clause,[],[f304,f153,f318,f314,f310,f306])).

fof(f314,plain,
    ( spl6_19
  <=> v5_pre_topc(k9_tmap_1(sK0,sK1),sK0,k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f304,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ v5_pre_topc(k9_tmap_1(sK0,sK1),sK0,k8_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | spl6_6 ),
    inference(resolution,[],[f154,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( sP2(X1,X0)
      | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1))
      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_1(k9_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f154,plain,
    ( ~ sP2(sK1,sK0)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f153])).

fof(f302,plain,
    ( ~ spl6_5
    | ~ spl6_6 ),
    inference(avatar_contradiction_clause,[],[f301])).

fof(f301,plain,
    ( $false
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f300,f151])).

fof(f300,plain,
    ( ~ v1_tsep_1(sK1,sK0)
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f100,f155])).

fof(f100,plain,
    ( ~ sP2(sK1,sK0)
    | ~ v1_tsep_1(sK1,sK0) ),
    inference(global_subsumption,[],[f99,f52])).

fof(f52,plain,
    ( ~ sP2(sK1,sK0)
    | ~ v1_tsep_1(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f99,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(global_subsumption,[],[f55])).

fof(f55,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f299,plain,
    ( spl6_16
    | ~ spl6_3
    | ~ spl6_4
    | spl6_5 ),
    inference(avatar_split_clause,[],[f196,f149,f117,f112,f296])).

fof(f196,plain,
    ( u1_struct_0(sK1) = sK3(sK0,sK1)
    | ~ spl6_3
    | ~ spl6_4
    | spl6_5 ),
    inference(subsumption_resolution,[],[f195,f119])).

fof(f195,plain,
    ( u1_struct_0(sK1) = sK3(sK0,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl6_3
    | spl6_5 ),
    inference(resolution,[],[f145,f150])).

fof(f145,plain,
    ( ! [X1] :
        ( v1_tsep_1(X1,sK0)
        | u1_struct_0(X1) = sK3(sK0,X1)
        | ~ m1_pre_topc(X1,sK0) )
    | ~ spl6_3 ),
    inference(resolution,[],[f114,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | u1_struct_0(X1) = sK3(X0,X1)
      | v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f270,plain,
    ( spl6_13
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f182,f158,f112,f107,f102,f267])).

fof(f182,plain,
    ( l1_pre_topc(k8_tmap_1(sK0,sK0))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_7 ),
    inference(resolution,[],[f180,f160])).

fof(f180,plain,
    ( ! [X11] :
        ( ~ m1_pre_topc(X11,sK0)
        | l1_pre_topc(k8_tmap_1(sK0,X11)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f142,f114])).

fof(f142,plain,
    ( ! [X11] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X11,sK0)
        | l1_pre_topc(k8_tmap_1(sK0,X11)) )
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f131,f104])).

fof(f131,plain,
    ( ! [X11] :
        ( v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X11,sK0)
        | l1_pre_topc(k8_tmap_1(sK0,X11)) )
    | ~ spl6_2 ),
    inference(resolution,[],[f109,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(k8_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_tmap_1)).

fof(f260,plain,
    ( spl6_12
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f181,f117,f112,f107,f102,f257])).

fof(f181,plain,
    ( l1_pre_topc(k8_tmap_1(sK0,sK1))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(resolution,[],[f180,f119])).

fof(f231,plain,
    ( spl6_11
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f172,f158,f112,f107,f102,f228])).

fof(f172,plain,
    ( v2_pre_topc(k8_tmap_1(sK0,sK0))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_7 ),
    inference(resolution,[],[f165,f160])).

fof(f165,plain,
    ( ! [X10] :
        ( ~ m1_pre_topc(X10,sK0)
        | v2_pre_topc(k8_tmap_1(sK0,X10)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f141,f114])).

fof(f141,plain,
    ( ! [X10] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X10,sK0)
        | v2_pre_topc(k8_tmap_1(sK0,X10)) )
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f130,f104])).

fof(f130,plain,
    ( ! [X10] :
        ( v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X10,sK0)
        | v2_pre_topc(k8_tmap_1(sK0,X10)) )
    | ~ spl6_2 ),
    inference(resolution,[],[f109,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(k8_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f201,plain,
    ( spl6_10
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f171,f117,f112,f107,f102,f198])).

fof(f171,plain,
    ( v2_pre_topc(k8_tmap_1(sK0,sK1))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(resolution,[],[f165,f119])).

fof(f187,plain,
    ( spl6_9
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f164,f158,f112,f107,f102,f184])).

fof(f164,plain,
    ( v1_pre_topc(k8_tmap_1(sK0,sK0))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_7 ),
    inference(resolution,[],[f162,f160])).

fof(f162,plain,
    ( ! [X9] :
        ( ~ m1_pre_topc(X9,sK0)
        | v1_pre_topc(k8_tmap_1(sK0,X9)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f140,f114])).

fof(f140,plain,
    ( ! [X9] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X9,sK0)
        | v1_pre_topc(k8_tmap_1(sK0,X9)) )
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f129,f104])).

fof(f129,plain,
    ( ! [X9] :
        ( v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X9,sK0)
        | v1_pre_topc(k8_tmap_1(sK0,X9)) )
    | ~ spl6_2 ),
    inference(resolution,[],[f109,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v1_pre_topc(k8_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f170,plain,
    ( spl6_8
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f163,f117,f112,f107,f102,f167])).

fof(f163,plain,
    ( v1_pre_topc(k8_tmap_1(sK0,sK1))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(resolution,[],[f162,f119])).

fof(f161,plain,
    ( spl6_7
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f147,f112,f158])).

fof(f147,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ spl6_3 ),
    inference(resolution,[],[f114,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f156,plain,
    ( spl6_5
    | spl6_6 ),
    inference(avatar_split_clause,[],[f53,f153,f149])).

fof(f53,plain,
    ( sP2(sK1,sK0)
    | v1_tsep_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f121,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f99,f117])).

fof(f115,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f58,f112])).

fof(f58,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f110,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f57,f107])).

fof(f57,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f105,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f56,f102])).

fof(f56,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:09:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.45  % (9419)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.46  % (9436)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.46  % (9429)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.46  % (9419)Refutation not found, incomplete strategy% (9419)------------------------------
% 0.20/0.46  % (9419)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (9419)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (9419)Memory used [KB]: 10618
% 0.20/0.46  % (9419)Time elapsed: 0.050 s
% 0.20/0.46  % (9419)------------------------------
% 0.20/0.46  % (9419)------------------------------
% 0.20/0.47  % (9426)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.47  % (9423)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.48  % (9421)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  % (9422)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.49  % (9432)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  % (9424)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.49  % (9420)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.49  % (9438)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.50  % (9435)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.50  % (9430)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (9431)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.50  % (9434)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.50  % (9425)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.50  % (9437)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.51  % (9428)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.51  % (9433)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.51  % (9429)Refutation not found, incomplete strategy% (9429)------------------------------
% 0.20/0.51  % (9429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (9429)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (9429)Memory used [KB]: 11641
% 0.20/0.51  % (9429)Time elapsed: 0.104 s
% 0.20/0.51  % (9429)------------------------------
% 0.20/0.51  % (9429)------------------------------
% 0.20/0.51  % (9418)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (9430)Refutation not found, incomplete strategy% (9430)------------------------------
% 0.20/0.51  % (9430)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (9430)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (9430)Memory used [KB]: 6140
% 0.20/0.51  % (9430)Time elapsed: 0.109 s
% 0.20/0.51  % (9430)------------------------------
% 0.20/0.51  % (9430)------------------------------
% 0.20/0.51  % (9418)Refutation not found, incomplete strategy% (9418)------------------------------
% 0.20/0.51  % (9418)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (9418)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (9418)Memory used [KB]: 6268
% 0.20/0.51  % (9418)Time elapsed: 0.100 s
% 0.20/0.51  % (9418)------------------------------
% 0.20/0.51  % (9418)------------------------------
% 0.20/0.51  % (9438)Refutation not found, incomplete strategy% (9438)------------------------------
% 0.20/0.51  % (9438)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (9438)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (9438)Memory used [KB]: 10618
% 0.20/0.51  % (9438)Time elapsed: 0.100 s
% 0.20/0.51  % (9438)------------------------------
% 0.20/0.51  % (9438)------------------------------
% 0.20/0.52  % (9427)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 1.37/0.53  % (9431)Refutation not found, incomplete strategy% (9431)------------------------------
% 1.37/0.53  % (9431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.53  % (9431)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.53  
% 1.37/0.53  % (9431)Memory used [KB]: 1791
% 1.37/0.53  % (9431)Time elapsed: 0.093 s
% 1.37/0.53  % (9431)------------------------------
% 1.37/0.53  % (9431)------------------------------
% 1.37/0.53  % (9428)Refutation not found, incomplete strategy% (9428)------------------------------
% 1.37/0.53  % (9428)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.53  % (9428)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.53  
% 1.37/0.53  % (9428)Memory used [KB]: 6396
% 1.37/0.53  % (9428)Time elapsed: 0.106 s
% 1.37/0.53  % (9428)------------------------------
% 1.37/0.53  % (9428)------------------------------
% 1.53/0.54  % (9421)Refutation found. Thanks to Tanya!
% 1.53/0.54  % SZS status Theorem for theBenchmark
% 1.53/0.54  % SZS output start Proof for theBenchmark
% 1.53/0.54  fof(f2324,plain,(
% 1.53/0.54    $false),
% 1.53/0.54    inference(avatar_sat_refutation,[],[f105,f110,f115,f121,f156,f161,f170,f187,f201,f231,f260,f270,f299,f302,f321,f328,f336,f343,f352,f389,f433,f491,f554,f559,f655,f707,f807,f816,f820,f869,f925,f1072,f1165,f1186,f1192,f1833,f1923,f2004,f2017,f2020,f2027,f2035,f2100,f2125,f2323])).
% 1.53/0.54  fof(f2323,plain,(
% 1.53/0.54    ~spl6_6 | spl6_61 | ~spl6_96),
% 1.53/0.54    inference(avatar_contradiction_clause,[],[f2322])).
% 1.53/0.54  fof(f2322,plain,(
% 1.53/0.54    $false | (~spl6_6 | spl6_61 | ~spl6_96)),
% 1.53/0.54    inference(subsumption_resolution,[],[f2225,f1184])).
% 1.53/0.54  fof(f1184,plain,(
% 1.53/0.54    ~v5_pre_topc(k6_partfun1(u1_struct_0(sK0)),sK0,k8_tmap_1(sK0,sK1)) | spl6_61),
% 1.53/0.54    inference(avatar_component_clause,[],[f1183])).
% 1.53/0.54  fof(f1183,plain,(
% 1.53/0.54    spl6_61 <=> v5_pre_topc(k6_partfun1(u1_struct_0(sK0)),sK0,k8_tmap_1(sK0,sK1))),
% 1.53/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).
% 1.53/0.54  fof(f2225,plain,(
% 1.53/0.54    v5_pre_topc(k6_partfun1(u1_struct_0(sK0)),sK0,k8_tmap_1(sK0,sK1)) | (~spl6_6 | ~spl6_96)),
% 1.53/0.54    inference(subsumption_resolution,[],[f2214,f155])).
% 1.53/0.54  fof(f155,plain,(
% 1.53/0.54    sP2(sK1,sK0) | ~spl6_6),
% 1.53/0.54    inference(avatar_component_clause,[],[f153])).
% 1.53/0.54  fof(f153,plain,(
% 1.53/0.54    spl6_6 <=> sP2(sK1,sK0)),
% 1.53/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.53/0.54  fof(f2214,plain,(
% 1.53/0.54    v5_pre_topc(k6_partfun1(u1_struct_0(sK0)),sK0,k8_tmap_1(sK0,sK1)) | ~sP2(sK1,sK0) | ~spl6_96),
% 1.53/0.54    inference(superposition,[],[f50,f2040])).
% 1.53/0.54  fof(f2040,plain,(
% 1.53/0.54    k6_partfun1(u1_struct_0(sK0)) = k9_tmap_1(sK0,sK1) | ~spl6_96),
% 1.53/0.54    inference(avatar_component_clause,[],[f2038])).
% 1.53/0.54  fof(f2038,plain,(
% 1.53/0.54    spl6_96 <=> k6_partfun1(u1_struct_0(sK0)) = k9_tmap_1(sK0,sK1)),
% 1.53/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_96])])).
% 1.53/0.54  fof(f50,plain,(
% 1.53/0.54    ( ! [X0,X1] : (v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) | ~sP2(X1,X0)) )),
% 1.53/0.54    inference(cnf_transformation,[],[f19])).
% 1.53/0.54  fof(f19,plain,(
% 1.53/0.54    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.53/0.54    inference(flattening,[],[f18])).
% 1.53/0.54  fof(f18,plain,(
% 1.53/0.54    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1)))) & m1_pre_topc(X1,X0)) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.53/0.54    inference(ennf_transformation,[],[f17])).
% 1.53/0.54  fof(f17,negated_conjecture,(
% 1.53/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))))))),
% 1.53/0.54    inference(negated_conjecture,[],[f16])).
% 1.53/0.54  fof(f16,conjecture,(
% 1.53/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))))))),
% 1.53/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t122_tmap_1)).
% 1.53/0.54  fof(f2125,plain,(
% 1.53/0.54    spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | spl6_5 | ~spl6_16 | ~spl6_21 | ~spl6_23 | ~spl6_25 | ~spl6_26 | ~spl6_38 | ~spl6_52 | ~spl6_61),
% 1.53/0.54    inference(avatar_contradiction_clause,[],[f2124])).
% 1.53/0.54  fof(f2124,plain,(
% 1.53/0.54    $false | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | spl6_5 | ~spl6_16 | ~spl6_21 | ~spl6_23 | ~spl6_25 | ~spl6_26 | ~spl6_38 | ~spl6_52 | ~spl6_61)),
% 1.53/0.54    inference(subsumption_resolution,[],[f2123,f553])).
% 1.53/0.54  fof(f553,plain,(
% 1.53/0.54    v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | ~spl6_26),
% 1.53/0.54    inference(avatar_component_clause,[],[f551])).
% 1.53/0.54  fof(f551,plain,(
% 1.53/0.54    spl6_26 <=> v1_funct_1(k6_partfun1(u1_struct_0(sK0)))),
% 1.53/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 1.53/0.54  fof(f2123,plain,(
% 1.53/0.54    ~v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | spl6_5 | ~spl6_16 | ~spl6_21 | ~spl6_23 | ~spl6_25 | ~spl6_38 | ~spl6_52 | ~spl6_61)),
% 1.53/0.54    inference(forward_demodulation,[],[f2122,f351])).
% 1.53/0.54  fof(f351,plain,(
% 1.53/0.54    k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK1)) | ~spl6_21),
% 1.53/0.54    inference(avatar_component_clause,[],[f349])).
% 1.53/0.54  fof(f349,plain,(
% 1.53/0.54    spl6_21 <=> k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK1))),
% 1.53/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 1.53/0.54  fof(f2122,plain,(
% 1.53/0.54    ~v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | spl6_5 | ~spl6_16 | ~spl6_21 | ~spl6_23 | ~spl6_25 | ~spl6_38 | ~spl6_52 | ~spl6_61)),
% 1.53/0.54    inference(subsumption_resolution,[],[f2121,f1071])).
% 1.53/0.54  fof(f1071,plain,(
% 1.53/0.54    v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~spl6_52),
% 1.53/0.54    inference(avatar_component_clause,[],[f1069])).
% 1.53/0.54  fof(f1069,plain,(
% 1.53/0.54    spl6_52 <=> v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))),
% 1.53/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).
% 1.53/0.54  fof(f2121,plain,(
% 1.53/0.54    ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | spl6_5 | ~spl6_16 | ~spl6_21 | ~spl6_23 | ~spl6_25 | ~spl6_38 | ~spl6_61)),
% 1.53/0.54    inference(forward_demodulation,[],[f2120,f351])).
% 1.53/0.54  fof(f2120,plain,(
% 1.53/0.54    ~v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | spl6_5 | ~spl6_16 | ~spl6_21 | ~spl6_23 | ~spl6_25 | ~spl6_38 | ~spl6_61)),
% 1.53/0.54    inference(forward_demodulation,[],[f2119,f432])).
% 1.53/0.54  fof(f432,plain,(
% 1.53/0.54    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) | ~spl6_23),
% 1.53/0.54    inference(avatar_component_clause,[],[f430])).
% 1.53/0.54  fof(f430,plain,(
% 1.53/0.54    spl6_23 <=> u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))),
% 1.53/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 1.53/0.54  fof(f2119,plain,(
% 1.53/0.54    ~v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))) | ~v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | spl6_5 | ~spl6_16 | ~spl6_21 | ~spl6_25 | ~spl6_38 | ~spl6_61)),
% 1.53/0.54    inference(subsumption_resolution,[],[f2118,f1185])).
% 1.53/0.54  fof(f1185,plain,(
% 1.53/0.54    v5_pre_topc(k6_partfun1(u1_struct_0(sK0)),sK0,k8_tmap_1(sK0,sK1)) | ~spl6_61),
% 1.53/0.54    inference(avatar_component_clause,[],[f1183])).
% 1.53/0.54  fof(f2118,plain,(
% 1.53/0.54    ~v5_pre_topc(k6_partfun1(u1_struct_0(sK0)),sK0,k8_tmap_1(sK0,sK1)) | ~v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))) | ~v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | spl6_5 | ~spl6_16 | ~spl6_21 | ~spl6_25 | ~spl6_38)),
% 1.53/0.54    inference(forward_demodulation,[],[f2117,f351])).
% 1.53/0.54  fof(f2117,plain,(
% 1.53/0.54    ~v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k8_tmap_1(sK0,sK1)) | ~v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))) | ~v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | spl6_5 | ~spl6_16 | ~spl6_25 | ~spl6_38)),
% 1.53/0.54    inference(forward_demodulation,[],[f2116,f654])).
% 1.53/0.54  fof(f654,plain,(
% 1.53/0.54    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~spl6_38),
% 1.53/0.54    inference(avatar_component_clause,[],[f652])).
% 1.53/0.54  fof(f652,plain,(
% 1.53/0.54    spl6_38 <=> k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))),
% 1.53/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).
% 1.53/0.54  fof(f2116,plain,(
% 1.53/0.54    ~v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k6_tmap_1(sK0,u1_struct_0(sK1))) | ~v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))) | ~v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | spl6_5 | ~spl6_16 | ~spl6_25)),
% 1.53/0.54    inference(subsumption_resolution,[],[f2115,f150])).
% 1.53/0.54  fof(f150,plain,(
% 1.53/0.54    ~v1_tsep_1(sK1,sK0) | spl6_5),
% 1.53/0.54    inference(avatar_component_clause,[],[f149])).
% 1.53/0.54  fof(f149,plain,(
% 1.53/0.54    spl6_5 <=> v1_tsep_1(sK1,sK0)),
% 1.53/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.53/0.54  fof(f2115,plain,(
% 1.53/0.54    ~v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k6_tmap_1(sK0,u1_struct_0(sK1))) | ~v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))) | ~v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | v1_tsep_1(sK1,sK0) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_16 | ~spl6_25)),
% 1.53/0.54    inference(subsumption_resolution,[],[f2114,f119])).
% 1.53/0.54  fof(f119,plain,(
% 1.53/0.54    m1_pre_topc(sK1,sK0) | ~spl6_4),
% 1.53/0.54    inference(avatar_component_clause,[],[f117])).
% 1.53/0.54  fof(f117,plain,(
% 1.53/0.54    spl6_4 <=> m1_pre_topc(sK1,sK0)),
% 1.53/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.53/0.54  fof(f2114,plain,(
% 1.53/0.54    ~v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k6_tmap_1(sK0,u1_struct_0(sK1))) | ~v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))) | ~v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | ~m1_pre_topc(sK1,sK0) | v1_tsep_1(sK1,sK0) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_16 | ~spl6_25)),
% 1.53/0.54    inference(subsumption_resolution,[],[f2111,f548])).
% 1.53/0.54  fof(f548,plain,(
% 1.53/0.54    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_25),
% 1.53/0.54    inference(avatar_component_clause,[],[f547])).
% 1.53/0.54  fof(f547,plain,(
% 1.53/0.54    spl6_25 <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.53/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 1.53/0.54  fof(f2111,plain,(
% 1.53/0.54    ~v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k6_tmap_1(sK0,u1_struct_0(sK1))) | ~v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))) | ~v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_pre_topc(sK1,sK0) | v1_tsep_1(sK1,sK0) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_16)),
% 1.53/0.54    inference(superposition,[],[f434,f298])).
% 1.53/0.54  fof(f298,plain,(
% 1.53/0.54    u1_struct_0(sK1) = sK3(sK0,sK1) | ~spl6_16),
% 1.53/0.54    inference(avatar_component_clause,[],[f296])).
% 1.53/0.54  fof(f296,plain,(
% 1.53/0.54    spl6_16 <=> u1_struct_0(sK1) = sK3(sK0,sK1)),
% 1.53/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 1.53/0.54  fof(f434,plain,(
% 1.53/0.54    ( ! [X0] : (~v5_pre_topc(k7_tmap_1(sK0,sK3(sK0,X0)),sK0,k6_tmap_1(sK0,sK3(sK0,X0))) | ~v1_funct_2(k7_tmap_1(sK0,sK3(sK0,X0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK3(sK0,X0)))) | ~v1_funct_1(k7_tmap_1(sK0,sK3(sK0,X0))) | ~m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_pre_topc(X0,sK0) | v1_tsep_1(X0,sK0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3)),
% 1.53/0.54    inference(resolution,[],[f285,f146])).
% 1.53/0.54  fof(f146,plain,(
% 1.53/0.54    ( ! [X2] : (~v3_pre_topc(sK3(sK0,X2),sK0) | ~m1_pre_topc(X2,sK0) | v1_tsep_1(X2,sK0)) ) | ~spl6_3),
% 1.53/0.54    inference(resolution,[],[f114,f65])).
% 1.53/0.54  fof(f65,plain,(
% 1.53/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v3_pre_topc(sK3(X0,X1),X0) | v1_tsep_1(X1,X0)) )),
% 1.53/0.54    inference(cnf_transformation,[],[f24])).
% 1.53/0.54  fof(f24,plain,(
% 1.53/0.54    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.53/0.54    inference(flattening,[],[f23])).
% 1.53/0.54  fof(f23,plain,(
% 1.53/0.54    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.53/0.54    inference(ennf_transformation,[],[f7])).
% 1.53/0.54  fof(f7,axiom,(
% 1.53/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tsep_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v3_pre_topc(X2,X0))))))),
% 1.53/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tsep_1)).
% 1.53/0.54  fof(f114,plain,(
% 1.53/0.54    l1_pre_topc(sK0) | ~spl6_3),
% 1.53/0.54    inference(avatar_component_clause,[],[f112])).
% 1.53/0.54  fof(f112,plain,(
% 1.53/0.54    spl6_3 <=> l1_pre_topc(sK0)),
% 1.53/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.53/0.54  fof(f285,plain,(
% 1.53/0.54    ( ! [X0] : (v3_pre_topc(X0,sK0) | ~v1_funct_1(k7_tmap_1(sK0,X0)) | ~v1_funct_2(k7_tmap_1(sK0,X0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X0))) | ~v5_pre_topc(k7_tmap_1(sK0,X0),sK0,k6_tmap_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl6_1 | ~spl6_2 | ~spl6_3)),
% 1.53/0.54    inference(subsumption_resolution,[],[f284,f104])).
% 1.53/0.54  fof(f104,plain,(
% 1.53/0.54    ~v2_struct_0(sK0) | spl6_1),
% 1.53/0.54    inference(avatar_component_clause,[],[f102])).
% 1.53/0.54  fof(f102,plain,(
% 1.53/0.54    spl6_1 <=> v2_struct_0(sK0)),
% 1.53/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.53/0.54  fof(f284,plain,(
% 1.53/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_funct_1(k7_tmap_1(sK0,X0)) | ~v1_funct_2(k7_tmap_1(sK0,X0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X0))) | ~v5_pre_topc(k7_tmap_1(sK0,X0),sK0,k6_tmap_1(sK0,X0)) | v2_struct_0(sK0) | v3_pre_topc(X0,sK0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3)),
% 1.53/0.54    inference(subsumption_resolution,[],[f283,f114])).
% 1.53/0.54  fof(f283,plain,(
% 1.53/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v1_funct_1(k7_tmap_1(sK0,X0)) | ~v1_funct_2(k7_tmap_1(sK0,X0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X0))) | ~v5_pre_topc(k7_tmap_1(sK0,X0),sK0,k6_tmap_1(sK0,X0)) | v2_struct_0(sK0) | v3_pre_topc(X0,sK0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3)),
% 1.53/0.54    inference(subsumption_resolution,[],[f282,f109])).
% 1.53/0.54  fof(f109,plain,(
% 1.53/0.54    v2_pre_topc(sK0) | ~spl6_2),
% 1.53/0.54    inference(avatar_component_clause,[],[f107])).
% 1.53/0.54  fof(f107,plain,(
% 1.53/0.54    spl6_2 <=> v2_pre_topc(sK0)),
% 1.53/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.53/0.54  fof(f282,plain,(
% 1.53/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(k7_tmap_1(sK0,X0)) | ~v1_funct_2(k7_tmap_1(sK0,X0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X0))) | ~v5_pre_topc(k7_tmap_1(sK0,X0),sK0,k6_tmap_1(sK0,X0)) | v2_struct_0(sK0) | v3_pre_topc(X0,sK0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3)),
% 1.53/0.54    inference(duplicate_literal_removal,[],[f281])).
% 1.53/0.54  fof(f281,plain,(
% 1.53/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_funct_1(k7_tmap_1(sK0,X0)) | ~v1_funct_2(k7_tmap_1(sK0,X0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X0))) | ~v5_pre_topc(k7_tmap_1(sK0,X0),sK0,k6_tmap_1(sK0,X0)) | v2_struct_0(sK0) | v3_pre_topc(X0,sK0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3)),
% 1.53/0.54    inference(resolution,[],[f275,f82])).
% 1.53/0.54  fof(f82,plain,(
% 1.53/0.54    ( ! [X0,X1] : (~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_funct_1(k7_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | v2_struct_0(X0) | v3_pre_topc(X1,X0)) )),
% 1.53/0.54    inference(cnf_transformation,[],[f36])).
% 1.53/0.54  fof(f36,plain,(
% 1.53/0.54    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.53/0.54    inference(flattening,[],[f35])).
% 1.53/0.54  fof(f35,plain,(
% 1.53/0.54    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.53/0.54    inference(ennf_transformation,[],[f12])).
% 1.53/0.54  fof(f12,axiom,(
% 1.53/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))))),
% 1.53/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_tmap_1)).
% 1.53/0.54  fof(f275,plain,(
% 1.53/0.54    ( ! [X12] : (m1_subset_1(k7_tmap_1(sK0,X12),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X12))))) | ~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl6_1 | ~spl6_2 | ~spl6_3)),
% 1.53/0.54    inference(subsumption_resolution,[],[f143,f114])).
% 1.53/0.54  fof(f143,plain,(
% 1.53/0.54    ( ! [X12] : (~l1_pre_topc(sK0) | ~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k7_tmap_1(sK0,X12),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X12)))))) ) | (spl6_1 | ~spl6_2)),
% 1.53/0.54    inference(subsumption_resolution,[],[f132,f104])).
% 1.53/0.54  fof(f132,plain,(
% 1.53/0.54    ( ! [X12] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k7_tmap_1(sK0,X12),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X12)))))) ) | ~spl6_2),
% 1.53/0.54    inference(resolution,[],[f109,f92])).
% 1.53/0.54  fof(f92,plain,(
% 1.53/0.54    ( ! [X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))) )),
% 1.53/0.54    inference(cnf_transformation,[],[f44])).
% 1.53/0.54  fof(f44,plain,(
% 1.53/0.54    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.53/0.54    inference(flattening,[],[f43])).
% 1.53/0.54  fof(f43,plain,(
% 1.53/0.54    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.53/0.54    inference(ennf_transformation,[],[f8])).
% 1.53/0.54  fof(f8,axiom,(
% 1.53/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 1.53/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).
% 1.53/0.54  fof(f2100,plain,(
% 1.53/0.54    k9_tmap_1(sK0,sK1) != k9_tmap_1(sK0,sK0) | k6_partfun1(u1_struct_0(sK0)) != k9_tmap_1(sK0,sK0) | k6_partfun1(u1_struct_0(sK0)) = k9_tmap_1(sK0,sK1)),
% 1.53/0.54    introduced(theory_tautology_sat_conflict,[])).
% 1.53/0.54  fof(f2035,plain,(
% 1.53/0.54    k9_tmap_1(sK0,sK1) != k9_tmap_1(sK0,sK0) | k6_partfun1(u1_struct_0(sK0)) != k9_tmap_1(sK0,sK0) | v5_pre_topc(k9_tmap_1(sK0,sK1),sK0,k8_tmap_1(sK0,sK1)) | ~v5_pre_topc(k6_partfun1(u1_struct_0(sK0)),sK0,k8_tmap_1(sK0,sK1))),
% 1.53/0.54    introduced(theory_tautology_sat_conflict,[])).
% 1.53/0.54  fof(f2027,plain,(
% 1.53/0.54    ~spl6_17 | ~spl6_41 | ~spl6_45 | ~spl6_93),
% 1.53/0.54    inference(avatar_contradiction_clause,[],[f2026])).
% 1.53/0.54  fof(f2026,plain,(
% 1.53/0.54    $false | (~spl6_17 | ~spl6_41 | ~spl6_45 | ~spl6_93)),
% 1.53/0.54    inference(subsumption_resolution,[],[f2025,f806])).
% 1.53/0.54  fof(f806,plain,(
% 1.53/0.54    v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | ~spl6_41),
% 1.53/0.54    inference(avatar_component_clause,[],[f804])).
% 1.53/0.54  fof(f804,plain,(
% 1.53/0.54    spl6_41 <=> v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))),
% 1.53/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 1.53/0.54  fof(f2025,plain,(
% 1.53/0.54    ~v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | (~spl6_17 | ~spl6_45 | ~spl6_93)),
% 1.53/0.54    inference(subsumption_resolution,[],[f2022,f307])).
% 1.53/0.54  fof(f307,plain,(
% 1.53/0.54    v1_funct_1(k9_tmap_1(sK0,sK1)) | ~spl6_17),
% 1.53/0.54    inference(avatar_component_clause,[],[f306])).
% 1.53/0.54  fof(f306,plain,(
% 1.53/0.54    spl6_17 <=> v1_funct_1(k9_tmap_1(sK0,sK1))),
% 1.53/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 1.53/0.54  fof(f2022,plain,(
% 1.53/0.54    ~v1_funct_1(k9_tmap_1(sK0,sK1)) | ~v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | (~spl6_45 | ~spl6_93)),
% 1.53/0.54    inference(resolution,[],[f1999,f924])).
% 1.53/0.54  fof(f924,plain,(
% 1.53/0.54    m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~spl6_45),
% 1.53/0.54    inference(avatar_component_clause,[],[f922])).
% 1.53/0.54  fof(f922,plain,(
% 1.53/0.54    spl6_45 <=> m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 1.53/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).
% 1.53/0.54  fof(f1999,plain,(
% 1.53/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))) ) | ~spl6_93),
% 1.53/0.54    inference(avatar_component_clause,[],[f1998])).
% 1.53/0.54  fof(f1998,plain,(
% 1.53/0.54    spl6_93 <=> ! [X0] : (~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)))),
% 1.53/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_93])])).
% 1.53/0.54  fof(f2020,plain,(
% 1.53/0.54    ~spl6_3 | spl6_95),
% 1.53/0.54    inference(avatar_contradiction_clause,[],[f2019])).
% 1.53/0.54  fof(f2019,plain,(
% 1.53/0.54    $false | (~spl6_3 | spl6_95)),
% 1.53/0.54    inference(subsumption_resolution,[],[f2018,f114])).
% 1.53/0.54  fof(f2018,plain,(
% 1.53/0.54    ~l1_pre_topc(sK0) | spl6_95),
% 1.53/0.54    inference(resolution,[],[f2016,f59])).
% 1.53/0.54  fof(f59,plain,(
% 1.53/0.54    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.53/0.54    inference(cnf_transformation,[],[f20])).
% 1.53/0.54  fof(f20,plain,(
% 1.53/0.54    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.53/0.54    inference(ennf_transformation,[],[f1])).
% 1.53/0.54  fof(f1,axiom,(
% 1.53/0.54    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.53/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.53/0.54  fof(f2016,plain,(
% 1.53/0.54    ~l1_struct_0(sK0) | spl6_95),
% 1.53/0.54    inference(avatar_component_clause,[],[f2014])).
% 1.53/0.54  fof(f2014,plain,(
% 1.53/0.54    spl6_95 <=> l1_struct_0(sK0)),
% 1.53/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_95])])).
% 1.53/0.54  fof(f2017,plain,(
% 1.53/0.54    ~spl6_95 | spl6_1 | ~spl6_37),
% 1.53/0.54    inference(avatar_split_clause,[],[f2012,f639,f102,f2014])).
% 1.53/0.54  fof(f639,plain,(
% 1.53/0.54    spl6_37 <=> v1_xboole_0(u1_struct_0(sK0))),
% 1.53/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 1.53/0.54  fof(f2012,plain,(
% 1.53/0.54    ~l1_struct_0(sK0) | (spl6_1 | ~spl6_37)),
% 1.53/0.54    inference(subsumption_resolution,[],[f2011,f104])).
% 1.53/0.54  fof(f2011,plain,(
% 1.53/0.54    ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl6_37),
% 1.53/0.54    inference(resolution,[],[f640,f66])).
% 1.53/0.54  fof(f66,plain,(
% 1.53/0.54    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.53/0.54    inference(cnf_transformation,[],[f26])).
% 1.53/0.54  fof(f26,plain,(
% 1.53/0.54    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.53/0.54    inference(flattening,[],[f25])).
% 1.53/0.54  fof(f25,plain,(
% 1.53/0.54    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.53/0.54    inference(ennf_transformation,[],[f2])).
% 1.53/0.54  fof(f2,axiom,(
% 1.53/0.54    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.53/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.53/0.54  fof(f640,plain,(
% 1.53/0.54    v1_xboole_0(u1_struct_0(sK0)) | ~spl6_37),
% 1.53/0.54    inference(avatar_component_clause,[],[f639])).
% 1.53/0.54  fof(f2004,plain,(
% 1.53/0.54    spl6_93 | spl6_94 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_21 | ~spl6_23 | ~spl6_26 | spl6_37 | ~spl6_39 | ~spl6_52 | ~spl6_59 | ~spl6_90),
% 1.53/0.54    inference(avatar_split_clause,[],[f1991,f1920,f1162,f1069,f658,f639,f551,f430,f349,f117,f112,f107,f102,f2001,f1998])).
% 1.53/0.54  fof(f2001,plain,(
% 1.53/0.54    spl6_94 <=> k6_partfun1(u1_struct_0(sK0)) = k9_tmap_1(sK0,sK0)),
% 1.53/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_94])])).
% 1.53/0.54  fof(f658,plain,(
% 1.53/0.54    spl6_39 <=> u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))),
% 1.53/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).
% 1.53/0.54  fof(f1162,plain,(
% 1.53/0.54    spl6_59 <=> m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 1.53/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).
% 1.53/0.54  fof(f1920,plain,(
% 1.53/0.54    spl6_90 <=> k9_tmap_1(sK0,sK1) = k9_tmap_1(sK0,sK0)),
% 1.53/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_90])])).
% 1.53/0.54  fof(f1991,plain,(
% 1.53/0.54    ( ! [X0] : (k6_partfun1(u1_struct_0(sK0)) = k9_tmap_1(sK0,sK0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_21 | ~spl6_23 | ~spl6_26 | spl6_37 | ~spl6_39 | ~spl6_52 | ~spl6_59 | ~spl6_90)),
% 1.53/0.54    inference(forward_demodulation,[],[f1990,f1922])).
% 1.53/0.54  fof(f1922,plain,(
% 1.53/0.54    k9_tmap_1(sK0,sK1) = k9_tmap_1(sK0,sK0) | ~spl6_90),
% 1.53/0.54    inference(avatar_component_clause,[],[f1920])).
% 1.53/0.54  fof(f1990,plain,(
% 1.53/0.54    ( ! [X0] : (k6_partfun1(u1_struct_0(sK0)) = k9_tmap_1(sK0,sK1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_21 | ~spl6_23 | ~spl6_26 | spl6_37 | ~spl6_39 | ~spl6_52 | ~spl6_59)),
% 1.53/0.54    inference(subsumption_resolution,[],[f1130,f1164])).
% 1.53/0.54  fof(f1164,plain,(
% 1.53/0.54    m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~spl6_59),
% 1.53/0.54    inference(avatar_component_clause,[],[f1162])).
% 1.53/0.54  fof(f1130,plain,(
% 1.53/0.54    ( ! [X0] : (~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | k6_partfun1(u1_struct_0(sK0)) = k9_tmap_1(sK0,sK1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_21 | ~spl6_23 | ~spl6_26 | spl6_37 | ~spl6_39 | ~spl6_52)),
% 1.53/0.54    inference(subsumption_resolution,[],[f1129,f641])).
% 1.53/0.54  fof(f641,plain,(
% 1.53/0.54    ~v1_xboole_0(u1_struct_0(sK0)) | spl6_37),
% 1.53/0.54    inference(avatar_component_clause,[],[f639])).
% 1.53/0.54  fof(f1129,plain,(
% 1.53/0.54    ( ! [X0] : (~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | k6_partfun1(u1_struct_0(sK0)) = k9_tmap_1(sK0,sK1) | v1_xboole_0(u1_struct_0(sK0)) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_21 | ~spl6_23 | ~spl6_26 | ~spl6_39 | ~spl6_52)),
% 1.53/0.54    inference(subsumption_resolution,[],[f1128,f553])).
% 1.53/0.54  fof(f1128,plain,(
% 1.53/0.54    ( ! [X0] : (~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | k6_partfun1(u1_struct_0(sK0)) = k9_tmap_1(sK0,sK1) | v1_xboole_0(u1_struct_0(sK0)) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_21 | ~spl6_23 | ~spl6_39 | ~spl6_52)),
% 1.53/0.54    inference(subsumption_resolution,[],[f1127,f1071])).
% 1.53/0.54  fof(f1127,plain,(
% 1.53/0.54    ( ! [X0] : (~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | k6_partfun1(u1_struct_0(sK0)) = k9_tmap_1(sK0,sK1) | v1_xboole_0(u1_struct_0(sK0)) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_21 | ~spl6_23 | ~spl6_39)),
% 1.53/0.54    inference(duplicate_literal_removal,[],[f1126])).
% 1.53/0.54  fof(f1126,plain,(
% 1.53/0.54    ( ! [X0] : (~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | k6_partfun1(u1_struct_0(sK0)) = k9_tmap_1(sK0,sK1) | v1_xboole_0(u1_struct_0(sK0)) | ~v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | v1_xboole_0(u1_struct_0(sK0))) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_21 | ~spl6_23 | ~spl6_39)),
% 1.53/0.54    inference(resolution,[],[f1121,f93])).
% 1.53/0.54  fof(f93,plain,(
% 1.53/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | v1_xboole_0(X3) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X0,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | v1_xboole_0(X1)) )),
% 1.53/0.54    inference(cnf_transformation,[],[f46])).
% 1.53/0.54  fof(f46,plain,(
% 1.53/0.54    ! [X0,X1,X2,X3,X4,X5] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 1.53/0.54    inference(flattening,[],[f45])).
% 1.53/0.54  fof(f45,plain,(
% 1.53/0.54    ! [X0,X1,X2,X3,X4,X5] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 1.53/0.54    inference(ennf_transformation,[],[f3])).
% 1.53/0.54  fof(f3,axiom,(
% 1.53/0.54    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => r1_funct_2(X0,X1,X2,X3,X4,X4))),
% 1.53/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r1_funct_2)).
% 1.53/0.54  fof(f1121,plain,(
% 1.53/0.54    ( ! [X0] : (~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),X0,k6_partfun1(u1_struct_0(sK0))) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_1(X0) | k9_tmap_1(sK0,sK1) = X0) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_21 | ~spl6_23 | ~spl6_39)),
% 1.53/0.54    inference(forward_demodulation,[],[f1120,f660])).
% 1.53/0.54  fof(f660,plain,(
% 1.53/0.54    u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) | ~spl6_39),
% 1.53/0.54    inference(avatar_component_clause,[],[f658])).
% 1.53/0.54  fof(f1120,plain,(
% 1.53/0.54    ( ! [X0] : (~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),X0,k6_partfun1(u1_struct_0(sK0))) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | k9_tmap_1(sK0,sK1) = X0) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_21 | ~spl6_23 | ~spl6_39)),
% 1.53/0.54    inference(forward_demodulation,[],[f1119,f660])).
% 1.53/0.54  fof(f1119,plain,(
% 1.53/0.54    ( ! [X0] : (~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),X0,k6_partfun1(u1_struct_0(sK0))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | k9_tmap_1(sK0,sK1) = X0) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_21 | ~spl6_23 | ~spl6_39)),
% 1.53/0.54    inference(forward_demodulation,[],[f497,f660])).
% 1.53/0.54  fof(f497,plain,(
% 1.53/0.54    ( ! [X0] : (~r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(sK0),X0,k6_partfun1(u1_struct_0(sK0))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | k9_tmap_1(sK0,sK1) = X0) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_21 | ~spl6_23)),
% 1.53/0.54    inference(forward_demodulation,[],[f496,f432])).
% 1.53/0.54  fof(f496,plain,(
% 1.53/0.54    ( ! [X0] : (~r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),X0,k6_partfun1(u1_struct_0(sK0))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | k9_tmap_1(sK0,sK1) = X0) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_21)),
% 1.53/0.54    inference(forward_demodulation,[],[f494,f351])).
% 1.53/0.54  fof(f494,plain,(
% 1.53/0.54    ( ! [X0] : (~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),X0,k7_tmap_1(sK0,u1_struct_0(sK1))) | k9_tmap_1(sK0,sK1) = X0) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4)),
% 1.53/0.54    inference(resolution,[],[f347,f119])).
% 1.53/0.54  fof(f347,plain,(
% 1.53/0.54    ( ! [X0,X1] : (~m1_pre_topc(X0,sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0))))) | ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0))),X1,k7_tmap_1(sK0,u1_struct_0(X0))) | k9_tmap_1(sK0,X0) = X1) ) | (spl6_1 | ~spl6_2 | ~spl6_3)),
% 1.53/0.54    inference(duplicate_literal_removal,[],[f346])).
% 1.53/0.54  fof(f346,plain,(
% 1.53/0.54    ( ! [X0,X1] : (~r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0))),X1,k7_tmap_1(sK0,u1_struct_0(X0))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0))))) | ~m1_pre_topc(X0,sK0) | k9_tmap_1(sK0,X0) = X1 | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0))))) | ~m1_pre_topc(X0,sK0) | k9_tmap_1(sK0,X0) = X1) ) | (spl6_1 | ~spl6_2 | ~spl6_3)),
% 1.53/0.54    inference(superposition,[],[f294,f291])).
% 1.53/0.54  fof(f291,plain,(
% 1.53/0.54    ( ! [X0,X1] : (u1_struct_0(X0) = sK5(sK0,X0,X1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0))))) | ~m1_pre_topc(X0,sK0) | k9_tmap_1(sK0,X0) = X1) ) | (spl6_1 | ~spl6_2 | ~spl6_3)),
% 1.53/0.54    inference(subsumption_resolution,[],[f133,f114])).
% 1.53/0.54  fof(f133,plain,(
% 1.53/0.54    ( ! [X0,X1] : (~l1_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0))))) | u1_struct_0(X0) = sK5(sK0,X0,X1) | k9_tmap_1(sK0,X0) = X1) ) | (spl6_1 | ~spl6_2)),
% 1.53/0.54    inference(subsumption_resolution,[],[f122,f104])).
% 1.53/0.54  fof(f122,plain,(
% 1.53/0.54    ( ! [X0,X1] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0))))) | u1_struct_0(X0) = sK5(sK0,X0,X1) | k9_tmap_1(sK0,X0) = X1) ) | ~spl6_2),
% 1.53/0.54    inference(resolution,[],[f109,f73])).
% 1.53/0.54  fof(f73,plain,(
% 1.53/0.54    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | u1_struct_0(X1) = sK5(X0,X1,X2) | k9_tmap_1(X0,X1) = X2) )),
% 1.53/0.54    inference(cnf_transformation,[],[f30])).
% 1.53/0.54  fof(f30,plain,(
% 1.53/0.54    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.53/0.54    inference(flattening,[],[f29])).
% 1.53/0.54  fof(f29,plain,(
% 1.53/0.54    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : ((r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.53/0.54    inference(ennf_transformation,[],[f6])).
% 1.53/0.54  fof(f6,axiom,(
% 1.53/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(X2)) => (k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))))))))),
% 1.53/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_tmap_1)).
% 1.53/0.54  fof(f294,plain,(
% 1.53/0.54    ( ! [X2,X3] : (~r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X2)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK5(sK0,X2,X3))),X3,k7_tmap_1(sK0,sK5(sK0,X2,X3))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X2))))) | ~m1_pre_topc(X2,sK0) | k9_tmap_1(sK0,X2) = X3) ) | (spl6_1 | ~spl6_2 | ~spl6_3)),
% 1.53/0.54    inference(subsumption_resolution,[],[f134,f114])).
% 1.53/0.54  fof(f134,plain,(
% 1.53/0.54    ( ! [X2,X3] : (~l1_pre_topc(sK0) | ~m1_pre_topc(X2,sK0) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X2))))) | ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X2)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK5(sK0,X2,X3))),X3,k7_tmap_1(sK0,sK5(sK0,X2,X3))) | k9_tmap_1(sK0,X2) = X3) ) | (spl6_1 | ~spl6_2)),
% 1.53/0.54    inference(subsumption_resolution,[],[f123,f104])).
% 1.53/0.54  fof(f123,plain,(
% 1.53/0.54    ( ! [X2,X3] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(X2,sK0) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X2))))) | ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X2)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK5(sK0,X2,X3))),X3,k7_tmap_1(sK0,sK5(sK0,X2,X3))) | k9_tmap_1(sK0,X2) = X3) ) | ~spl6_2),
% 1.53/0.54    inference(resolution,[],[f109,f74])).
% 1.53/0.54  fof(f74,plain,(
% 1.53/0.54    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK5(X0,X1,X2))),X2,k7_tmap_1(X0,sK5(X0,X1,X2))) | k9_tmap_1(X0,X1) = X2) )),
% 1.53/0.54    inference(cnf_transformation,[],[f30])).
% 1.53/0.54  fof(f1923,plain,(
% 1.53/0.54    spl6_90 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_7 | ~spl6_17 | ~spl6_22 | ~spl6_24 | ~spl6_41 | ~spl6_44 | ~spl6_45 | ~spl6_88),
% 1.53/0.54    inference(avatar_split_clause,[],[f1839,f1830,f922,f822,f804,f488,f386,f306,f158,f112,f107,f102,f1920])).
% 1.53/0.54  fof(f158,plain,(
% 1.53/0.54    spl6_7 <=> m1_pre_topc(sK0,sK0)),
% 1.53/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.53/0.54  fof(f386,plain,(
% 1.53/0.54    spl6_22 <=> k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK0))),
% 1.53/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 1.53/0.54  fof(f488,plain,(
% 1.53/0.54    spl6_24 <=> u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0)))),
% 1.53/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 1.53/0.54  fof(f822,plain,(
% 1.53/0.54    spl6_44 <=> u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK0))),
% 1.53/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).
% 1.53/0.54  fof(f1830,plain,(
% 1.53/0.54    spl6_88 <=> r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)))),
% 1.53/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_88])])).
% 1.53/0.54  fof(f1839,plain,(
% 1.53/0.54    k9_tmap_1(sK0,sK1) = k9_tmap_1(sK0,sK0) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_7 | ~spl6_17 | ~spl6_22 | ~spl6_24 | ~spl6_41 | ~spl6_44 | ~spl6_45 | ~spl6_88)),
% 1.53/0.54    inference(subsumption_resolution,[],[f1838,f307])).
% 1.53/0.54  fof(f1838,plain,(
% 1.53/0.54    ~v1_funct_1(k9_tmap_1(sK0,sK1)) | k9_tmap_1(sK0,sK1) = k9_tmap_1(sK0,sK0) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_7 | ~spl6_22 | ~spl6_24 | ~spl6_41 | ~spl6_44 | ~spl6_45 | ~spl6_88)),
% 1.53/0.54    inference(subsumption_resolution,[],[f1837,f924])).
% 1.53/0.54  fof(f1837,plain,(
% 1.53/0.54    ~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_1(k9_tmap_1(sK0,sK1)) | k9_tmap_1(sK0,sK1) = k9_tmap_1(sK0,sK0) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_7 | ~spl6_22 | ~spl6_24 | ~spl6_41 | ~spl6_44 | ~spl6_88)),
% 1.53/0.54    inference(subsumption_resolution,[],[f1835,f806])).
% 1.53/0.54  fof(f1835,plain,(
% 1.53/0.54    ~v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_1(k9_tmap_1(sK0,sK1)) | k9_tmap_1(sK0,sK1) = k9_tmap_1(sK0,sK0) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_7 | ~spl6_22 | ~spl6_24 | ~spl6_44 | ~spl6_88)),
% 1.53/0.54    inference(resolution,[],[f1832,f1136])).
% 1.53/0.54  fof(f1136,plain,(
% 1.53/0.54    ( ! [X1] : (~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),X1,k6_partfun1(u1_struct_0(sK0))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | k9_tmap_1(sK0,sK0) = X1) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_7 | ~spl6_22 | ~spl6_24 | ~spl6_44)),
% 1.53/0.54    inference(forward_demodulation,[],[f1135,f824])).
% 1.53/0.54  fof(f824,plain,(
% 1.53/0.54    u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK0)) | ~spl6_44),
% 1.53/0.54    inference(avatar_component_clause,[],[f822])).
% 1.53/0.54  fof(f1135,plain,(
% 1.53/0.54    ( ! [X1] : (~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(sK0)) | ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),X1,k6_partfun1(u1_struct_0(sK0))) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK0))))) | k9_tmap_1(sK0,sK0) = X1) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_7 | ~spl6_22 | ~spl6_24 | ~spl6_44)),
% 1.53/0.54    inference(forward_demodulation,[],[f1134,f824])).
% 1.53/0.54  fof(f1134,plain,(
% 1.53/0.54    ( ! [X1] : (~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),X1,k6_partfun1(u1_struct_0(sK0))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK0))))) | k9_tmap_1(sK0,sK0) = X1) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_7 | ~spl6_22 | ~spl6_24 | ~spl6_44)),
% 1.53/0.54    inference(forward_demodulation,[],[f1133,f824])).
% 1.53/0.54  fof(f1133,plain,(
% 1.53/0.54    ( ! [X1] : (~r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK0)),u1_struct_0(sK0),u1_struct_0(sK0),X1,k6_partfun1(u1_struct_0(sK0))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK0))))) | k9_tmap_1(sK0,sK0) = X1) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_7 | ~spl6_22 | ~spl6_24)),
% 1.53/0.54    inference(forward_demodulation,[],[f498,f490])).
% 1.53/0.54  fof(f490,plain,(
% 1.53/0.54    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))) | ~spl6_24),
% 1.53/0.54    inference(avatar_component_clause,[],[f488])).
% 1.53/0.54  fof(f498,plain,(
% 1.53/0.54    ( ! [X1] : (~r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))),X1,k6_partfun1(u1_struct_0(sK0))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK0))))) | k9_tmap_1(sK0,sK0) = X1) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_7 | ~spl6_22)),
% 1.53/0.54    inference(forward_demodulation,[],[f495,f388])).
% 1.53/0.54  fof(f388,plain,(
% 1.53/0.54    k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK0)) | ~spl6_22),
% 1.53/0.54    inference(avatar_component_clause,[],[f386])).
% 1.53/0.54  fof(f495,plain,(
% 1.53/0.54    ( ! [X1] : (~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK0))))) | ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))),X1,k7_tmap_1(sK0,u1_struct_0(sK0))) | k9_tmap_1(sK0,sK0) = X1) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_7)),
% 1.53/0.54    inference(resolution,[],[f347,f160])).
% 1.53/0.54  fof(f160,plain,(
% 1.53/0.54    m1_pre_topc(sK0,sK0) | ~spl6_7),
% 1.53/0.54    inference(avatar_component_clause,[],[f158])).
% 1.53/0.54  fof(f1832,plain,(
% 1.53/0.54    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0))) | ~spl6_88),
% 1.53/0.54    inference(avatar_component_clause,[],[f1830])).
% 1.53/0.54  fof(f1833,plain,(
% 1.53/0.54    spl6_88 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_17 | ~spl6_18 | ~spl6_20 | ~spl6_21 | ~spl6_25 | ~spl6_38 | ~spl6_39),
% 1.53/0.54    inference(avatar_split_clause,[],[f1828,f658,f652,f547,f349,f318,f310,f306,f117,f112,f107,f102,f1830])).
% 1.53/0.54  fof(f310,plain,(
% 1.53/0.54    spl6_18 <=> m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))),
% 1.53/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 1.53/0.54  fof(f318,plain,(
% 1.53/0.54    spl6_20 <=> v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))),
% 1.53/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 1.53/0.54  fof(f1828,plain,(
% 1.53/0.54    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_17 | ~spl6_18 | ~spl6_20 | ~spl6_21 | ~spl6_25 | ~spl6_38 | ~spl6_39)),
% 1.53/0.54    inference(forward_demodulation,[],[f684,f660])).
% 1.53/0.54  fof(f684,plain,(
% 1.53/0.54    r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k9_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_17 | ~spl6_18 | ~spl6_20 | ~spl6_21 | ~spl6_25 | ~spl6_38)),
% 1.53/0.54    inference(forward_demodulation,[],[f683,f351])).
% 1.53/0.54  fof(f683,plain,(
% 1.53/0.54    r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_17 | ~spl6_18 | ~spl6_20 | ~spl6_25 | ~spl6_38)),
% 1.53/0.54    inference(subsumption_resolution,[],[f682,f104])).
% 1.53/0.54  fof(f682,plain,(
% 1.53/0.54    r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_17 | ~spl6_18 | ~spl6_20 | ~spl6_25 | ~spl6_38)),
% 1.53/0.54    inference(subsumption_resolution,[],[f681,f548])).
% 1.53/0.54  fof(f681,plain,(
% 1.53/0.54    r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_17 | ~spl6_18 | ~spl6_20 | ~spl6_38)),
% 1.53/0.54    inference(subsumption_resolution,[],[f680,f311])).
% 1.53/0.54  fof(f311,plain,(
% 1.53/0.54    m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~spl6_18),
% 1.53/0.54    inference(avatar_component_clause,[],[f310])).
% 1.53/0.54  fof(f680,plain,(
% 1.53/0.54    r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) | ~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_17 | ~spl6_20 | ~spl6_38)),
% 1.53/0.54    inference(subsumption_resolution,[],[f679,f319])).
% 1.53/0.54  fof(f319,plain,(
% 1.53/0.54    v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~spl6_20),
% 1.53/0.54    inference(avatar_component_clause,[],[f318])).
% 1.53/0.54  fof(f679,plain,(
% 1.53/0.54    r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) | ~v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_17 | ~spl6_38)),
% 1.53/0.54    inference(subsumption_resolution,[],[f678,f307])).
% 1.53/0.54  fof(f678,plain,(
% 1.53/0.54    r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) | ~v1_funct_1(k9_tmap_1(sK0,sK1)) | ~v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_38)),
% 1.53/0.54    inference(subsumption_resolution,[],[f677,f119])).
% 1.53/0.54  fof(f677,plain,(
% 1.53/0.54    r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) | ~m1_pre_topc(sK1,sK0) | ~v1_funct_1(k9_tmap_1(sK0,sK1)) | ~v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_3 | ~spl6_38)),
% 1.53/0.54    inference(subsumption_resolution,[],[f676,f114])).
% 1.53/0.54  fof(f676,plain,(
% 1.53/0.54    r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_funct_1(k9_tmap_1(sK0,sK1)) | ~v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_38)),
% 1.53/0.54    inference(subsumption_resolution,[],[f667,f109])).
% 1.53/0.54  fof(f667,plain,(
% 1.53/0.54    r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_funct_1(k9_tmap_1(sK0,sK1)) | ~v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~spl6_38),
% 1.53/0.54    inference(superposition,[],[f98,f654])).
% 1.53/0.54  fof(f98,plain,(
% 1.53/0.54    ( ! [X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) )),
% 1.53/0.54    inference(equality_resolution,[],[f97])).
% 1.53/0.54  fof(f97,plain,(
% 1.53/0.54    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),X2,k7_tmap_1(X0,u1_struct_0(X1))) | k9_tmap_1(X0,X1) != X2) )),
% 1.53/0.54    inference(equality_resolution,[],[f71])).
% 1.53/0.54  fof(f71,plain,(
% 1.53/0.54    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X3 | r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | k9_tmap_1(X0,X1) != X2) )),
% 1.53/0.54    inference(cnf_transformation,[],[f30])).
% 1.53/0.54  fof(f1192,plain,(
% 1.53/0.54    ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_25 | spl6_60),
% 1.53/0.54    inference(avatar_contradiction_clause,[],[f1191])).
% 1.53/0.54  fof(f1191,plain,(
% 1.53/0.54    $false | (~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_25 | spl6_60)),
% 1.53/0.54    inference(subsumption_resolution,[],[f1190,f151])).
% 1.53/0.54  fof(f151,plain,(
% 1.53/0.54    v1_tsep_1(sK1,sK0) | ~spl6_5),
% 1.53/0.54    inference(avatar_component_clause,[],[f149])).
% 1.53/0.54  fof(f1190,plain,(
% 1.53/0.54    ~v1_tsep_1(sK1,sK0) | (~spl6_3 | ~spl6_4 | ~spl6_25 | spl6_60)),
% 1.53/0.54    inference(subsumption_resolution,[],[f1189,f119])).
% 1.53/0.54  fof(f1189,plain,(
% 1.53/0.54    ~m1_pre_topc(sK1,sK0) | ~v1_tsep_1(sK1,sK0) | (~spl6_3 | ~spl6_25 | spl6_60)),
% 1.53/0.54    inference(subsumption_resolution,[],[f1187,f548])).
% 1.53/0.54  fof(f1187,plain,(
% 1.53/0.54    ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_pre_topc(sK1,sK0) | ~v1_tsep_1(sK1,sK0) | (~spl6_3 | spl6_60)),
% 1.53/0.54    inference(resolution,[],[f1181,f144])).
% 1.53/0.54  fof(f144,plain,(
% 1.53/0.54    ( ! [X0] : (v3_pre_topc(u1_struct_0(X0),sK0) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_pre_topc(X0,sK0) | ~v1_tsep_1(X0,sK0)) ) | ~spl6_3),
% 1.53/0.54    inference(resolution,[],[f114,f94])).
% 1.53/0.54  fof(f94,plain,(
% 1.53/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(u1_struct_0(X1),X0) | ~v1_tsep_1(X1,X0)) )),
% 1.53/0.54    inference(equality_resolution,[],[f62])).
% 1.53/0.54  fof(f62,plain,(
% 1.53/0.54    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | v3_pre_topc(X2,X0) | ~v1_tsep_1(X1,X0)) )),
% 1.53/0.54    inference(cnf_transformation,[],[f24])).
% 1.53/0.54  fof(f1181,plain,(
% 1.53/0.54    ~v3_pre_topc(u1_struct_0(sK1),sK0) | spl6_60),
% 1.53/0.54    inference(avatar_component_clause,[],[f1179])).
% 1.53/0.54  fof(f1179,plain,(
% 1.53/0.54    spl6_60 <=> v3_pre_topc(u1_struct_0(sK1),sK0)),
% 1.53/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).
% 1.53/0.54  fof(f1186,plain,(
% 1.53/0.54    ~spl6_60 | spl6_61 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_21 | ~spl6_25 | ~spl6_38),
% 1.53/0.54    inference(avatar_split_clause,[],[f674,f652,f547,f349,f112,f107,f102,f1183,f1179])).
% 1.53/0.54  fof(f674,plain,(
% 1.53/0.54    v5_pre_topc(k6_partfun1(u1_struct_0(sK0)),sK0,k8_tmap_1(sK0,sK1)) | ~v3_pre_topc(u1_struct_0(sK1),sK0) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_21 | ~spl6_25 | ~spl6_38)),
% 1.53/0.54    inference(forward_demodulation,[],[f673,f351])).
% 1.53/0.54  fof(f673,plain,(
% 1.53/0.54    v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k8_tmap_1(sK0,sK1)) | ~v3_pre_topc(u1_struct_0(sK1),sK0) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_25 | ~spl6_38)),
% 1.53/0.54    inference(subsumption_resolution,[],[f665,f548])).
% 1.53/0.54  fof(f665,plain,(
% 1.53/0.54    v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k8_tmap_1(sK0,sK1)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(u1_struct_0(sK1),sK0) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_38)),
% 1.53/0.54    inference(superposition,[],[f265,f654])).
% 1.53/0.54  fof(f265,plain,(
% 1.53/0.54    ( ! [X7] : (v5_pre_topc(k7_tmap_1(sK0,X7),sK0,k6_tmap_1(sK0,X7)) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X7,sK0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3)),
% 1.53/0.54    inference(subsumption_resolution,[],[f138,f114])).
% 1.53/0.54  fof(f138,plain,(
% 1.53/0.54    ( ! [X7] : (~l1_pre_topc(sK0) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) | v5_pre_topc(k7_tmap_1(sK0,X7),sK0,k6_tmap_1(sK0,X7)) | ~v3_pre_topc(X7,sK0)) ) | (spl6_1 | ~spl6_2)),
% 1.53/0.54    inference(subsumption_resolution,[],[f127,f104])).
% 1.53/0.54  fof(f127,plain,(
% 1.53/0.54    ( ! [X7] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) | v5_pre_topc(k7_tmap_1(sK0,X7),sK0,k6_tmap_1(sK0,X7)) | ~v3_pre_topc(X7,sK0)) ) | ~spl6_2),
% 1.53/0.54    inference(resolution,[],[f109,f80])).
% 1.53/0.54  fof(f80,plain,(
% 1.53/0.54    ( ! [X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v3_pre_topc(X1,X0)) )),
% 1.53/0.54    inference(cnf_transformation,[],[f36])).
% 1.53/0.54  fof(f1165,plain,(
% 1.53/0.54    spl6_59 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_21 | ~spl6_25 | ~spl6_38 | ~spl6_39),
% 1.53/0.54    inference(avatar_split_clause,[],[f1160,f658,f652,f547,f349,f112,f107,f102,f1162])).
% 1.53/0.54  fof(f1160,plain,(
% 1.53/0.54    m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_21 | ~spl6_25 | ~spl6_38 | ~spl6_39)),
% 1.53/0.54    inference(forward_demodulation,[],[f672,f660])).
% 1.53/0.54  fof(f672,plain,(
% 1.53/0.54    m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_21 | ~spl6_25 | ~spl6_38)),
% 1.53/0.54    inference(forward_demodulation,[],[f671,f351])).
% 1.53/0.54  fof(f671,plain,(
% 1.53/0.54    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_25 | ~spl6_38)),
% 1.53/0.54    inference(subsumption_resolution,[],[f664,f548])).
% 1.53/0.54  fof(f664,plain,(
% 1.53/0.54    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_38)),
% 1.53/0.54    inference(superposition,[],[f275,f654])).
% 1.53/0.54  fof(f1072,plain,(
% 1.53/0.54    spl6_52 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_21 | ~spl6_25 | ~spl6_38 | ~spl6_39),
% 1.53/0.54    inference(avatar_split_clause,[],[f1067,f658,f652,f547,f349,f112,f107,f102,f1069])).
% 1.53/0.54  fof(f1067,plain,(
% 1.53/0.54    v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_21 | ~spl6_25 | ~spl6_38 | ~spl6_39)),
% 1.53/0.54    inference(forward_demodulation,[],[f689,f660])).
% 1.53/0.54  fof(f689,plain,(
% 1.53/0.54    v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_21 | ~spl6_25 | ~spl6_38)),
% 1.53/0.54    inference(forward_demodulation,[],[f688,f351])).
% 1.53/0.54  fof(f688,plain,(
% 1.53/0.54    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_25 | ~spl6_38)),
% 1.53/0.54    inference(subsumption_resolution,[],[f687,f104])).
% 1.53/0.54  fof(f687,plain,(
% 1.53/0.54    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_3 | ~spl6_25 | ~spl6_38)),
% 1.53/0.54    inference(subsumption_resolution,[],[f686,f548])).
% 1.53/0.54  fof(f686,plain,(
% 1.53/0.54    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_3 | ~spl6_38)),
% 1.53/0.54    inference(subsumption_resolution,[],[f685,f114])).
% 1.53/0.54  fof(f685,plain,(
% 1.53/0.54    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~l1_pre_topc(sK0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_38)),
% 1.53/0.54    inference(subsumption_resolution,[],[f668,f109])).
% 1.53/0.54  fof(f668,plain,(
% 1.53/0.54    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~spl6_38),
% 1.53/0.54    inference(superposition,[],[f91,f654])).
% 1.53/0.54  fof(f91,plain,(
% 1.53/0.54    ( ! [X0,X1] : (v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) )),
% 1.53/0.54    inference(cnf_transformation,[],[f44])).
% 1.53/0.54  fof(f925,plain,(
% 1.53/0.54    spl6_45 | ~spl6_18 | ~spl6_39),
% 1.53/0.54    inference(avatar_split_clause,[],[f709,f658,f310,f922])).
% 1.53/0.54  fof(f709,plain,(
% 1.53/0.54    m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | (~spl6_18 | ~spl6_39)),
% 1.53/0.54    inference(superposition,[],[f311,f660])).
% 1.53/0.54  fof(f869,plain,(
% 1.53/0.54    spl6_44 | ~spl6_24 | ~spl6_42),
% 1.53/0.54    inference(avatar_split_clause,[],[f827,f809,f488,f822])).
% 1.53/0.54  fof(f809,plain,(
% 1.53/0.54    spl6_42 <=> k8_tmap_1(sK0,sK0) = k6_tmap_1(sK0,u1_struct_0(sK0))),
% 1.53/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 1.53/0.54  fof(f827,plain,(
% 1.53/0.54    u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK0)) | (~spl6_24 | ~spl6_42)),
% 1.53/0.54    inference(superposition,[],[f490,f811])).
% 1.53/0.54  fof(f811,plain,(
% 1.53/0.54    k8_tmap_1(sK0,sK0) = k6_tmap_1(sK0,u1_struct_0(sK0)) | ~spl6_42),
% 1.53/0.54    inference(avatar_component_clause,[],[f809])).
% 1.53/0.54  fof(f820,plain,(
% 1.53/0.54    ~spl6_3 | ~spl6_7 | spl6_43),
% 1.53/0.54    inference(avatar_contradiction_clause,[],[f819])).
% 1.53/0.54  fof(f819,plain,(
% 1.53/0.54    $false | (~spl6_3 | ~spl6_7 | spl6_43)),
% 1.53/0.54    inference(subsumption_resolution,[],[f818,f114])).
% 1.53/0.54  fof(f818,plain,(
% 1.53/0.54    ~l1_pre_topc(sK0) | (~spl6_7 | spl6_43)),
% 1.53/0.54    inference(subsumption_resolution,[],[f817,f160])).
% 1.53/0.54  fof(f817,plain,(
% 1.53/0.54    ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | spl6_43),
% 1.53/0.54    inference(resolution,[],[f815,f61])).
% 1.53/0.54  fof(f61,plain,(
% 1.53/0.54    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.53/0.54    inference(cnf_transformation,[],[f22])).
% 1.53/0.54  fof(f22,plain,(
% 1.53/0.54    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.53/0.54    inference(ennf_transformation,[],[f14])).
% 1.53/0.54  fof(f14,axiom,(
% 1.53/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.53/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 1.53/0.54  fof(f815,plain,(
% 1.53/0.54    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | spl6_43),
% 1.53/0.54    inference(avatar_component_clause,[],[f813])).
% 1.53/0.54  fof(f813,plain,(
% 1.53/0.54    spl6_43 <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.53/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).
% 1.53/0.54  fof(f816,plain,(
% 1.53/0.54    spl6_42 | ~spl6_43 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_7 | ~spl6_9 | ~spl6_11 | ~spl6_13),
% 1.53/0.54    inference(avatar_split_clause,[],[f802,f267,f228,f184,f158,f112,f107,f102,f813,f809])).
% 1.53/0.54  fof(f184,plain,(
% 1.53/0.54    spl6_9 <=> v1_pre_topc(k8_tmap_1(sK0,sK0))),
% 1.53/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 1.53/0.54  fof(f228,plain,(
% 1.53/0.54    spl6_11 <=> v2_pre_topc(k8_tmap_1(sK0,sK0))),
% 1.53/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 1.53/0.54  fof(f267,plain,(
% 1.53/0.54    spl6_13 <=> l1_pre_topc(k8_tmap_1(sK0,sK0))),
% 1.53/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 1.53/0.54  fof(f802,plain,(
% 1.53/0.54    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | k8_tmap_1(sK0,sK0) = k6_tmap_1(sK0,u1_struct_0(sK0)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_7 | ~spl6_9 | ~spl6_11 | ~spl6_13)),
% 1.53/0.54    inference(subsumption_resolution,[],[f801,f269])).
% 1.53/0.54  fof(f269,plain,(
% 1.53/0.54    l1_pre_topc(k8_tmap_1(sK0,sK0)) | ~spl6_13),
% 1.53/0.54    inference(avatar_component_clause,[],[f267])).
% 1.53/0.54  fof(f801,plain,(
% 1.53/0.54    ~l1_pre_topc(k8_tmap_1(sK0,sK0)) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | k8_tmap_1(sK0,sK0) = k6_tmap_1(sK0,u1_struct_0(sK0)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_7 | ~spl6_9 | ~spl6_11)),
% 1.53/0.54    inference(subsumption_resolution,[],[f194,f230])).
% 1.53/0.54  fof(f230,plain,(
% 1.53/0.54    v2_pre_topc(k8_tmap_1(sK0,sK0)) | ~spl6_11),
% 1.53/0.54    inference(avatar_component_clause,[],[f228])).
% 1.53/0.54  fof(f194,plain,(
% 1.53/0.54    ~v2_pre_topc(k8_tmap_1(sK0,sK0)) | ~l1_pre_topc(k8_tmap_1(sK0,sK0)) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | k8_tmap_1(sK0,sK0) = k6_tmap_1(sK0,u1_struct_0(sK0)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_7 | ~spl6_9)),
% 1.53/0.54    inference(subsumption_resolution,[],[f193,f104])).
% 1.53/0.54  fof(f193,plain,(
% 1.53/0.54    v2_struct_0(sK0) | ~v2_pre_topc(k8_tmap_1(sK0,sK0)) | ~l1_pre_topc(k8_tmap_1(sK0,sK0)) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | k8_tmap_1(sK0,sK0) = k6_tmap_1(sK0,u1_struct_0(sK0)) | (~spl6_2 | ~spl6_3 | ~spl6_7 | ~spl6_9)),
% 1.53/0.54    inference(subsumption_resolution,[],[f192,f160])).
% 1.53/0.54  fof(f192,plain,(
% 1.53/0.54    ~m1_pre_topc(sK0,sK0) | v2_struct_0(sK0) | ~v2_pre_topc(k8_tmap_1(sK0,sK0)) | ~l1_pre_topc(k8_tmap_1(sK0,sK0)) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | k8_tmap_1(sK0,sK0) = k6_tmap_1(sK0,u1_struct_0(sK0)) | (~spl6_2 | ~spl6_3 | ~spl6_9)),
% 1.53/0.54    inference(subsumption_resolution,[],[f191,f114])).
% 1.53/0.54  fof(f191,plain,(
% 1.53/0.54    ~l1_pre_topc(sK0) | ~m1_pre_topc(sK0,sK0) | v2_struct_0(sK0) | ~v2_pre_topc(k8_tmap_1(sK0,sK0)) | ~l1_pre_topc(k8_tmap_1(sK0,sK0)) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | k8_tmap_1(sK0,sK0) = k6_tmap_1(sK0,u1_struct_0(sK0)) | (~spl6_2 | ~spl6_9)),
% 1.53/0.54    inference(subsumption_resolution,[],[f188,f109])).
% 1.53/0.54  fof(f188,plain,(
% 1.53/0.54    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK0,sK0) | v2_struct_0(sK0) | ~v2_pre_topc(k8_tmap_1(sK0,sK0)) | ~l1_pre_topc(k8_tmap_1(sK0,sK0)) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | k8_tmap_1(sK0,sK0) = k6_tmap_1(sK0,u1_struct_0(sK0)) | ~spl6_9),
% 1.53/0.54    inference(resolution,[],[f186,f96])).
% 1.53/0.54  fof(f96,plain,(
% 1.53/0.54    ( ! [X0,X1] : (~v1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))) )),
% 1.53/0.54    inference(equality_resolution,[],[f95])).
% 1.53/0.54  fof(f95,plain,(
% 1.53/0.54    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k6_tmap_1(X0,u1_struct_0(X1)) = X2 | k8_tmap_1(X0,X1) != X2) )),
% 1.53/0.54    inference(equality_resolution,[],[f67])).
% 1.53/0.54  fof(f67,plain,(
% 1.53/0.54    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X3 | k6_tmap_1(X0,X3) = X2 | k8_tmap_1(X0,X1) != X2) )),
% 1.53/0.54    inference(cnf_transformation,[],[f28])).
% 1.53/0.54  fof(f28,plain,(
% 1.53/0.54    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.53/0.54    inference(flattening,[],[f27])).
% 1.53/0.54  fof(f27,plain,(
% 1.53/0.54    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : ((k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.53/0.54    inference(ennf_transformation,[],[f5])).
% 1.53/0.54  fof(f5,axiom,(
% 1.53/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & v1_pre_topc(X2)) => (k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => k6_tmap_1(X0,X3) = X2))))))),
% 1.53/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_tmap_1)).
% 1.53/0.54  fof(f186,plain,(
% 1.53/0.54    v1_pre_topc(k8_tmap_1(sK0,sK0)) | ~spl6_9),
% 1.53/0.54    inference(avatar_component_clause,[],[f184])).
% 1.53/0.54  fof(f807,plain,(
% 1.53/0.54    spl6_41 | ~spl6_20 | ~spl6_39),
% 1.53/0.54    inference(avatar_split_clause,[],[f710,f658,f318,f804])).
% 1.53/0.54  fof(f710,plain,(
% 1.53/0.54    v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | (~spl6_20 | ~spl6_39)),
% 1.53/0.54    inference(superposition,[],[f319,f660])).
% 1.53/0.54  fof(f707,plain,(
% 1.53/0.54    k8_tmap_1(sK0,sK1) != k6_tmap_1(sK0,u1_struct_0(sK1)) | u1_struct_0(sK0) != u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) | u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))),
% 1.53/0.54    introduced(theory_tautology_sat_conflict,[])).
% 1.53/0.54  fof(f655,plain,(
% 1.53/0.54    spl6_38 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_8 | ~spl6_10 | ~spl6_12 | ~spl6_25),
% 1.53/0.54    inference(avatar_split_clause,[],[f650,f547,f257,f198,f167,f117,f112,f107,f102,f652])).
% 1.53/0.54  fof(f167,plain,(
% 1.53/0.54    spl6_8 <=> v1_pre_topc(k8_tmap_1(sK0,sK1))),
% 1.53/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.53/0.54  fof(f198,plain,(
% 1.53/0.54    spl6_10 <=> v2_pre_topc(k8_tmap_1(sK0,sK1))),
% 1.53/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.53/0.54  fof(f257,plain,(
% 1.53/0.54    spl6_12 <=> l1_pre_topc(k8_tmap_1(sK0,sK1))),
% 1.53/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 1.53/0.54  fof(f650,plain,(
% 1.53/0.54    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_8 | ~spl6_10 | ~spl6_12 | ~spl6_25)),
% 1.53/0.54    inference(subsumption_resolution,[],[f649,f548])).
% 1.53/0.54  fof(f649,plain,(
% 1.53/0.54    ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_8 | ~spl6_10 | ~spl6_12)),
% 1.53/0.54    inference(subsumption_resolution,[],[f648,f259])).
% 1.53/0.54  fof(f259,plain,(
% 1.53/0.54    l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~spl6_12),
% 1.53/0.54    inference(avatar_component_clause,[],[f257])).
% 1.53/0.54  fof(f648,plain,(
% 1.53/0.54    ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_8 | ~spl6_10)),
% 1.53/0.54    inference(subsumption_resolution,[],[f179,f200])).
% 1.53/0.54  fof(f200,plain,(
% 1.53/0.54    v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~spl6_10),
% 1.53/0.54    inference(avatar_component_clause,[],[f198])).
% 1.53/0.54  fof(f179,plain,(
% 1.53/0.54    ~v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_8)),
% 1.53/0.54    inference(subsumption_resolution,[],[f178,f104])).
% 1.53/0.54  fof(f178,plain,(
% 1.53/0.54    v2_struct_0(sK0) | ~v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_8)),
% 1.53/0.54    inference(subsumption_resolution,[],[f177,f119])).
% 1.53/0.54  fof(f177,plain,(
% 1.53/0.54    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | ~v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | (~spl6_2 | ~spl6_3 | ~spl6_8)),
% 1.53/0.54    inference(subsumption_resolution,[],[f176,f114])).
% 1.53/0.54  fof(f176,plain,(
% 1.53/0.54    ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | ~v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | (~spl6_2 | ~spl6_8)),
% 1.53/0.54    inference(subsumption_resolution,[],[f173,f109])).
% 1.53/0.54  fof(f173,plain,(
% 1.53/0.54    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | ~v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~spl6_8),
% 1.53/0.54    inference(resolution,[],[f169,f96])).
% 1.53/0.54  fof(f169,plain,(
% 1.53/0.54    v1_pre_topc(k8_tmap_1(sK0,sK1)) | ~spl6_8),
% 1.53/0.54    inference(avatar_component_clause,[],[f167])).
% 1.53/0.54  fof(f559,plain,(
% 1.53/0.54    ~spl6_3 | ~spl6_4 | spl6_25),
% 1.53/0.54    inference(avatar_contradiction_clause,[],[f558])).
% 1.53/0.54  fof(f558,plain,(
% 1.53/0.54    $false | (~spl6_3 | ~spl6_4 | spl6_25)),
% 1.53/0.54    inference(subsumption_resolution,[],[f557,f114])).
% 1.53/0.54  fof(f557,plain,(
% 1.53/0.54    ~l1_pre_topc(sK0) | (~spl6_4 | spl6_25)),
% 1.53/0.54    inference(subsumption_resolution,[],[f556,f119])).
% 1.53/0.54  fof(f556,plain,(
% 1.53/0.54    ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | spl6_25),
% 1.53/0.54    inference(resolution,[],[f549,f61])).
% 1.53/0.54  fof(f549,plain,(
% 1.53/0.54    ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl6_25),
% 1.53/0.54    inference(avatar_component_clause,[],[f547])).
% 1.53/0.54  fof(f554,plain,(
% 1.53/0.54    ~spl6_25 | spl6_26 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_21),
% 1.53/0.54    inference(avatar_split_clause,[],[f372,f349,f112,f107,f102,f551,f547])).
% 1.53/0.54  fof(f372,plain,(
% 1.53/0.54    v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_21)),
% 1.53/0.54    inference(subsumption_resolution,[],[f371,f104])).
% 1.53/0.54  fof(f371,plain,(
% 1.53/0.54    v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_3 | ~spl6_21)),
% 1.53/0.54    inference(subsumption_resolution,[],[f370,f114])).
% 1.53/0.54  fof(f370,plain,(
% 1.53/0.54    v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_21)),
% 1.53/0.54    inference(subsumption_resolution,[],[f358,f109])).
% 1.53/0.54  fof(f358,plain,(
% 1.53/0.54    v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~spl6_21),
% 1.53/0.54    inference(superposition,[],[f90,f351])).
% 1.53/0.54  fof(f90,plain,(
% 1.53/0.54    ( ! [X0,X1] : (v1_funct_1(k7_tmap_1(X0,X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) )),
% 1.53/0.54    inference(cnf_transformation,[],[f44])).
% 1.53/0.54  fof(f491,plain,(
% 1.53/0.54    spl6_24 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_7),
% 1.53/0.54    inference(avatar_split_clause,[],[f354,f158,f112,f107,f102,f488])).
% 1.53/0.54  fof(f354,plain,(
% 1.53/0.54    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_7)),
% 1.53/0.54    inference(resolution,[],[f236,f160])).
% 1.53/0.54  fof(f236,plain,(
% 1.53/0.54    ( ! [X0] : (~m1_pre_topc(X0,sK0) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0)))) ) | (spl6_1 | ~spl6_2 | ~spl6_3)),
% 1.53/0.54    inference(subsumption_resolution,[],[f232,f114])).
% 1.53/0.54  fof(f232,plain,(
% 1.53/0.54    ( ! [X0] : (u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0))) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3)),
% 1.53/0.54    inference(resolution,[],[f226,f61])).
% 1.53/0.54  fof(f226,plain,(
% 1.53/0.54    ( ! [X5] : (~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X5))) ) | (spl6_1 | ~spl6_2 | ~spl6_3)),
% 1.53/0.54    inference(subsumption_resolution,[],[f136,f114])).
% 1.53/0.54  fof(f136,plain,(
% 1.53/0.54    ( ! [X5] : (~l1_pre_topc(sK0) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X5))) ) | (spl6_1 | ~spl6_2)),
% 1.53/0.54    inference(subsumption_resolution,[],[f125,f104])).
% 1.53/0.54  fof(f125,plain,(
% 1.53/0.54    ( ! [X5] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X5))) ) | ~spl6_2),
% 1.53/0.54    inference(resolution,[],[f109,f76])).
% 1.53/0.54  fof(f76,plain,(
% 1.53/0.54    ( ! [X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) )),
% 1.53/0.54    inference(cnf_transformation,[],[f34])).
% 1.53/0.54  fof(f34,plain,(
% 1.53/0.54    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.53/0.54    inference(flattening,[],[f33])).
% 1.53/0.54  fof(f33,plain,(
% 1.53/0.54    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.53/0.54    inference(ennf_transformation,[],[f11])).
% 1.53/0.54  fof(f11,axiom,(
% 1.53/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 1.53/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).
% 1.53/0.54  fof(f433,plain,(
% 1.53/0.54    spl6_23 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4),
% 1.53/0.54    inference(avatar_split_clause,[],[f353,f117,f112,f107,f102,f430])).
% 1.53/0.54  fof(f353,plain,(
% 1.53/0.54    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4)),
% 1.53/0.54    inference(resolution,[],[f236,f119])).
% 1.53/0.54  fof(f389,plain,(
% 1.53/0.54    spl6_22 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_7),
% 1.53/0.54    inference(avatar_split_clause,[],[f345,f158,f112,f107,f102,f386])).
% 1.53/0.54  fof(f345,plain,(
% 1.53/0.54    k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK0)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_7)),
% 1.53/0.54    inference(resolution,[],[f218,f160])).
% 1.53/0.54  fof(f218,plain,(
% 1.53/0.54    ( ! [X0] : (~m1_pre_topc(X0,sK0) | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(X0))) ) | (spl6_1 | ~spl6_2 | ~spl6_3)),
% 1.53/0.54    inference(subsumption_resolution,[],[f214,f114])).
% 1.53/0.54  fof(f214,plain,(
% 1.53/0.54    ( ! [X0] : (k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3)),
% 1.53/0.54    inference(resolution,[],[f202,f61])).
% 1.53/0.54  fof(f202,plain,(
% 1.53/0.54    ( ! [X4] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | k7_tmap_1(sK0,X4) = k6_partfun1(u1_struct_0(sK0))) ) | (spl6_1 | ~spl6_2 | ~spl6_3)),
% 1.53/0.54    inference(subsumption_resolution,[],[f135,f114])).
% 1.53/0.54  fof(f135,plain,(
% 1.53/0.54    ( ! [X4] : (~l1_pre_topc(sK0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | k7_tmap_1(sK0,X4) = k6_partfun1(u1_struct_0(sK0))) ) | (spl6_1 | ~spl6_2)),
% 1.53/0.54    inference(subsumption_resolution,[],[f124,f104])).
% 1.53/0.54  fof(f124,plain,(
% 1.53/0.54    ( ! [X4] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | k7_tmap_1(sK0,X4) = k6_partfun1(u1_struct_0(sK0))) ) | ~spl6_2),
% 1.53/0.54    inference(resolution,[],[f109,f75])).
% 1.53/0.54  fof(f75,plain,(
% 1.53/0.54    ( ! [X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))) )),
% 1.53/0.54    inference(cnf_transformation,[],[f32])).
% 1.53/0.54  fof(f32,plain,(
% 1.53/0.54    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.53/0.54    inference(flattening,[],[f31])).
% 1.53/0.54  fof(f31,plain,(
% 1.53/0.54    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.53/0.54    inference(ennf_transformation,[],[f4])).
% 1.53/0.54  fof(f4,axiom,(
% 1.53/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))))),
% 1.53/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_tmap_1)).
% 1.53/0.54  fof(f352,plain,(
% 1.53/0.54    spl6_21 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4),
% 1.53/0.54    inference(avatar_split_clause,[],[f344,f117,f112,f107,f102,f349])).
% 1.53/0.54  fof(f344,plain,(
% 1.53/0.54    k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK1)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4)),
% 1.53/0.54    inference(resolution,[],[f218,f119])).
% 1.53/0.54  fof(f343,plain,(
% 1.53/0.54    spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | spl6_18),
% 1.53/0.54    inference(avatar_contradiction_clause,[],[f342])).
% 1.53/0.54  fof(f342,plain,(
% 1.53/0.54    $false | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | spl6_18)),
% 1.53/0.54    inference(subsumption_resolution,[],[f341,f104])).
% 1.53/0.54  fof(f341,plain,(
% 1.53/0.54    v2_struct_0(sK0) | (~spl6_2 | ~spl6_3 | ~spl6_4 | spl6_18)),
% 1.53/0.54    inference(subsumption_resolution,[],[f340,f119])).
% 1.53/0.54  fof(f340,plain,(
% 1.53/0.54    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_3 | spl6_18)),
% 1.53/0.54    inference(subsumption_resolution,[],[f339,f114])).
% 1.53/0.54  fof(f339,plain,(
% 1.53/0.54    ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | (~spl6_2 | spl6_18)),
% 1.53/0.54    inference(subsumption_resolution,[],[f338,f109])).
% 1.53/0.54  fof(f338,plain,(
% 1.53/0.54    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | spl6_18),
% 1.53/0.54    inference(resolution,[],[f312,f89])).
% 1.53/0.54  fof(f89,plain,(
% 1.53/0.54    ( ! [X0,X1] : (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0)) )),
% 1.53/0.54    inference(cnf_transformation,[],[f42])).
% 1.53/0.54  fof(f42,plain,(
% 1.53/0.54    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.53/0.54    inference(flattening,[],[f41])).
% 1.53/0.54  fof(f41,plain,(
% 1.53/0.54    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.53/0.54    inference(ennf_transformation,[],[f10])).
% 1.53/0.54  fof(f10,axiom,(
% 1.53/0.54    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))))),
% 1.53/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_tmap_1)).
% 1.53/0.54  fof(f312,plain,(
% 1.53/0.54    ~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | spl6_18),
% 1.53/0.54    inference(avatar_component_clause,[],[f310])).
% 1.53/0.54  fof(f336,plain,(
% 1.53/0.54    spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | spl6_20),
% 1.53/0.54    inference(avatar_contradiction_clause,[],[f335])).
% 1.53/0.54  fof(f335,plain,(
% 1.53/0.54    $false | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | spl6_20)),
% 1.53/0.54    inference(subsumption_resolution,[],[f334,f104])).
% 1.53/0.54  fof(f334,plain,(
% 1.53/0.54    v2_struct_0(sK0) | (~spl6_2 | ~spl6_3 | ~spl6_4 | spl6_20)),
% 1.53/0.54    inference(subsumption_resolution,[],[f333,f119])).
% 1.53/0.54  fof(f333,plain,(
% 1.53/0.54    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_3 | spl6_20)),
% 1.53/0.54    inference(subsumption_resolution,[],[f332,f114])).
% 1.53/0.54  fof(f332,plain,(
% 1.53/0.54    ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | (~spl6_2 | spl6_20)),
% 1.53/0.54    inference(subsumption_resolution,[],[f331,f109])).
% 1.53/0.54  fof(f331,plain,(
% 1.53/0.54    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | spl6_20),
% 1.53/0.54    inference(resolution,[],[f320,f88])).
% 1.53/0.54  fof(f88,plain,(
% 1.53/0.54    ( ! [X0,X1] : (v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0)) )),
% 1.53/0.54    inference(cnf_transformation,[],[f42])).
% 1.53/0.54  fof(f320,plain,(
% 1.53/0.54    ~v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | spl6_20),
% 1.53/0.54    inference(avatar_component_clause,[],[f318])).
% 1.53/0.54  fof(f328,plain,(
% 1.53/0.54    spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | spl6_17),
% 1.53/0.54    inference(avatar_contradiction_clause,[],[f327])).
% 1.53/0.54  fof(f327,plain,(
% 1.53/0.54    $false | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | spl6_17)),
% 1.53/0.54    inference(subsumption_resolution,[],[f326,f104])).
% 1.53/0.54  fof(f326,plain,(
% 1.53/0.54    v2_struct_0(sK0) | (~spl6_2 | ~spl6_3 | ~spl6_4 | spl6_17)),
% 1.53/0.54    inference(subsumption_resolution,[],[f325,f119])).
% 1.53/0.54  fof(f325,plain,(
% 1.53/0.54    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_3 | spl6_17)),
% 1.53/0.54    inference(subsumption_resolution,[],[f324,f114])).
% 1.53/0.54  fof(f324,plain,(
% 1.53/0.54    ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | (~spl6_2 | spl6_17)),
% 1.53/0.54    inference(subsumption_resolution,[],[f323,f109])).
% 1.53/0.54  fof(f323,plain,(
% 1.53/0.54    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | spl6_17),
% 1.53/0.54    inference(resolution,[],[f308,f87])).
% 1.53/0.54  fof(f87,plain,(
% 1.53/0.54    ( ! [X0,X1] : (v1_funct_1(k9_tmap_1(X0,X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0)) )),
% 1.53/0.54    inference(cnf_transformation,[],[f42])).
% 1.53/0.54  fof(f308,plain,(
% 1.53/0.54    ~v1_funct_1(k9_tmap_1(sK0,sK1)) | spl6_17),
% 1.53/0.54    inference(avatar_component_clause,[],[f306])).
% 1.53/0.54  fof(f321,plain,(
% 1.53/0.54    ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | spl6_6),
% 1.53/0.54    inference(avatar_split_clause,[],[f304,f153,f318,f314,f310,f306])).
% 1.53/0.54  fof(f314,plain,(
% 1.53/0.54    spl6_19 <=> v5_pre_topc(k9_tmap_1(sK0,sK1),sK0,k8_tmap_1(sK0,sK1))),
% 1.53/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 1.53/0.54  fof(f304,plain,(
% 1.53/0.54    ~v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v5_pre_topc(k9_tmap_1(sK0,sK1),sK0,k8_tmap_1(sK0,sK1)) | ~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~v1_funct_1(k9_tmap_1(sK0,sK1)) | spl6_6),
% 1.53/0.54    inference(resolution,[],[f154,f47])).
% 1.53/0.54  fof(f47,plain,(
% 1.53/0.54    ( ! [X0,X1] : (sP2(X1,X0) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) | ~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_1(k9_tmap_1(X0,X1))) )),
% 1.53/0.54    inference(cnf_transformation,[],[f19])).
% 1.53/0.54  fof(f154,plain,(
% 1.53/0.54    ~sP2(sK1,sK0) | spl6_6),
% 1.53/0.54    inference(avatar_component_clause,[],[f153])).
% 1.53/0.54  fof(f302,plain,(
% 1.53/0.54    ~spl6_5 | ~spl6_6),
% 1.53/0.54    inference(avatar_contradiction_clause,[],[f301])).
% 1.53/0.54  fof(f301,plain,(
% 1.53/0.54    $false | (~spl6_5 | ~spl6_6)),
% 1.53/0.54    inference(subsumption_resolution,[],[f300,f151])).
% 1.53/0.54  fof(f300,plain,(
% 1.53/0.54    ~v1_tsep_1(sK1,sK0) | ~spl6_6),
% 1.53/0.54    inference(subsumption_resolution,[],[f100,f155])).
% 1.53/0.54  fof(f100,plain,(
% 1.53/0.54    ~sP2(sK1,sK0) | ~v1_tsep_1(sK1,sK0)),
% 1.53/0.54    inference(global_subsumption,[],[f99,f52])).
% 1.53/0.54  fof(f52,plain,(
% 1.53/0.54    ~sP2(sK1,sK0) | ~v1_tsep_1(sK1,sK0) | ~m1_pre_topc(sK1,sK0)),
% 1.53/0.54    inference(cnf_transformation,[],[f19])).
% 1.53/0.54  fof(f99,plain,(
% 1.53/0.54    m1_pre_topc(sK1,sK0)),
% 1.53/0.54    inference(global_subsumption,[],[f55])).
% 1.53/0.54  fof(f55,plain,(
% 1.53/0.54    m1_pre_topc(sK1,sK0)),
% 1.53/0.54    inference(cnf_transformation,[],[f19])).
% 1.53/0.54  fof(f299,plain,(
% 1.53/0.54    spl6_16 | ~spl6_3 | ~spl6_4 | spl6_5),
% 1.53/0.54    inference(avatar_split_clause,[],[f196,f149,f117,f112,f296])).
% 1.53/0.54  fof(f196,plain,(
% 1.53/0.54    u1_struct_0(sK1) = sK3(sK0,sK1) | (~spl6_3 | ~spl6_4 | spl6_5)),
% 1.53/0.54    inference(subsumption_resolution,[],[f195,f119])).
% 1.53/0.54  fof(f195,plain,(
% 1.53/0.54    u1_struct_0(sK1) = sK3(sK0,sK1) | ~m1_pre_topc(sK1,sK0) | (~spl6_3 | spl6_5)),
% 1.53/0.54    inference(resolution,[],[f145,f150])).
% 1.53/0.54  fof(f145,plain,(
% 1.53/0.54    ( ! [X1] : (v1_tsep_1(X1,sK0) | u1_struct_0(X1) = sK3(sK0,X1) | ~m1_pre_topc(X1,sK0)) ) | ~spl6_3),
% 1.53/0.54    inference(resolution,[],[f114,f64])).
% 1.53/0.54  fof(f64,plain,(
% 1.53/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | u1_struct_0(X1) = sK3(X0,X1) | v1_tsep_1(X1,X0)) )),
% 1.53/0.54    inference(cnf_transformation,[],[f24])).
% 1.53/0.54  fof(f270,plain,(
% 1.53/0.54    spl6_13 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_7),
% 1.53/0.54    inference(avatar_split_clause,[],[f182,f158,f112,f107,f102,f267])).
% 1.53/0.54  fof(f182,plain,(
% 1.53/0.54    l1_pre_topc(k8_tmap_1(sK0,sK0)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_7)),
% 1.53/0.54    inference(resolution,[],[f180,f160])).
% 1.53/0.54  fof(f180,plain,(
% 1.53/0.54    ( ! [X11] : (~m1_pre_topc(X11,sK0) | l1_pre_topc(k8_tmap_1(sK0,X11))) ) | (spl6_1 | ~spl6_2 | ~spl6_3)),
% 1.53/0.54    inference(subsumption_resolution,[],[f142,f114])).
% 1.53/0.54  fof(f142,plain,(
% 1.53/0.54    ( ! [X11] : (~l1_pre_topc(sK0) | ~m1_pre_topc(X11,sK0) | l1_pre_topc(k8_tmap_1(sK0,X11))) ) | (spl6_1 | ~spl6_2)),
% 1.53/0.54    inference(subsumption_resolution,[],[f131,f104])).
% 1.53/0.54  fof(f131,plain,(
% 1.53/0.54    ( ! [X11] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(X11,sK0) | l1_pre_topc(k8_tmap_1(sK0,X11))) ) | ~spl6_2),
% 1.53/0.54    inference(resolution,[],[f109,f86])).
% 1.53/0.54  fof(f86,plain,(
% 1.53/0.54    ( ! [X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(k8_tmap_1(X0,X1))) )),
% 1.53/0.54    inference(cnf_transformation,[],[f40])).
% 1.53/0.54  fof(f40,plain,(
% 1.53/0.54    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.53/0.54    inference(flattening,[],[f39])).
% 1.53/0.54  fof(f39,plain,(
% 1.53/0.54    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.53/0.54    inference(ennf_transformation,[],[f9])).
% 1.53/0.54  fof(f9,axiom,(
% 1.53/0.54    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 1.53/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_tmap_1)).
% 1.53/0.54  fof(f260,plain,(
% 1.53/0.54    spl6_12 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4),
% 1.53/0.54    inference(avatar_split_clause,[],[f181,f117,f112,f107,f102,f257])).
% 1.53/0.54  fof(f181,plain,(
% 1.53/0.54    l1_pre_topc(k8_tmap_1(sK0,sK1)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4)),
% 1.53/0.54    inference(resolution,[],[f180,f119])).
% 1.53/0.54  fof(f231,plain,(
% 1.53/0.54    spl6_11 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_7),
% 1.53/0.54    inference(avatar_split_clause,[],[f172,f158,f112,f107,f102,f228])).
% 1.53/0.54  fof(f172,plain,(
% 1.53/0.54    v2_pre_topc(k8_tmap_1(sK0,sK0)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_7)),
% 1.53/0.54    inference(resolution,[],[f165,f160])).
% 1.53/0.54  fof(f165,plain,(
% 1.53/0.54    ( ! [X10] : (~m1_pre_topc(X10,sK0) | v2_pre_topc(k8_tmap_1(sK0,X10))) ) | (spl6_1 | ~spl6_2 | ~spl6_3)),
% 1.53/0.54    inference(subsumption_resolution,[],[f141,f114])).
% 1.53/0.54  fof(f141,plain,(
% 1.53/0.54    ( ! [X10] : (~l1_pre_topc(sK0) | ~m1_pre_topc(X10,sK0) | v2_pre_topc(k8_tmap_1(sK0,X10))) ) | (spl6_1 | ~spl6_2)),
% 1.53/0.54    inference(subsumption_resolution,[],[f130,f104])).
% 1.53/0.54  fof(f130,plain,(
% 1.53/0.54    ( ! [X10] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(X10,sK0) | v2_pre_topc(k8_tmap_1(sK0,X10))) ) | ~spl6_2),
% 1.53/0.54    inference(resolution,[],[f109,f85])).
% 1.53/0.54  fof(f85,plain,(
% 1.53/0.54    ( ! [X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_pre_topc(k8_tmap_1(X0,X1))) )),
% 1.53/0.54    inference(cnf_transformation,[],[f40])).
% 1.53/0.54  fof(f201,plain,(
% 1.53/0.54    spl6_10 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4),
% 1.53/0.54    inference(avatar_split_clause,[],[f171,f117,f112,f107,f102,f198])).
% 1.53/0.54  fof(f171,plain,(
% 1.53/0.54    v2_pre_topc(k8_tmap_1(sK0,sK1)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4)),
% 1.53/0.54    inference(resolution,[],[f165,f119])).
% 1.53/0.54  fof(f187,plain,(
% 1.53/0.54    spl6_9 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_7),
% 1.53/0.54    inference(avatar_split_clause,[],[f164,f158,f112,f107,f102,f184])).
% 1.53/0.54  fof(f164,plain,(
% 1.53/0.54    v1_pre_topc(k8_tmap_1(sK0,sK0)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_7)),
% 1.53/0.54    inference(resolution,[],[f162,f160])).
% 1.53/0.54  fof(f162,plain,(
% 1.53/0.54    ( ! [X9] : (~m1_pre_topc(X9,sK0) | v1_pre_topc(k8_tmap_1(sK0,X9))) ) | (spl6_1 | ~spl6_2 | ~spl6_3)),
% 1.53/0.54    inference(subsumption_resolution,[],[f140,f114])).
% 1.53/0.54  fof(f140,plain,(
% 1.53/0.54    ( ! [X9] : (~l1_pre_topc(sK0) | ~m1_pre_topc(X9,sK0) | v1_pre_topc(k8_tmap_1(sK0,X9))) ) | (spl6_1 | ~spl6_2)),
% 1.53/0.54    inference(subsumption_resolution,[],[f129,f104])).
% 1.53/0.54  fof(f129,plain,(
% 1.53/0.54    ( ! [X9] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(X9,sK0) | v1_pre_topc(k8_tmap_1(sK0,X9))) ) | ~spl6_2),
% 1.53/0.54    inference(resolution,[],[f109,f84])).
% 1.53/0.54  fof(f84,plain,(
% 1.53/0.54    ( ! [X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v1_pre_topc(k8_tmap_1(X0,X1))) )),
% 1.53/0.54    inference(cnf_transformation,[],[f40])).
% 1.53/0.54  fof(f170,plain,(
% 1.53/0.54    spl6_8 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4),
% 1.53/0.54    inference(avatar_split_clause,[],[f163,f117,f112,f107,f102,f167])).
% 1.53/0.54  fof(f163,plain,(
% 1.53/0.54    v1_pre_topc(k8_tmap_1(sK0,sK1)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4)),
% 1.53/0.54    inference(resolution,[],[f162,f119])).
% 1.53/0.54  fof(f161,plain,(
% 1.53/0.54    spl6_7 | ~spl6_3),
% 1.53/0.54    inference(avatar_split_clause,[],[f147,f112,f158])).
% 1.53/0.54  fof(f147,plain,(
% 1.53/0.54    m1_pre_topc(sK0,sK0) | ~spl6_3),
% 1.53/0.54    inference(resolution,[],[f114,f60])).
% 1.53/0.54  fof(f60,plain,(
% 1.53/0.54    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 1.53/0.54    inference(cnf_transformation,[],[f21])).
% 1.53/0.54  fof(f21,plain,(
% 1.53/0.54    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 1.53/0.54    inference(ennf_transformation,[],[f15])).
% 1.53/0.54  fof(f15,axiom,(
% 1.53/0.54    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 1.53/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 1.53/0.54  fof(f156,plain,(
% 1.53/0.54    spl6_5 | spl6_6),
% 1.53/0.54    inference(avatar_split_clause,[],[f53,f153,f149])).
% 1.53/0.54  fof(f53,plain,(
% 1.53/0.54    sP2(sK1,sK0) | v1_tsep_1(sK1,sK0)),
% 1.53/0.54    inference(cnf_transformation,[],[f19])).
% 1.53/0.54  fof(f121,plain,(
% 1.53/0.54    spl6_4),
% 1.53/0.54    inference(avatar_split_clause,[],[f99,f117])).
% 1.53/0.54  fof(f115,plain,(
% 1.53/0.54    spl6_3),
% 1.53/0.54    inference(avatar_split_clause,[],[f58,f112])).
% 1.53/0.54  fof(f58,plain,(
% 1.53/0.54    l1_pre_topc(sK0)),
% 1.53/0.54    inference(cnf_transformation,[],[f19])).
% 1.53/0.54  fof(f110,plain,(
% 1.53/0.54    spl6_2),
% 1.53/0.54    inference(avatar_split_clause,[],[f57,f107])).
% 1.53/0.54  fof(f57,plain,(
% 1.53/0.54    v2_pre_topc(sK0)),
% 1.53/0.54    inference(cnf_transformation,[],[f19])).
% 1.53/0.54  fof(f105,plain,(
% 1.53/0.54    ~spl6_1),
% 1.53/0.54    inference(avatar_split_clause,[],[f56,f102])).
% 1.53/0.54  fof(f56,plain,(
% 1.53/0.54    ~v2_struct_0(sK0)),
% 1.53/0.54    inference(cnf_transformation,[],[f19])).
% 1.53/0.54  % SZS output end Proof for theBenchmark
% 1.53/0.54  % (9421)------------------------------
% 1.53/0.54  % (9421)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.54  % (9421)Termination reason: Refutation
% 1.53/0.54  
% 1.53/0.54  % (9421)Memory used [KB]: 11769
% 1.53/0.55  % (9421)Time elapsed: 0.119 s
% 1.53/0.55  % (9421)------------------------------
% 1.53/0.55  % (9421)------------------------------
% 1.53/0.55  % (9417)Success in time 0.196 s
%------------------------------------------------------------------------------
