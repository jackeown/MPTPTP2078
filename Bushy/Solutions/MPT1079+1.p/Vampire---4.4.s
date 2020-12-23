%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t196_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:40 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  232 ( 657 expanded)
%              Number of leaves         :   36 ( 272 expanded)
%              Depth                    :   23
%              Number of atoms          : 1424 (2826 expanded)
%              Number of equality atoms :   89 ( 198 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f549,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f112,f116,f120,f124,f128,f138,f152,f237,f242,f248,f252,f256,f261,f265,f270,f274,f278,f283,f287,f315,f337,f391,f531,f543,f548])).

fof(f548,plain,
    ( spl8_3
    | spl8_5
    | ~ spl8_114 ),
    inference(avatar_contradiction_clause,[],[f547])).

fof(f547,plain,
    ( $false
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_114 ),
    inference(subsumption_resolution,[],[f546,f119])).

fof(f119,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl8_5
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f546,plain,
    ( v1_xboole_0(sK1)
    | ~ spl8_3
    | ~ spl8_114 ),
    inference(subsumption_resolution,[],[f544,f115])).

fof(f115,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl8_3
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f544,plain,
    ( v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | ~ spl8_114 ),
    inference(resolution,[],[f530,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t196_funct_2.p',fc10_subset_1)).

fof(f530,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK1,sK2))
    | ~ spl8_114 ),
    inference(avatar_component_clause,[],[f529])).

fof(f529,plain,
    ( spl8_114
  <=> v1_xboole_0(k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_114])])).

fof(f543,plain,
    ( ~ spl8_0
    | spl8_3
    | spl8_5
    | spl8_7
    | ~ spl8_8
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_22
    | spl8_25
    | ~ spl8_28
    | ~ spl8_32
    | ~ spl8_34
    | ~ spl8_38
    | ~ spl8_40
    | ~ spl8_42
    | ~ spl8_50
    | ~ spl8_112 ),
    inference(avatar_contradiction_clause,[],[f542])).

fof(f542,plain,
    ( $false
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_22
    | ~ spl8_25
    | ~ spl8_28
    | ~ spl8_32
    | ~ spl8_34
    | ~ spl8_38
    | ~ spl8_40
    | ~ spl8_42
    | ~ spl8_50
    | ~ spl8_112 ),
    inference(subsumption_resolution,[],[f541,f251])).

fof(f251,plain,
    ( k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4) != k4_tarski(k3_funct_2(sK0,sK1,k15_mcart_1(sK3),sK4),k3_funct_2(sK0,sK2,k16_mcart_1(sK3),sK4))
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f250])).

fof(f250,plain,
    ( spl8_25
  <=> k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4) != k4_tarski(k3_funct_2(sK0,sK1,k15_mcart_1(sK3),sK4),k3_funct_2(sK0,sK2,k16_mcart_1(sK3),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f541,plain,
    ( k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4) = k4_tarski(k3_funct_2(sK0,sK1,k15_mcart_1(sK3),sK4),k3_funct_2(sK0,sK2,k16_mcart_1(sK3),sK4))
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_22
    | ~ spl8_28
    | ~ spl8_32
    | ~ spl8_34
    | ~ spl8_38
    | ~ spl8_40
    | ~ spl8_42
    | ~ spl8_50
    | ~ spl8_112 ),
    inference(forward_demodulation,[],[f540,f457])).

fof(f457,plain,
    ( k3_funct_2(sK0,sK1,k15_mcart_1(sK3),sK4) = k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4))
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_28
    | ~ spl8_38
    | ~ spl8_40
    | ~ spl8_50 ),
    inference(resolution,[],[f339,f127])).

fof(f127,plain,
    ( m1_subset_1(sK4,sK0)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl8_8
  <=> m1_subset_1(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f339,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK1,k15_mcart_1(sK3),X0) = k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) )
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_28
    | ~ spl8_38
    | ~ spl8_40
    | ~ spl8_50 ),
    inference(subsumption_resolution,[],[f311,f338])).

fof(f338,plain,
    ( m1_subset_1(k15_mcart_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_40
    | ~ spl8_50 ),
    inference(forward_demodulation,[],[f336,f286])).

fof(f286,plain,
    ( k4_funct_2(sK0,sK1,sK2,sK3) = k15_mcart_1(sK3)
    | ~ spl8_40 ),
    inference(avatar_component_clause,[],[f285])).

fof(f285,plain,
    ( spl8_40
  <=> k4_funct_2(sK0,sK1,sK2,sK3) = k15_mcart_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f336,plain,
    ( m1_subset_1(k4_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_50 ),
    inference(avatar_component_clause,[],[f335])).

fof(f335,plain,
    ( spl8_50
  <=> m1_subset_1(k4_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).

fof(f311,plain,
    ( ! [X0] :
        ( k3_funct_2(sK0,sK1,k15_mcart_1(sK3),X0) = k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0))
        | ~ m1_subset_1(k15_mcart_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_28
    | ~ spl8_38
    | ~ spl8_40 ),
    inference(forward_demodulation,[],[f310,f286])).

fof(f310,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k15_mcart_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),X0) = k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) )
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_28
    | ~ spl8_38
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f309,f282])).

fof(f282,plain,
    ( v1_funct_2(k15_mcart_1(sK3),sK0,sK1)
    | ~ spl8_38 ),
    inference(avatar_component_clause,[],[f281])).

fof(f281,plain,
    ( spl8_38
  <=> v1_funct_2(k15_mcart_1(sK3),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f309,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k15_mcart_1(sK3),sK0,sK1)
        | ~ m1_subset_1(k15_mcart_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),X0) = k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) )
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_28
    | ~ spl8_40 ),
    inference(forward_demodulation,[],[f308,f286])).

fof(f308,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k15_mcart_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(k4_funct_2(sK0,sK1,sK2,sK3),sK0,sK1)
        | ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),X0) = k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) )
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_28
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f307,f260])).

fof(f260,plain,
    ( v1_funct_1(k15_mcart_1(sK3))
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f259])).

fof(f259,plain,
    ( spl8_28
  <=> v1_funct_1(k15_mcart_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f307,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k15_mcart_1(sK3))
        | ~ m1_subset_1(k15_mcart_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(k4_funct_2(sK0,sK1,sK2,sK3),sK0,sK1)
        | ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),X0) = k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) )
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_40 ),
    inference(forward_demodulation,[],[f306,f286])).

fof(f306,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k15_mcart_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(k4_funct_2(sK0,sK1,sK2,sK3))
        | ~ v1_funct_2(k4_funct_2(sK0,sK1,sK2,sK3),sK0,sK1)
        | ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),X0) = k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) )
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f305,f123])).

fof(f123,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl8_7
  <=> ~ v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f305,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k15_mcart_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(k4_funct_2(sK0,sK1,sK2,sK3))
        | ~ v1_funct_2(k4_funct_2(sK0,sK1,sK2,sK3),sK0,sK1)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),X0) = k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) )
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f304,f151])).

fof(f151,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2))))
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl8_16
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f304,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k15_mcart_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2))))
        | ~ v1_funct_1(k4_funct_2(sK0,sK1,sK2,sK3))
        | ~ v1_funct_2(k4_funct_2(sK0,sK1,sK2,sK3),sK0,sK1)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),X0) = k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) )
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_12
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f303,f137])).

fof(f137,plain,
    ( v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl8_12
  <=> v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f303,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k15_mcart_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2))))
        | ~ v1_funct_1(k4_funct_2(sK0,sK1,sK2,sK3))
        | ~ v1_funct_2(k4_funct_2(sK0,sK1,sK2,sK3),sK0,sK1)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),X0) = k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) )
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f302,f111])).

fof(f111,plain,
    ( v1_funct_1(sK3)
    | ~ spl8_0 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl8_0
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_0])])).

fof(f302,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k15_mcart_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2))))
        | ~ v1_funct_1(k4_funct_2(sK0,sK1,sK2,sK3))
        | ~ v1_funct_2(k4_funct_2(sK0,sK1,sK2,sK3),sK0,sK1)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),X0) = k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) )
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f301,f115])).

fof(f301,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k15_mcart_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | v1_xboole_0(sK2)
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2))))
        | ~ v1_funct_1(k4_funct_2(sK0,sK1,sK2,sK3))
        | ~ v1_funct_2(k4_funct_2(sK0,sK1,sK2,sK3),sK0,sK1)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),X0) = k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) )
    | ~ spl8_5
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f300,f119])).

fof(f300,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k15_mcart_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | v1_xboole_0(sK1)
        | v1_xboole_0(sK2)
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2))))
        | ~ v1_funct_1(k4_funct_2(sK0,sK1,sK2,sK3))
        | ~ v1_funct_2(k4_funct_2(sK0,sK1,sK2,sK3),sK0,sK1)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),X0) = k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) )
    | ~ spl8_40 ),
    inference(superposition,[],[f108,f286])).

fof(f108,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(k4_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_1(k4_funct_2(X0,X1,X2,X3))
      | ~ v1_funct_2(k4_funct_2(X0,X1,X2,X3),X0,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X5,X0)
      | k3_funct_2(X0,X1,k4_funct_2(X0,X1,X2,X3),X5) = k1_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5)) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X0,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X5,X0)
      | k3_funct_2(X0,X1,X4,X5) = k1_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5))
      | k4_funct_2(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( k4_funct_2(X0,X1,X2,X3) = X4
                      <=> ! [X5] :
                            ( k3_funct_2(X0,X1,X4,X5) = k1_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5))
                            | ~ m1_subset_1(X5,X0) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      | ~ v1_funct_2(X4,X0,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                  | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                  | ~ v1_funct_1(X3) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( k4_funct_2(X0,X1,X2,X3) = X4
                      <=> ! [X5] :
                            ( k3_funct_2(X0,X1,X4,X5) = k1_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5))
                            | ~ m1_subset_1(X5,X0) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      | ~ v1_funct_2(X4,X0,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                  | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                  | ~ v1_funct_1(X3) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                    & v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                        & v1_funct_2(X4,X0,X1)
                        & v1_funct_1(X4) )
                     => ( k4_funct_2(X0,X1,X2,X3) = X4
                      <=> ! [X5] :
                            ( m1_subset_1(X5,X0)
                           => k3_funct_2(X0,X1,X4,X5) = k1_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t196_funct_2.p',d6_funct_2)).

fof(f540,plain,
    ( k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4) = k4_tarski(k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4)),k3_funct_2(sK0,sK2,k16_mcart_1(sK3),sK4))
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_22
    | ~ spl8_32
    | ~ spl8_34
    | ~ spl8_42
    | ~ spl8_112 ),
    inference(forward_demodulation,[],[f539,f451])).

fof(f451,plain,
    ( k3_funct_2(sK0,sK2,k16_mcart_1(sK3),sK4) = k2_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4))
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_22
    | ~ spl8_32
    | ~ spl8_34
    | ~ spl8_42 ),
    inference(resolution,[],[f317,f127])).

fof(f317,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK2,k16_mcart_1(sK3),X0) = k2_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) )
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_22
    | ~ spl8_32
    | ~ spl8_34
    | ~ spl8_42 ),
    inference(subsumption_resolution,[],[f299,f316])).

fof(f316,plain,
    ( m1_subset_1(k16_mcart_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl8_34
    | ~ spl8_42 ),
    inference(forward_demodulation,[],[f314,f273])).

fof(f273,plain,
    ( k5_funct_2(sK0,sK1,sK2,sK3) = k16_mcart_1(sK3)
    | ~ spl8_34 ),
    inference(avatar_component_clause,[],[f272])).

fof(f272,plain,
    ( spl8_34
  <=> k5_funct_2(sK0,sK1,sK2,sK3) = k16_mcart_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f314,plain,
    ( m1_subset_1(k5_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl8_42 ),
    inference(avatar_component_clause,[],[f313])).

fof(f313,plain,
    ( spl8_42
  <=> m1_subset_1(k5_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).

fof(f299,plain,
    ( ! [X0] :
        ( k3_funct_2(sK0,sK2,k16_mcart_1(sK3),X0) = k2_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0))
        | ~ m1_subset_1(k16_mcart_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_22
    | ~ spl8_32
    | ~ spl8_34 ),
    inference(forward_demodulation,[],[f298,f273])).

fof(f298,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k16_mcart_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        | ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),X0) = k2_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) )
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_22
    | ~ spl8_32
    | ~ spl8_34 ),
    inference(subsumption_resolution,[],[f297,f269])).

fof(f269,plain,
    ( v1_funct_2(k16_mcart_1(sK3),sK0,sK2)
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f268])).

fof(f268,plain,
    ( spl8_32
  <=> v1_funct_2(k16_mcart_1(sK3),sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f297,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k16_mcart_1(sK3),sK0,sK2)
        | ~ m1_subset_1(k16_mcart_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        | ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),X0) = k2_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) )
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_22
    | ~ spl8_34 ),
    inference(forward_demodulation,[],[f296,f273])).

fof(f296,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k16_mcart_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        | ~ v1_funct_2(k5_funct_2(sK0,sK1,sK2,sK3),sK0,sK2)
        | ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),X0) = k2_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) )
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_22
    | ~ spl8_34 ),
    inference(subsumption_resolution,[],[f295,f247])).

fof(f247,plain,
    ( v1_funct_1(k16_mcart_1(sK3))
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f246])).

fof(f246,plain,
    ( spl8_22
  <=> v1_funct_1(k16_mcart_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f295,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k16_mcart_1(sK3))
        | ~ m1_subset_1(k16_mcart_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        | ~ v1_funct_2(k5_funct_2(sK0,sK1,sK2,sK3),sK0,sK2)
        | ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),X0) = k2_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) )
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_34 ),
    inference(forward_demodulation,[],[f294,f273])).

fof(f294,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k16_mcart_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        | ~ v1_funct_1(k5_funct_2(sK0,sK1,sK2,sK3))
        | ~ v1_funct_2(k5_funct_2(sK0,sK1,sK2,sK3),sK0,sK2)
        | ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),X0) = k2_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) )
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_34 ),
    inference(subsumption_resolution,[],[f293,f123])).

fof(f293,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k16_mcart_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        | ~ v1_funct_1(k5_funct_2(sK0,sK1,sK2,sK3))
        | ~ v1_funct_2(k5_funct_2(sK0,sK1,sK2,sK3),sK0,sK2)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),X0) = k2_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) )
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_34 ),
    inference(subsumption_resolution,[],[f292,f151])).

fof(f292,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k16_mcart_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2))))
        | ~ v1_funct_1(k5_funct_2(sK0,sK1,sK2,sK3))
        | ~ v1_funct_2(k5_funct_2(sK0,sK1,sK2,sK3),sK0,sK2)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),X0) = k2_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) )
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_12
    | ~ spl8_34 ),
    inference(subsumption_resolution,[],[f291,f137])).

fof(f291,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k16_mcart_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2))))
        | ~ v1_funct_1(k5_funct_2(sK0,sK1,sK2,sK3))
        | ~ v1_funct_2(k5_funct_2(sK0,sK1,sK2,sK3),sK0,sK2)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),X0) = k2_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) )
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_34 ),
    inference(subsumption_resolution,[],[f290,f111])).

fof(f290,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k16_mcart_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2))))
        | ~ v1_funct_1(k5_funct_2(sK0,sK1,sK2,sK3))
        | ~ v1_funct_2(k5_funct_2(sK0,sK1,sK2,sK3),sK0,sK2)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),X0) = k2_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) )
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_34 ),
    inference(subsumption_resolution,[],[f289,f115])).

fof(f289,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k16_mcart_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        | v1_xboole_0(sK2)
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2))))
        | ~ v1_funct_1(k5_funct_2(sK0,sK1,sK2,sK3))
        | ~ v1_funct_2(k5_funct_2(sK0,sK1,sK2,sK3),sK0,sK2)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),X0) = k2_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) )
    | ~ spl8_5
    | ~ spl8_34 ),
    inference(subsumption_resolution,[],[f288,f119])).

fof(f288,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k16_mcart_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        | v1_xboole_0(sK1)
        | v1_xboole_0(sK2)
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2))))
        | ~ v1_funct_1(k5_funct_2(sK0,sK1,sK2,sK3))
        | ~ v1_funct_2(k5_funct_2(sK0,sK1,sK2,sK3),sK0,sK2)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),X0) = k2_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) )
    | ~ spl8_34 ),
    inference(superposition,[],[f107,f273])).

fof(f107,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(k5_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_1(k5_funct_2(X0,X1,X2,X3))
      | ~ v1_funct_2(k5_funct_2(X0,X1,X2,X3),X0,X2)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X5,X0)
      | k3_funct_2(X0,X2,k5_funct_2(X0,X1,X2,X3),X5) = k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5)) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X0,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ m1_subset_1(X5,X0)
      | k3_funct_2(X0,X2,X4,X5) = k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5))
      | k5_funct_2(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( k5_funct_2(X0,X1,X2,X3) = X4
                      <=> ! [X5] :
                            ( k3_funct_2(X0,X2,X4,X5) = k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5))
                            | ~ m1_subset_1(X5,X0) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                      | ~ v1_funct_2(X4,X0,X2)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                  | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                  | ~ v1_funct_1(X3) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( k5_funct_2(X0,X1,X2,X3) = X4
                      <=> ! [X5] :
                            ( k3_funct_2(X0,X2,X4,X5) = k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5))
                            | ~ m1_subset_1(X5,X0) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                      | ~ v1_funct_2(X4,X0,X2)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                  | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                  | ~ v1_funct_1(X3) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                    & v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                        & v1_funct_2(X4,X0,X2)
                        & v1_funct_1(X4) )
                     => ( k5_funct_2(X0,X1,X2,X3) = X4
                      <=> ! [X5] :
                            ( m1_subset_1(X5,X0)
                           => k3_funct_2(X0,X2,X4,X5) = k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t196_funct_2.p',d7_funct_2)).

fof(f539,plain,
    ( k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4) = k4_tarski(k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4)),k2_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4)))
    | ~ spl8_112 ),
    inference(subsumption_resolution,[],[f537,f102])).

fof(f102,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t196_funct_2.p',fc6_relat_1)).

fof(f537,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4) = k4_tarski(k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4)),k2_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4)))
    | ~ spl8_112 ),
    inference(resolution,[],[f527,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1)
      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t196_funct_2.p',t23_mcart_1)).

fof(f527,plain,
    ( r2_hidden(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4),k2_zfmisc_1(sK1,sK2))
    | ~ spl8_112 ),
    inference(avatar_component_clause,[],[f526])).

fof(f526,plain,
    ( spl8_112
  <=> r2_hidden(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4),k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_112])])).

fof(f531,plain,
    ( spl8_112
    | spl8_114
    | ~ spl8_62 ),
    inference(avatar_split_clause,[],[f398,f389,f529,f526])).

fof(f389,plain,
    ( spl8_62
  <=> m1_subset_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4),k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_62])])).

fof(f398,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK1,sK2))
    | r2_hidden(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4),k2_zfmisc_1(sK1,sK2))
    | ~ spl8_62 ),
    inference(resolution,[],[f390,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t196_funct_2.p',t2_subset)).

fof(f390,plain,
    ( m1_subset_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4),k2_zfmisc_1(sK1,sK2))
    | ~ spl8_62 ),
    inference(avatar_component_clause,[],[f389])).

fof(f391,plain,
    ( spl8_62
    | ~ spl8_0
    | spl8_7
    | ~ spl8_8
    | ~ spl8_12
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f349,f150,f136,f126,f122,f110,f389])).

fof(f349,plain,
    ( m1_subset_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4),k2_zfmisc_1(sK1,sK2))
    | ~ spl8_0
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_12
    | ~ spl8_16 ),
    inference(resolution,[],[f233,f127])).

fof(f233,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,sK0)
        | m1_subset_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X4),k2_zfmisc_1(sK1,sK2)) )
    | ~ spl8_0
    | ~ spl8_7
    | ~ spl8_12
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f232,f123])).

fof(f232,plain,
    ( ! [X4] :
        ( v1_xboole_0(sK0)
        | ~ m1_subset_1(X4,sK0)
        | m1_subset_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X4),k2_zfmisc_1(sK1,sK2)) )
    | ~ spl8_0
    | ~ spl8_12
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f231,f137])).

fof(f231,plain,
    ( ! [X4] :
        ( ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X4,sK0)
        | m1_subset_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X4),k2_zfmisc_1(sK1,sK2)) )
    | ~ spl8_0
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f165,f111])).

fof(f165,plain,
    ( ! [X4] :
        ( ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X4,sK0)
        | m1_subset_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X4),k2_zfmisc_1(sK1,sK2)) )
    | ~ spl8_16 ),
    inference(resolution,[],[f151,f93])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X3,X0)
      | m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t196_funct_2.p',dt_k3_funct_2)).

fof(f337,plain,
    ( spl8_50
    | ~ spl8_0
    | spl8_3
    | spl8_5
    | spl8_7
    | ~ spl8_12
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f213,f150,f136,f122,f118,f114,f110,f335])).

fof(f213,plain,
    ( m1_subset_1(k4_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_12
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f212,f123])).

fof(f212,plain,
    ( v1_xboole_0(sK0)
    | m1_subset_1(k4_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_12
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f211,f137])).

fof(f211,plain,
    ( ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | v1_xboole_0(sK0)
    | m1_subset_1(k4_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f210,f111])).

fof(f210,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | v1_xboole_0(sK0)
    | m1_subset_1(k4_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f209,f115])).

fof(f209,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | v1_xboole_0(sK0)
    | m1_subset_1(k4_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_5
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f161,f119])).

fof(f161,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | v1_xboole_0(sK0)
    | m1_subset_1(k4_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_16 ),
    inference(resolution,[],[f151,f88])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | v1_xboole_0(X0)
      | m1_subset_1(k4_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k4_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(k4_funct_2(X0,X1,X2,X3),X0,X1)
        & v1_funct_1(k4_funct_2(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k4_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(k4_funct_2(X0,X1,X2,X3),X0,X1)
        & v1_funct_1(k4_funct_2(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
        & v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
        & v1_funct_1(X3)
        & ~ v1_xboole_0(X2)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( m1_subset_1(k4_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(k4_funct_2(X0,X1,X2,X3),X0,X1)
        & v1_funct_1(k4_funct_2(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t196_funct_2.p',dt_k4_funct_2)).

fof(f315,plain,
    ( spl8_42
    | ~ spl8_0
    | spl8_3
    | spl8_5
    | spl8_7
    | ~ spl8_12
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f181,f150,f136,f122,f118,f114,f110,f313])).

fof(f181,plain,
    ( m1_subset_1(k5_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_12
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f180,f123])).

fof(f180,plain,
    ( v1_xboole_0(sK0)
    | m1_subset_1(k5_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_12
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f179,f137])).

fof(f179,plain,
    ( ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | v1_xboole_0(sK0)
    | m1_subset_1(k5_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f178,f111])).

fof(f178,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | v1_xboole_0(sK0)
    | m1_subset_1(k5_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f177,f115])).

fof(f177,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | v1_xboole_0(sK0)
    | m1_subset_1(k5_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl8_5
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f155,f119])).

fof(f155,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | v1_xboole_0(sK0)
    | m1_subset_1(k5_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl8_16 ),
    inference(resolution,[],[f151,f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | v1_xboole_0(X0)
      | m1_subset_1(k5_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k5_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k5_funct_2(X0,X1,X2,X3),X0,X2)
        & v1_funct_1(k5_funct_2(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k5_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k5_funct_2(X0,X1,X2,X3),X0,X2)
        & v1_funct_1(k5_funct_2(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
        & v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
        & v1_funct_1(X3)
        & ~ v1_xboole_0(X2)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( m1_subset_1(k5_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k5_funct_2(X0,X1,X2,X3),X0,X2)
        & v1_funct_1(k5_funct_2(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t196_funct_2.p',dt_k5_funct_2)).

fof(f287,plain,
    ( spl8_40
    | ~ spl8_0
    | spl8_3
    | spl8_5
    | spl8_7
    | ~ spl8_12
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f218,f150,f136,f122,f118,f114,f110,f285])).

fof(f218,plain,
    ( k4_funct_2(sK0,sK1,sK2,sK3) = k15_mcart_1(sK3)
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_12
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f217,f123])).

fof(f217,plain,
    ( v1_xboole_0(sK0)
    | k4_funct_2(sK0,sK1,sK2,sK3) = k15_mcart_1(sK3)
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_12
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f216,f137])).

fof(f216,plain,
    ( ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | v1_xboole_0(sK0)
    | k4_funct_2(sK0,sK1,sK2,sK3) = k15_mcart_1(sK3)
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f215,f111])).

fof(f215,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | v1_xboole_0(sK0)
    | k4_funct_2(sK0,sK1,sK2,sK3) = k15_mcart_1(sK3)
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f214,f115])).

fof(f214,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | v1_xboole_0(sK0)
    | k4_funct_2(sK0,sK1,sK2,sK3) = k15_mcart_1(sK3)
    | ~ spl8_5
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f162,f119])).

fof(f162,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | v1_xboole_0(sK0)
    | k4_funct_2(sK0,sK1,sK2,sK3) = k15_mcart_1(sK3)
    | ~ spl8_16 ),
    inference(resolution,[],[f151,f89])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | v1_xboole_0(X0)
      | k4_funct_2(X0,X1,X2,X3) = k15_mcart_1(X3) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( k4_funct_2(X0,X1,X2,X3) = k15_mcart_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( k4_funct_2(X0,X1,X2,X3) = k15_mcart_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
        & v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
        & v1_funct_1(X3)
        & ~ v1_xboole_0(X2)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => k4_funct_2(X0,X1,X2,X3) = k15_mcart_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t196_funct_2.p',redefinition_k4_funct_2)).

fof(f283,plain,
    ( spl8_38
    | ~ spl8_0
    | spl8_3
    | spl8_5
    | spl8_7
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_36 ),
    inference(avatar_split_clause,[],[f279,f276,f150,f136,f122,f118,f114,f110,f281])).

fof(f276,plain,
    ( spl8_36
  <=> v1_funct_2(k4_funct_2(sK0,sK1,sK2,sK3),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f279,plain,
    ( v1_funct_2(k15_mcart_1(sK3),sK0,sK1)
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_36 ),
    inference(forward_demodulation,[],[f277,f218])).

fof(f277,plain,
    ( v1_funct_2(k4_funct_2(sK0,sK1,sK2,sK3),sK0,sK1)
    | ~ spl8_36 ),
    inference(avatar_component_clause,[],[f276])).

fof(f278,plain,
    ( spl8_36
    | ~ spl8_0
    | spl8_3
    | spl8_5
    | spl8_7
    | ~ spl8_12
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f208,f150,f136,f122,f118,f114,f110,f276])).

fof(f208,plain,
    ( v1_funct_2(k4_funct_2(sK0,sK1,sK2,sK3),sK0,sK1)
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_12
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f207,f123])).

fof(f207,plain,
    ( v1_xboole_0(sK0)
    | v1_funct_2(k4_funct_2(sK0,sK1,sK2,sK3),sK0,sK1)
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_12
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f206,f137])).

fof(f206,plain,
    ( ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | v1_xboole_0(sK0)
    | v1_funct_2(k4_funct_2(sK0,sK1,sK2,sK3),sK0,sK1)
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f205,f111])).

fof(f205,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | v1_xboole_0(sK0)
    | v1_funct_2(k4_funct_2(sK0,sK1,sK2,sK3),sK0,sK1)
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f204,f115])).

fof(f204,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | v1_xboole_0(sK0)
    | v1_funct_2(k4_funct_2(sK0,sK1,sK2,sK3),sK0,sK1)
    | ~ spl8_5
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f160,f119])).

fof(f160,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | v1_xboole_0(sK0)
    | v1_funct_2(k4_funct_2(sK0,sK1,sK2,sK3),sK0,sK1)
    | ~ spl8_16 ),
    inference(resolution,[],[f151,f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | v1_xboole_0(X0)
      | v1_funct_2(k4_funct_2(X0,X1,X2,X3),X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f274,plain,
    ( spl8_34
    | ~ spl8_0
    | spl8_3
    | spl8_5
    | spl8_7
    | ~ spl8_12
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f186,f150,f136,f122,f118,f114,f110,f272])).

fof(f186,plain,
    ( k5_funct_2(sK0,sK1,sK2,sK3) = k16_mcart_1(sK3)
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_12
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f185,f123])).

fof(f185,plain,
    ( v1_xboole_0(sK0)
    | k5_funct_2(sK0,sK1,sK2,sK3) = k16_mcart_1(sK3)
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_12
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f184,f137])).

fof(f184,plain,
    ( ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | v1_xboole_0(sK0)
    | k5_funct_2(sK0,sK1,sK2,sK3) = k16_mcart_1(sK3)
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f183,f111])).

fof(f183,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | v1_xboole_0(sK0)
    | k5_funct_2(sK0,sK1,sK2,sK3) = k16_mcart_1(sK3)
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f182,f115])).

fof(f182,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | v1_xboole_0(sK0)
    | k5_funct_2(sK0,sK1,sK2,sK3) = k16_mcart_1(sK3)
    | ~ spl8_5
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f156,f119])).

fof(f156,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | v1_xboole_0(sK0)
    | k5_funct_2(sK0,sK1,sK2,sK3) = k16_mcart_1(sK3)
    | ~ spl8_16 ),
    inference(resolution,[],[f151,f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | v1_xboole_0(X0)
      | k5_funct_2(X0,X1,X2,X3) = k16_mcart_1(X3) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( k5_funct_2(X0,X1,X2,X3) = k16_mcart_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( k5_funct_2(X0,X1,X2,X3) = k16_mcart_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
        & v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
        & v1_funct_1(X3)
        & ~ v1_xboole_0(X2)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => k5_funct_2(X0,X1,X2,X3) = k16_mcart_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t196_funct_2.p',redefinition_k5_funct_2)).

fof(f270,plain,
    ( spl8_32
    | ~ spl8_0
    | spl8_3
    | spl8_5
    | spl8_7
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f266,f263,f150,f136,f122,f118,f114,f110,f268])).

fof(f263,plain,
    ( spl8_30
  <=> v1_funct_2(k5_funct_2(sK0,sK1,sK2,sK3),sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f266,plain,
    ( v1_funct_2(k16_mcart_1(sK3),sK0,sK2)
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_30 ),
    inference(forward_demodulation,[],[f264,f186])).

fof(f264,plain,
    ( v1_funct_2(k5_funct_2(sK0,sK1,sK2,sK3),sK0,sK2)
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f263])).

fof(f265,plain,
    ( spl8_30
    | ~ spl8_0
    | spl8_3
    | spl8_5
    | spl8_7
    | ~ spl8_12
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f176,f150,f136,f122,f118,f114,f110,f263])).

fof(f176,plain,
    ( v1_funct_2(k5_funct_2(sK0,sK1,sK2,sK3),sK0,sK2)
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_12
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f175,f123])).

fof(f175,plain,
    ( v1_xboole_0(sK0)
    | v1_funct_2(k5_funct_2(sK0,sK1,sK2,sK3),sK0,sK2)
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_12
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f174,f137])).

fof(f174,plain,
    ( ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | v1_xboole_0(sK0)
    | v1_funct_2(k5_funct_2(sK0,sK1,sK2,sK3),sK0,sK2)
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f173,f111])).

fof(f173,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | v1_xboole_0(sK0)
    | v1_funct_2(k5_funct_2(sK0,sK1,sK2,sK3),sK0,sK2)
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f172,f115])).

fof(f172,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | v1_xboole_0(sK0)
    | v1_funct_2(k5_funct_2(sK0,sK1,sK2,sK3),sK0,sK2)
    | ~ spl8_5
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f154,f119])).

fof(f154,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | v1_xboole_0(sK0)
    | v1_funct_2(k5_funct_2(sK0,sK1,sK2,sK3),sK0,sK2)
    | ~ spl8_16 ),
    inference(resolution,[],[f151,f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | v1_xboole_0(X0)
      | v1_funct_2(k5_funct_2(X0,X1,X2,X3),X0,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f261,plain,
    ( spl8_28
    | ~ spl8_0
    | spl8_3
    | spl8_5
    | spl8_7
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f257,f254,f150,f136,f122,f118,f114,f110,f259])).

fof(f254,plain,
    ( spl8_26
  <=> v1_funct_1(k4_funct_2(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f257,plain,
    ( v1_funct_1(k15_mcart_1(sK3))
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_26 ),
    inference(forward_demodulation,[],[f255,f218])).

fof(f255,plain,
    ( v1_funct_1(k4_funct_2(sK0,sK1,sK2,sK3))
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f254])).

fof(f256,plain,
    ( spl8_26
    | ~ spl8_0
    | spl8_3
    | spl8_5
    | spl8_7
    | ~ spl8_12
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f203,f150,f136,f122,f118,f114,f110,f254])).

fof(f203,plain,
    ( v1_funct_1(k4_funct_2(sK0,sK1,sK2,sK3))
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_12
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f202,f123])).

fof(f202,plain,
    ( v1_xboole_0(sK0)
    | v1_funct_1(k4_funct_2(sK0,sK1,sK2,sK3))
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_12
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f201,f137])).

fof(f201,plain,
    ( ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | v1_xboole_0(sK0)
    | v1_funct_1(k4_funct_2(sK0,sK1,sK2,sK3))
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f200,f111])).

fof(f200,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | v1_xboole_0(sK0)
    | v1_funct_1(k4_funct_2(sK0,sK1,sK2,sK3))
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f199,f115])).

fof(f199,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | v1_xboole_0(sK0)
    | v1_funct_1(k4_funct_2(sK0,sK1,sK2,sK3))
    | ~ spl8_5
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f159,f119])).

fof(f159,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | v1_xboole_0(sK0)
    | v1_funct_1(k4_funct_2(sK0,sK1,sK2,sK3))
    | ~ spl8_16 ),
    inference(resolution,[],[f151,f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | v1_xboole_0(X0)
      | v1_funct_1(k4_funct_2(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f252,plain,
    ( ~ spl8_25
    | ~ spl8_0
    | spl8_3
    | spl8_5
    | spl8_7
    | ~ spl8_12
    | ~ spl8_16
    | spl8_21 ),
    inference(avatar_split_clause,[],[f244,f240,f150,f136,f122,f118,f114,f110,f250])).

fof(f240,plain,
    ( spl8_21
  <=> k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4) != k4_tarski(k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),sK4),k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f244,plain,
    ( k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4) != k4_tarski(k3_funct_2(sK0,sK1,k15_mcart_1(sK3),sK4),k3_funct_2(sK0,sK2,k16_mcart_1(sK3),sK4))
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_21 ),
    inference(forward_demodulation,[],[f243,f218])).

fof(f243,plain,
    ( k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4) != k4_tarski(k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),sK4),k3_funct_2(sK0,sK2,k16_mcart_1(sK3),sK4))
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_21 ),
    inference(forward_demodulation,[],[f241,f186])).

fof(f241,plain,
    ( k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4) != k4_tarski(k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),sK4),k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),sK4))
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f240])).

fof(f248,plain,
    ( spl8_22
    | ~ spl8_0
    | spl8_3
    | spl8_5
    | spl8_7
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f238,f235,f150,f136,f122,f118,f114,f110,f246])).

fof(f235,plain,
    ( spl8_18
  <=> v1_funct_1(k5_funct_2(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f238,plain,
    ( v1_funct_1(k16_mcart_1(sK3))
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_18 ),
    inference(forward_demodulation,[],[f236,f186])).

fof(f236,plain,
    ( v1_funct_1(k5_funct_2(sK0,sK1,sK2,sK3))
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f235])).

fof(f242,plain,(
    ~ spl8_21 ),
    inference(avatar_split_clause,[],[f70,f240])).

fof(f70,plain,(
    k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4) != k4_tarski(k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),sK4),k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),sK4)) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X4) != k4_tarski(k3_funct_2(X0,X1,k4_funct_2(X0,X1,X2,X3),X4),k3_funct_2(X0,X2,k5_funct_2(X0,X1,X2,X3),X4))
                      & m1_subset_1(X4,X0) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                  & v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                  & v1_funct_1(X3) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X4) != k4_tarski(k3_funct_2(X0,X1,k4_funct_2(X0,X1,X2,X3),X4),k3_funct_2(X0,X2,k5_funct_2(X0,X1,X2,X3),X4))
                      & m1_subset_1(X4,X0) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                  & v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                  & v1_funct_1(X3) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ~ v1_xboole_0(X2)
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                      & v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                      & v1_funct_1(X3) )
                   => ! [X4] :
                        ( m1_subset_1(X4,X0)
                       => k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X4) = k4_tarski(k3_funct_2(X0,X1,k4_funct_2(X0,X1,X2,X3),X4),k3_funct_2(X0,X2,k5_funct_2(X0,X1,X2,X3),X4)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                    & v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X4) = k4_tarski(k3_funct_2(X0,X1,k4_funct_2(X0,X1,X2,X3),X4),k3_funct_2(X0,X2,k5_funct_2(X0,X1,X2,X3),X4)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t196_funct_2.p',t196_funct_2)).

fof(f237,plain,
    ( spl8_18
    | ~ spl8_0
    | spl8_3
    | spl8_5
    | spl8_7
    | ~ spl8_12
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f171,f150,f136,f122,f118,f114,f110,f235])).

fof(f171,plain,
    ( v1_funct_1(k5_funct_2(sK0,sK1,sK2,sK3))
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_12
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f170,f123])).

fof(f170,plain,
    ( v1_xboole_0(sK0)
    | v1_funct_1(k5_funct_2(sK0,sK1,sK2,sK3))
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_12
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f169,f137])).

fof(f169,plain,
    ( ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | v1_xboole_0(sK0)
    | v1_funct_1(k5_funct_2(sK0,sK1,sK2,sK3))
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f168,f111])).

fof(f168,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | v1_xboole_0(sK0)
    | v1_funct_1(k5_funct_2(sK0,sK1,sK2,sK3))
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f167,f115])).

fof(f167,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | v1_xboole_0(sK0)
    | v1_funct_1(k5_funct_2(sK0,sK1,sK2,sK3))
    | ~ spl8_5
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f153,f119])).

fof(f153,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | v1_xboole_0(sK0)
    | v1_funct_1(k5_funct_2(sK0,sK1,sK2,sK3))
    | ~ spl8_16 ),
    inference(resolution,[],[f151,f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | v1_xboole_0(X0)
      | v1_funct_1(k5_funct_2(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f152,plain,(
    spl8_16 ),
    inference(avatar_split_clause,[],[f73,f150])).

fof(f73,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2)))) ),
    inference(cnf_transformation,[],[f37])).

fof(f138,plain,(
    spl8_12 ),
    inference(avatar_split_clause,[],[f72,f136])).

fof(f72,plain,(
    v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f37])).

fof(f128,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f69,f126])).

fof(f69,plain,(
    m1_subset_1(sK4,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f124,plain,(
    ~ spl8_7 ),
    inference(avatar_split_clause,[],[f76,f122])).

fof(f76,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f120,plain,(
    ~ spl8_5 ),
    inference(avatar_split_clause,[],[f75,f118])).

fof(f75,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f116,plain,(
    ~ spl8_3 ),
    inference(avatar_split_clause,[],[f74,f114])).

fof(f74,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f112,plain,(
    spl8_0 ),
    inference(avatar_split_clause,[],[f71,f110])).

fof(f71,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
