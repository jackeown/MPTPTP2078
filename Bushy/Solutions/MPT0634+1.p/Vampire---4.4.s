%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t37_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:23 EDT 2019

% Result     : Theorem 1.08s
% Output     : Refutation 1.08s
% Verified   : 
% Statistics : Number of formulae       :  521 (1776 expanded)
%              Number of leaves         :   88 ( 626 expanded)
%              Depth                    :   19
%              Number of atoms          : 1858 (5653 expanded)
%              Number of equality atoms :  279 (1239 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13119,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f86,f93,f147,f153,f166,f172,f207,f251,f258,f303,f308,f312,f322,f332,f338,f340,f344,f346,f356,f363,f370,f406,f419,f443,f448,f459,f466,f469,f491,f514,f521,f551,f556,f559,f897,f1061,f1070,f1085,f1090,f1211,f1341,f1350,f1354,f1361,f1585,f1597,f1600,f1602,f1628,f1637,f1643,f1650,f1665,f1674,f1723,f1855,f1878,f1897,f1911,f1942,f1944,f1950,f1979,f2241,f2323,f2450,f2608,f2615,f2646,f3013,f3343,f4492,f5564,f6807,f7201,f9648,f11742,f13023,f13028,f13041,f13048,f13058,f13112])).

fof(f13112,plain,
    ( ~ spl5_0
    | ~ spl5_2
    | spl5_5
    | spl5_7
    | ~ spl5_14
    | ~ spl5_22 ),
    inference(avatar_contradiction_clause,[],[f13111])).

fof(f13111,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_14
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f13110,f13080])).

fof(f13080,plain,
    ( r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(sK1))
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f13079,f66])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_xboole_0(X0,X1))
      | r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t37_funct_1.p',d4_xboole_0)).

fof(f13079,plain,
    ( r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(sK1))
    | r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k3_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f13054,f92])).

fof(f92,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) != k3_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl5_5
  <=> k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) != k3_xboole_0(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f13054,plain,
    ( r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(sK1))
    | r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k3_xboole_0(sK0,k1_relat_1(sK1)))
    | k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) = k3_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f13053,f78])).

fof(f78,plain,
    ( v1_relat_1(sK1)
    | ~ spl5_0 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl5_0
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f13053,plain,
    ( ~ v1_relat_1(sK1)
    | r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(sK1))
    | r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k3_xboole_0(sK0,k1_relat_1(sK1)))
    | k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) = k3_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl5_2
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f13016,f85])).

fof(f85,plain,
    ( v1_funct_1(sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl5_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f13016,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(sK1))
    | r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k3_xboole_0(sK0,k1_relat_1(sK1)))
    | k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) = k3_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl5_22 ),
    inference(resolution,[],[f414,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r2_hidden(sK3(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t37_funct_1.p',t2_tarski)).

fof(f414,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(k5_relat_1(k6_relat_1(sK0),X1)))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(X1)) )
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f413,f63])).

fof(f63,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t37_funct_1.p',fc3_funct_1)).

fof(f413,plain,
    ( ! [X1] :
        ( r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(X1))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_1(k6_relat_1(sK0))
        | ~ v1_relat_1(X1)
        | ~ r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(k5_relat_1(k6_relat_1(sK0),X1))) )
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f408,f62])).

fof(f62,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f408,plain,
    ( ! [X1] :
        ( r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(X1))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(k6_relat_1(sK0))
        | ~ v1_funct_1(k6_relat_1(sK0))
        | ~ v1_relat_1(X1)
        | ~ r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(k5_relat_1(k6_relat_1(sK0),X1))) )
    | ~ spl5_22 ),
    inference(superposition,[],[f59,f331])).

fof(f331,plain,
    ( k1_funct_1(k6_relat_1(sK0),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))) = sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f330])).

fof(f330,plain,
    ( spl5_22
  <=> k1_funct_1(k6_relat_1(sK0),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))) = sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t37_funct_1.p',t21_funct_1)).

fof(f13110,plain,
    ( ~ r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(sK1))
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_7
    | ~ spl5_14
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f13109,f78])).

fof(f13109,plain,
    ( ~ v1_relat_1(sK1)
    | ~ r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(sK1))
    | ~ spl5_2
    | ~ spl5_7
    | ~ spl5_14
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f13098,f85])).

fof(f13098,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(sK1))
    | ~ spl5_7
    | ~ spl5_14
    | ~ spl5_22 ),
    inference(resolution,[],[f140,f412])).

fof(f412,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(k5_relat_1(k6_relat_1(sK0),X0)))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(X0)) )
    | ~ spl5_14
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f411,f197])).

fof(f197,plain,
    ( r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),sK0)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl5_14
  <=> r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f411,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),sK0)
        | ~ r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(k5_relat_1(k6_relat_1(sK0),X0))) )
    | ~ spl5_22 ),
    inference(forward_demodulation,[],[f410,f121])).

fof(f121,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(subsumption_resolution,[],[f120,f62])).

fof(f120,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k6_relat_1(X0))
      | k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    inference(resolution,[],[f68,f63])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0))
      | k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) = X0
      | k6_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t37_funct_1.p',t34_funct_1)).

fof(f410,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(X0))
        | ~ v1_funct_1(X0)
        | ~ r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(k6_relat_1(sK0)))
        | ~ v1_relat_1(X0)
        | r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(k5_relat_1(k6_relat_1(sK0),X0))) )
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f409,f63])).

fof(f409,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_1(k6_relat_1(sK0))
        | ~ r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(k6_relat_1(sK0)))
        | ~ v1_relat_1(X0)
        | r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(k5_relat_1(k6_relat_1(sK0),X0))) )
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f407,f62])).

fof(f407,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(k6_relat_1(sK0))
        | ~ v1_funct_1(k6_relat_1(sK0))
        | ~ r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(k6_relat_1(sK0)))
        | ~ v1_relat_1(X0)
        | r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(k5_relat_1(k6_relat_1(sK0),X0))) )
    | ~ spl5_22 ),
    inference(superposition,[],[f60,f331])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X1)
      | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f140,plain,
    ( ~ r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl5_7
  <=> ~ r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f13058,plain,
    ( ~ spl5_0
    | ~ spl5_2
    | spl5_5
    | spl5_9
    | spl5_17
    | ~ spl5_22 ),
    inference(avatar_contradiction_clause,[],[f13057])).

fof(f13057,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_9
    | ~ spl5_17
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f13056,f92])).

fof(f13056,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) = k3_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_9
    | ~ spl5_17
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f13055,f146])).

fof(f146,plain,
    ( ~ r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k3_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl5_9
  <=> ~ r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k3_xboole_0(sK0,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f13055,plain,
    ( r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k3_xboole_0(sK0,k1_relat_1(sK1)))
    | k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) = k3_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_17
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f13054,f206])).

fof(f206,plain,
    ( ~ r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(sK1))
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl5_17
  <=> ~ r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f13048,plain,
    ( ~ spl5_0
    | ~ spl5_2
    | spl5_5
    | spl5_17
    | ~ spl5_22 ),
    inference(avatar_contradiction_clause,[],[f13047])).

fof(f13047,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_17
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f13046,f206])).

fof(f13046,plain,
    ( r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(sK1))
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_17
    | ~ spl5_22 ),
    inference(forward_demodulation,[],[f13045,f54])).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t37_funct_1.p',commutativity_k3_xboole_0)).

fof(f13045,plain,
    ( r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(k1_relat_1(sK1),sK0)),k1_relat_1(sK1))
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_17
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f13044,f92])).

fof(f13044,plain,
    ( r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(k1_relat_1(sK1),sK0)),k1_relat_1(sK1))
    | k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) = k3_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_17
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f13043,f206])).

fof(f13043,plain,
    ( r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(sK1))
    | r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(k1_relat_1(sK1),sK0)),k1_relat_1(sK1))
    | k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) = k3_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f13042,f78])).

fof(f13042,plain,
    ( ~ v1_relat_1(sK1)
    | r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(sK1))
    | r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(k1_relat_1(sK1),sK0)),k1_relat_1(sK1))
    | k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) = k3_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl5_2
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f13012,f85])).

fof(f13012,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(sK1))
    | r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(k1_relat_1(sK1),sK0)),k1_relat_1(sK1))
    | k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) = k3_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl5_22 ),
    inference(resolution,[],[f414,f706])).

fof(f706,plain,(
    ! [X6,X4,X5] :
      ( r2_hidden(sK3(X6,k3_xboole_0(X5,X4)),X5)
      | r2_hidden(sK3(X6,k3_xboole_0(X4,X5)),X6)
      | k3_xboole_0(X4,X5) = X6 ) ),
    inference(superposition,[],[f123,f54])).

fof(f123,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(sK3(X3,k3_xboole_0(X4,X5)),X5)
      | r2_hidden(sK3(X3,k3_xboole_0(X4,X5)),X3)
      | k3_xboole_0(X4,X5) = X3 ) ),
    inference(resolution,[],[f48,f66])).

fof(f13041,plain,
    ( ~ spl5_0
    | ~ spl5_2
    | spl5_5
    | spl5_17
    | ~ spl5_22 ),
    inference(avatar_contradiction_clause,[],[f13040])).

fof(f13040,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_17
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f13039,f92])).

fof(f13039,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) = k3_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_17
    | ~ spl5_22 ),
    inference(forward_demodulation,[],[f13038,f54])).

fof(f13038,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) = k3_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_17
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f13037,f206])).

fof(f13037,plain,
    ( r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(sK1))
    | k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) = k3_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_17
    | ~ spl5_22 ),
    inference(forward_demodulation,[],[f13036,f54])).

fof(f13036,plain,
    ( r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(k1_relat_1(sK1),sK0)),k1_relat_1(sK1))
    | k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) = k3_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_17
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f13035,f206])).

fof(f13035,plain,
    ( r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(sK1))
    | r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(k1_relat_1(sK1),sK0)),k1_relat_1(sK1))
    | k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) = k3_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f13034,f78])).

fof(f13034,plain,
    ( ~ v1_relat_1(sK1)
    | r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(sK1))
    | r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(k1_relat_1(sK1),sK0)),k1_relat_1(sK1))
    | k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) = k3_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl5_2
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f13010,f85])).

fof(f13010,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(sK1))
    | r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(k1_relat_1(sK1),sK0)),k1_relat_1(sK1))
    | k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) = k3_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl5_22 ),
    inference(resolution,[],[f414,f666])).

fof(f666,plain,(
    ! [X6,X4,X5] :
      ( r2_hidden(sK3(X6,k3_xboole_0(X5,X4)),X6)
      | r2_hidden(sK3(X6,k3_xboole_0(X4,X5)),X4)
      | k3_xboole_0(X4,X5) = X6 ) ),
    inference(superposition,[],[f122,f54])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,k3_xboole_0(X1,X2)),X1)
      | r2_hidden(sK3(X0,k3_xboole_0(X1,X2)),X0)
      | k3_xboole_0(X1,X2) = X0 ) ),
    inference(resolution,[],[f48,f67])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_xboole_0(X0,X1))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f13028,plain,
    ( ~ spl5_0
    | ~ spl5_2
    | spl5_5
    | spl5_17
    | ~ spl5_22 ),
    inference(avatar_contradiction_clause,[],[f13027])).

fof(f13027,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_17
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f13026,f92])).

fof(f13026,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) = k3_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_17
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f13025,f206])).

fof(f13025,plain,
    ( r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(sK1))
    | k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) = k3_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f13024,f78])).

fof(f13024,plain,
    ( ~ v1_relat_1(sK1)
    | r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(sK1))
    | k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) = k3_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl5_2
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f13018,f85])).

fof(f13018,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(sK1))
    | k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) = k3_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl5_22 ),
    inference(duplicate_literal_removal,[],[f13008])).

fof(f13008,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(sK1))
    | r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(sK1))
    | k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) = k3_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl5_22 ),
    inference(resolution,[],[f414,f123])).

fof(f13023,plain,
    ( ~ spl5_0
    | ~ spl5_2
    | ~ spl5_6
    | spl5_17
    | ~ spl5_22 ),
    inference(avatar_contradiction_clause,[],[f13022])).

fof(f13022,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_17
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f13021,f206])).

fof(f13021,plain,
    ( r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(sK1))
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f13020,f78])).

fof(f13020,plain,
    ( ~ v1_relat_1(sK1)
    | r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(sK1))
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f13005,f85])).

fof(f13005,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(sK1))
    | ~ spl5_6
    | ~ spl5_22 ),
    inference(resolution,[],[f414,f137])).

fof(f137,plain,
    ( r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl5_6
  <=> r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f11742,plain,
    ( spl5_122
    | ~ spl5_76
    | ~ spl5_86 ),
    inference(avatar_split_clause,[],[f10868,f1853,f1623,f11740])).

fof(f11740,plain,
    ( spl5_122
  <=> k1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(k6_relat_1(k1_relat_1(sK1))),k6_relat_1(k6_relat_1(k1_relat_1(sK1)))))),sK3(sK1,k6_relat_1(k1_relat_1(sK1)))) = sK3(sK1,k6_relat_1(k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_122])])).

fof(f1623,plain,
    ( spl5_76
  <=> r2_hidden(sK3(sK1,k6_relat_1(k1_relat_1(sK1))),k6_relat_1(k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).

fof(f1853,plain,
    ( spl5_86
  <=> k1_funct_1(k6_relat_1(k6_relat_1(k1_relat_1(sK1))),sK3(sK1,k6_relat_1(k1_relat_1(sK1)))) = sK3(sK1,k6_relat_1(k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_86])])).

fof(f10868,plain,
    ( k1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(k6_relat_1(k1_relat_1(sK1))),k6_relat_1(k6_relat_1(k1_relat_1(sK1)))))),sK3(sK1,k6_relat_1(k1_relat_1(sK1)))) = sK3(sK1,k6_relat_1(k1_relat_1(sK1)))
    | ~ spl5_76
    | ~ spl5_86 ),
    inference(resolution,[],[f10592,f1624])).

fof(f1624,plain,
    ( r2_hidden(sK3(sK1,k6_relat_1(k1_relat_1(sK1))),k6_relat_1(k1_relat_1(sK1)))
    | ~ spl5_76 ),
    inference(avatar_component_clause,[],[f1623])).

fof(f10592,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(sK1,k6_relat_1(k1_relat_1(sK1))),X0)
        | k1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(k6_relat_1(k1_relat_1(sK1))),k6_relat_1(X0)))),sK3(sK1,k6_relat_1(k1_relat_1(sK1)))) = sK3(sK1,k6_relat_1(k1_relat_1(sK1))) )
    | ~ spl5_76
    | ~ spl5_86 ),
    inference(subsumption_resolution,[],[f10591,f63])).

fof(f10591,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(sK1,k6_relat_1(k1_relat_1(sK1))),X0)
        | ~ v1_funct_1(k6_relat_1(X0))
        | k1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(k6_relat_1(k1_relat_1(sK1))),k6_relat_1(X0)))),sK3(sK1,k6_relat_1(k1_relat_1(sK1)))) = sK3(sK1,k6_relat_1(k1_relat_1(sK1))) )
    | ~ spl5_76
    | ~ spl5_86 ),
    inference(subsumption_resolution,[],[f10590,f62])).

fof(f10590,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(sK1,k6_relat_1(k1_relat_1(sK1))),X0)
        | ~ v1_relat_1(k6_relat_1(X0))
        | ~ v1_funct_1(k6_relat_1(X0))
        | k1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(k6_relat_1(k1_relat_1(sK1))),k6_relat_1(X0)))),sK3(sK1,k6_relat_1(k1_relat_1(sK1)))) = sK3(sK1,k6_relat_1(k1_relat_1(sK1))) )
    | ~ spl5_76
    | ~ spl5_86 ),
    inference(superposition,[],[f2009,f121])).

fof(f2009,plain,
    ( ! [X7] :
        ( ~ r2_hidden(sK3(sK1,k6_relat_1(k1_relat_1(sK1))),k1_relat_1(X7))
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7)
        | k1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(k6_relat_1(k1_relat_1(sK1))),X7))),sK3(sK1,k6_relat_1(k1_relat_1(sK1)))) = sK3(sK1,k6_relat_1(k1_relat_1(sK1))) )
    | ~ spl5_76
    | ~ spl5_86 ),
    inference(subsumption_resolution,[],[f2008,f62])).

fof(f2008,plain,
    ( ! [X7] :
        ( ~ v1_funct_1(X7)
        | ~ v1_relat_1(X7)
        | ~ r2_hidden(sK3(sK1,k6_relat_1(k1_relat_1(sK1))),k1_relat_1(X7))
        | ~ v1_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(k6_relat_1(k1_relat_1(sK1))),X7))))
        | k1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(k6_relat_1(k1_relat_1(sK1))),X7))),sK3(sK1,k6_relat_1(k1_relat_1(sK1)))) = sK3(sK1,k6_relat_1(k1_relat_1(sK1))) )
    | ~ spl5_76
    | ~ spl5_86 ),
    inference(subsumption_resolution,[],[f1993,f63])).

fof(f1993,plain,
    ( ! [X7] :
        ( ~ v1_funct_1(X7)
        | ~ v1_relat_1(X7)
        | ~ r2_hidden(sK3(sK1,k6_relat_1(k1_relat_1(sK1))),k1_relat_1(X7))
        | ~ v1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(k6_relat_1(k1_relat_1(sK1))),X7))))
        | ~ v1_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(k6_relat_1(k1_relat_1(sK1))),X7))))
        | k1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(k6_relat_1(k1_relat_1(sK1))),X7))),sK3(sK1,k6_relat_1(k1_relat_1(sK1)))) = sK3(sK1,k6_relat_1(k1_relat_1(sK1))) )
    | ~ spl5_76
    | ~ spl5_86 ),
    inference(resolution,[],[f1861,f69])).

fof(f69,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0))
      | k1_funct_1(k6_relat_1(X0),X2) = X2 ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X2,X0)
      | k1_funct_1(X1,X2) = X2
      | k6_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1861,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK1,k6_relat_1(k1_relat_1(sK1))),k1_relat_1(k5_relat_1(k6_relat_1(k6_relat_1(k1_relat_1(sK1))),X0)))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(sK3(sK1,k6_relat_1(k1_relat_1(sK1))),k1_relat_1(X0)) )
    | ~ spl5_76
    | ~ spl5_86 ),
    inference(subsumption_resolution,[],[f1860,f1624])).

fof(f1860,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(sK1,k6_relat_1(k1_relat_1(sK1))),k6_relat_1(k1_relat_1(sK1)))
        | ~ r2_hidden(sK3(sK1,k6_relat_1(k1_relat_1(sK1))),k1_relat_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | r2_hidden(sK3(sK1,k6_relat_1(k1_relat_1(sK1))),k1_relat_1(k5_relat_1(k6_relat_1(k6_relat_1(k1_relat_1(sK1))),X0))) )
    | ~ spl5_86 ),
    inference(forward_demodulation,[],[f1859,f121])).

fof(f1859,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(sK1,k6_relat_1(k1_relat_1(sK1))),k1_relat_1(X0))
        | ~ v1_funct_1(X0)
        | ~ r2_hidden(sK3(sK1,k6_relat_1(k1_relat_1(sK1))),k1_relat_1(k6_relat_1(k6_relat_1(k1_relat_1(sK1)))))
        | ~ v1_relat_1(X0)
        | r2_hidden(sK3(sK1,k6_relat_1(k1_relat_1(sK1))),k1_relat_1(k5_relat_1(k6_relat_1(k6_relat_1(k1_relat_1(sK1))),X0))) )
    | ~ spl5_86 ),
    inference(subsumption_resolution,[],[f1858,f63])).

fof(f1858,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(sK1,k6_relat_1(k1_relat_1(sK1))),k1_relat_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_1(k6_relat_1(k6_relat_1(k1_relat_1(sK1))))
        | ~ r2_hidden(sK3(sK1,k6_relat_1(k1_relat_1(sK1))),k1_relat_1(k6_relat_1(k6_relat_1(k1_relat_1(sK1)))))
        | ~ v1_relat_1(X0)
        | r2_hidden(sK3(sK1,k6_relat_1(k1_relat_1(sK1))),k1_relat_1(k5_relat_1(k6_relat_1(k6_relat_1(k1_relat_1(sK1))),X0))) )
    | ~ spl5_86 ),
    inference(subsumption_resolution,[],[f1856,f62])).

fof(f1856,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(sK1,k6_relat_1(k1_relat_1(sK1))),k1_relat_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(k6_relat_1(k6_relat_1(k1_relat_1(sK1))))
        | ~ v1_funct_1(k6_relat_1(k6_relat_1(k1_relat_1(sK1))))
        | ~ r2_hidden(sK3(sK1,k6_relat_1(k1_relat_1(sK1))),k1_relat_1(k6_relat_1(k6_relat_1(k1_relat_1(sK1)))))
        | ~ v1_relat_1(X0)
        | r2_hidden(sK3(sK1,k6_relat_1(k1_relat_1(sK1))),k1_relat_1(k5_relat_1(k6_relat_1(k6_relat_1(k1_relat_1(sK1))),X0))) )
    | ~ spl5_86 ),
    inference(superposition,[],[f60,f1854])).

fof(f1854,plain,
    ( k1_funct_1(k6_relat_1(k6_relat_1(k1_relat_1(sK1))),sK3(sK1,k6_relat_1(k1_relat_1(sK1)))) = sK3(sK1,k6_relat_1(k1_relat_1(sK1)))
    | ~ spl5_86 ),
    inference(avatar_component_clause,[],[f1853])).

fof(f9648,plain,
    ( spl5_120
    | ~ spl5_60
    | ~ spl5_84 ),
    inference(avatar_split_clause,[],[f9323,f1721,f1056,f9646])).

fof(f9646,plain,
    ( spl5_120
  <=> k1_funct_1(k6_relat_1(k3_xboole_0(sK1,k1_relat_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK1))))),sK3(k6_relat_1(k1_relat_1(sK1)),sK1)) = sK3(k6_relat_1(k1_relat_1(sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_120])])).

fof(f1056,plain,
    ( spl5_60
  <=> r2_hidden(sK3(k6_relat_1(k1_relat_1(sK1)),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).

fof(f1721,plain,
    ( spl5_84
  <=> k1_funct_1(k6_relat_1(sK1),sK3(k6_relat_1(k1_relat_1(sK1)),sK1)) = sK3(k6_relat_1(k1_relat_1(sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_84])])).

fof(f9323,plain,
    ( k1_funct_1(k6_relat_1(k3_xboole_0(sK1,k1_relat_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK1))))),sK3(k6_relat_1(k1_relat_1(sK1)),sK1)) = sK3(k6_relat_1(k1_relat_1(sK1)),sK1)
    | ~ spl5_60
    | ~ spl5_84 ),
    inference(resolution,[],[f9003,f1057])).

fof(f1057,plain,
    ( r2_hidden(sK3(k6_relat_1(k1_relat_1(sK1)),sK1),sK1)
    | ~ spl5_60 ),
    inference(avatar_component_clause,[],[f1056])).

fof(f9003,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(k6_relat_1(k1_relat_1(sK1)),sK1),X0)
        | k1_funct_1(k6_relat_1(k3_xboole_0(sK1,k1_relat_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(X0))))),sK3(k6_relat_1(k1_relat_1(sK1)),sK1)) = sK3(k6_relat_1(k1_relat_1(sK1)),sK1) )
    | ~ spl5_60
    | ~ spl5_84 ),
    inference(subsumption_resolution,[],[f9002,f62])).

fof(f9002,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(k6_relat_1(k1_relat_1(sK1)),sK1),X0)
        | ~ v1_relat_1(k6_relat_1(X0))
        | k1_funct_1(k6_relat_1(k3_xboole_0(sK1,k1_relat_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(X0))))),sK3(k6_relat_1(k1_relat_1(sK1)),sK1)) = sK3(k6_relat_1(k1_relat_1(sK1)),sK1) )
    | ~ spl5_60
    | ~ spl5_84 ),
    inference(subsumption_resolution,[],[f9001,f63])).

fof(f9001,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(k6_relat_1(k1_relat_1(sK1)),sK1),X0)
        | ~ v1_funct_1(k6_relat_1(X0))
        | ~ v1_relat_1(k6_relat_1(X0))
        | k1_funct_1(k6_relat_1(k3_xboole_0(sK1,k1_relat_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(X0))))),sK3(k6_relat_1(k1_relat_1(sK1)),sK1)) = sK3(k6_relat_1(k1_relat_1(sK1)),sK1) )
    | ~ spl5_60
    | ~ spl5_84 ),
    inference(superposition,[],[f1924,f121])).

fof(f1924,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(k6_relat_1(k1_relat_1(sK1)),sK1),k1_relat_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k1_funct_1(k6_relat_1(k3_xboole_0(sK1,k1_relat_1(k5_relat_1(k6_relat_1(sK1),X0)))),sK3(k6_relat_1(k1_relat_1(sK1)),sK1)) = sK3(k6_relat_1(k1_relat_1(sK1)),sK1) )
    | ~ spl5_60
    | ~ spl5_84 ),
    inference(forward_demodulation,[],[f1915,f54])).

fof(f1915,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(sK3(k6_relat_1(k1_relat_1(sK1)),sK1),k1_relat_1(X0))
        | k1_funct_1(k6_relat_1(k3_xboole_0(k1_relat_1(k5_relat_1(k6_relat_1(sK1),X0)),sK1)),sK3(k6_relat_1(k1_relat_1(sK1)),sK1)) = sK3(k6_relat_1(k1_relat_1(sK1)),sK1) )
    | ~ spl5_60
    | ~ spl5_84 ),
    inference(resolution,[],[f1800,f1605])).

fof(f1605,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(k6_relat_1(k1_relat_1(sK1)),sK1),X0)
        | k1_funct_1(k6_relat_1(k3_xboole_0(X0,sK1)),sK3(k6_relat_1(k1_relat_1(sK1)),sK1)) = sK3(k6_relat_1(k1_relat_1(sK1)),sK1) )
    | ~ spl5_60 ),
    inference(resolution,[],[f1057,f180])).

fof(f180,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | k1_funct_1(k6_relat_1(k3_xboole_0(X0,X1)),X2) = X2
      | ~ r2_hidden(X2,X0) ) ),
    inference(subsumption_resolution,[],[f179,f62])).

fof(f179,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(k6_relat_1(k3_xboole_0(X0,X1)))
      | k1_funct_1(k6_relat_1(k3_xboole_0(X0,X1)),X2) = X2
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(subsumption_resolution,[],[f174,f63])).

fof(f174,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(k6_relat_1(k3_xboole_0(X0,X1)))
      | ~ v1_relat_1(k6_relat_1(k3_xboole_0(X0,X1)))
      | k1_funct_1(k6_relat_1(k3_xboole_0(X0,X1)),X2) = X2
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(resolution,[],[f69,f65])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f1800,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(k6_relat_1(k1_relat_1(sK1)),sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK1),X0)))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(sK3(k6_relat_1(k1_relat_1(sK1)),sK1),k1_relat_1(X0)) )
    | ~ spl5_60
    | ~ spl5_84 ),
    inference(subsumption_resolution,[],[f1799,f1057])).

fof(f1799,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(k6_relat_1(k1_relat_1(sK1)),sK1),sK1)
        | ~ r2_hidden(sK3(k6_relat_1(k1_relat_1(sK1)),sK1),k1_relat_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | r2_hidden(sK3(k6_relat_1(k1_relat_1(sK1)),sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK1),X0))) )
    | ~ spl5_84 ),
    inference(forward_demodulation,[],[f1798,f121])).

fof(f1798,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(k6_relat_1(k1_relat_1(sK1)),sK1),k1_relat_1(X0))
        | ~ v1_funct_1(X0)
        | ~ r2_hidden(sK3(k6_relat_1(k1_relat_1(sK1)),sK1),k1_relat_1(k6_relat_1(sK1)))
        | ~ v1_relat_1(X0)
        | r2_hidden(sK3(k6_relat_1(k1_relat_1(sK1)),sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK1),X0))) )
    | ~ spl5_84 ),
    inference(subsumption_resolution,[],[f1797,f63])).

fof(f1797,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(k6_relat_1(k1_relat_1(sK1)),sK1),k1_relat_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_1(k6_relat_1(sK1))
        | ~ r2_hidden(sK3(k6_relat_1(k1_relat_1(sK1)),sK1),k1_relat_1(k6_relat_1(sK1)))
        | ~ v1_relat_1(X0)
        | r2_hidden(sK3(k6_relat_1(k1_relat_1(sK1)),sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK1),X0))) )
    | ~ spl5_84 ),
    inference(subsumption_resolution,[],[f1795,f62])).

fof(f1795,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(k6_relat_1(k1_relat_1(sK1)),sK1),k1_relat_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(k6_relat_1(sK1))
        | ~ v1_funct_1(k6_relat_1(sK1))
        | ~ r2_hidden(sK3(k6_relat_1(k1_relat_1(sK1)),sK1),k1_relat_1(k6_relat_1(sK1)))
        | ~ v1_relat_1(X0)
        | r2_hidden(sK3(k6_relat_1(k1_relat_1(sK1)),sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK1),X0))) )
    | ~ spl5_84 ),
    inference(superposition,[],[f60,f1722])).

fof(f1722,plain,
    ( k1_funct_1(k6_relat_1(sK1),sK3(k6_relat_1(k1_relat_1(sK1)),sK1)) = sK3(k6_relat_1(k1_relat_1(sK1)),sK1)
    | ~ spl5_84 ),
    inference(avatar_component_clause,[],[f1721])).

fof(f7201,plain,
    ( spl5_118
    | ~ spl5_0
    | ~ spl5_2
    | spl5_57
    | ~ spl5_98
    | ~ spl5_100 ),
    inference(avatar_split_clause,[],[f7091,f2318,f2315,f892,f84,f77,f7199])).

fof(f7199,plain,
    ( spl5_118
  <=> k1_funct_1(k6_relat_1(k3_xboole_0(k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),k6_relat_1(k1_relat_1(sK1)))))),sK4(k1_relat_1(sK1),sK1)) = sK4(k1_relat_1(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_118])])).

fof(f892,plain,
    ( spl5_57
  <=> k6_relat_1(k1_relat_1(sK1)) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).

fof(f2315,plain,
    ( spl5_98
  <=> ! [X0] :
        ( ~ r2_hidden(sK4(k1_relat_1(sK1),sK1),k1_relat_1(X0))
        | r2_hidden(sK4(k1_relat_1(sK1),sK1),k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),X0)))
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_98])])).

fof(f2318,plain,
    ( spl5_100
  <=> r2_hidden(sK4(k1_relat_1(sK1),sK1),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_100])])).

fof(f7091,plain,
    ( k1_funct_1(k6_relat_1(k3_xboole_0(k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),k6_relat_1(k1_relat_1(sK1)))))),sK4(k1_relat_1(sK1),sK1)) = sK4(k1_relat_1(sK1),sK1)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_57
    | ~ spl5_98
    | ~ spl5_100 ),
    inference(subsumption_resolution,[],[f7090,f893])).

fof(f893,plain,
    ( k6_relat_1(k1_relat_1(sK1)) != sK1
    | ~ spl5_57 ),
    inference(avatar_component_clause,[],[f892])).

fof(f7090,plain,
    ( k1_funct_1(k6_relat_1(k3_xboole_0(k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),k6_relat_1(k1_relat_1(sK1)))))),sK4(k1_relat_1(sK1),sK1)) = sK4(k1_relat_1(sK1),sK1)
    | k6_relat_1(k1_relat_1(sK1)) = sK1
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_98
    | ~ spl5_100 ),
    inference(subsumption_resolution,[],[f7089,f78])).

fof(f7089,plain,
    ( k1_funct_1(k6_relat_1(k3_xboole_0(k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),k6_relat_1(k1_relat_1(sK1)))))),sK4(k1_relat_1(sK1),sK1)) = sK4(k1_relat_1(sK1),sK1)
    | ~ v1_relat_1(sK1)
    | k6_relat_1(k1_relat_1(sK1)) = sK1
    | ~ spl5_2
    | ~ spl5_98
    | ~ spl5_100 ),
    inference(subsumption_resolution,[],[f7084,f85])).

fof(f7084,plain,
    ( k1_funct_1(k6_relat_1(k3_xboole_0(k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),k6_relat_1(k1_relat_1(sK1)))))),sK4(k1_relat_1(sK1),sK1)) = sK4(k1_relat_1(sK1),sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k6_relat_1(k1_relat_1(sK1)) = sK1
    | ~ spl5_98
    | ~ spl5_100 ),
    inference(resolution,[],[f6498,f71])).

fof(f71,plain,(
    ! [X1] :
      ( r2_hidden(sK4(k1_relat_1(X1),X1),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k6_relat_1(k1_relat_1(X1)) = X1 ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != X0
      | r2_hidden(sK4(X0,X1),X0)
      | k6_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f6498,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(k1_relat_1(sK1),sK1),X0)
        | k1_funct_1(k6_relat_1(k3_xboole_0(k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),k6_relat_1(X0))))),sK4(k1_relat_1(sK1),sK1)) = sK4(k1_relat_1(sK1),sK1) )
    | ~ spl5_98
    | ~ spl5_100 ),
    inference(subsumption_resolution,[],[f6497,f63])).

fof(f6497,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(k1_relat_1(sK1),sK1),X0)
        | k1_funct_1(k6_relat_1(k3_xboole_0(k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),k6_relat_1(X0))))),sK4(k1_relat_1(sK1),sK1)) = sK4(k1_relat_1(sK1),sK1)
        | ~ v1_funct_1(k6_relat_1(X0)) )
    | ~ spl5_98
    | ~ spl5_100 ),
    inference(subsumption_resolution,[],[f6492,f62])).

fof(f6492,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(k1_relat_1(sK1),sK1),X0)
        | k1_funct_1(k6_relat_1(k3_xboole_0(k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),k6_relat_1(X0))))),sK4(k1_relat_1(sK1),sK1)) = sK4(k1_relat_1(sK1),sK1)
        | ~ v1_relat_1(k6_relat_1(X0))
        | ~ v1_funct_1(k6_relat_1(X0)) )
    | ~ spl5_98
    | ~ spl5_100 ),
    inference(superposition,[],[f2627,f121])).

fof(f2627,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK4(k1_relat_1(sK1),sK1),k1_relat_1(X1))
        | k1_funct_1(k6_relat_1(k3_xboole_0(k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),X1)))),sK4(k1_relat_1(sK1),sK1)) = sK4(k1_relat_1(sK1),sK1)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1) )
    | ~ spl5_98
    | ~ spl5_100 ),
    inference(forward_demodulation,[],[f2617,f54])).

fof(f2617,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK4(k1_relat_1(sK1),sK1),k1_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | k1_funct_1(k6_relat_1(k3_xboole_0(k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),X1)),k1_relat_1(sK1))),sK4(k1_relat_1(sK1),sK1)) = sK4(k1_relat_1(sK1),sK1) )
    | ~ spl5_98
    | ~ spl5_100 ),
    inference(resolution,[],[f2316,f2517])).

fof(f2517,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(k1_relat_1(sK1),sK1),X0)
        | k1_funct_1(k6_relat_1(k3_xboole_0(X0,k1_relat_1(sK1))),sK4(k1_relat_1(sK1),sK1)) = sK4(k1_relat_1(sK1),sK1) )
    | ~ spl5_100 ),
    inference(resolution,[],[f2319,f180])).

fof(f2319,plain,
    ( r2_hidden(sK4(k1_relat_1(sK1),sK1),k1_relat_1(sK1))
    | ~ spl5_100 ),
    inference(avatar_component_clause,[],[f2318])).

fof(f2316,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(k1_relat_1(sK1),sK1),k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),X0)))
        | ~ r2_hidden(sK4(k1_relat_1(sK1),sK1),k1_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0) )
    | ~ spl5_98 ),
    inference(avatar_component_clause,[],[f2315])).

fof(f6807,plain,
    ( spl5_116
    | ~ spl5_0
    | ~ spl5_2
    | spl5_57
    | ~ spl5_98
    | ~ spl5_100 ),
    inference(avatar_split_clause,[],[f6496,f2318,f2315,f892,f84,f77,f6805])).

fof(f6805,plain,
    ( spl5_116
  <=> k1_funct_1(k6_relat_1(k3_xboole_0(k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1)))),sK4(k1_relat_1(sK1),sK1)) = sK4(k1_relat_1(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_116])])).

fof(f6496,plain,
    ( k1_funct_1(k6_relat_1(k3_xboole_0(k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1)))),sK4(k1_relat_1(sK1),sK1)) = sK4(k1_relat_1(sK1),sK1)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_57
    | ~ spl5_98
    | ~ spl5_100 ),
    inference(subsumption_resolution,[],[f6495,f893])).

fof(f6495,plain,
    ( k1_funct_1(k6_relat_1(k3_xboole_0(k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1)))),sK4(k1_relat_1(sK1),sK1)) = sK4(k1_relat_1(sK1),sK1)
    | k6_relat_1(k1_relat_1(sK1)) = sK1
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_98
    | ~ spl5_100 ),
    inference(subsumption_resolution,[],[f6494,f85])).

fof(f6494,plain,
    ( k1_funct_1(k6_relat_1(k3_xboole_0(k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1)))),sK4(k1_relat_1(sK1),sK1)) = sK4(k1_relat_1(sK1),sK1)
    | ~ v1_funct_1(sK1)
    | k6_relat_1(k1_relat_1(sK1)) = sK1
    | ~ spl5_0
    | ~ spl5_98
    | ~ spl5_100 ),
    inference(subsumption_resolution,[],[f6493,f78])).

fof(f6493,plain,
    ( k1_funct_1(k6_relat_1(k3_xboole_0(k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1)))),sK4(k1_relat_1(sK1),sK1)) = sK4(k1_relat_1(sK1),sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | k6_relat_1(k1_relat_1(sK1)) = sK1
    | ~ spl5_98
    | ~ spl5_100 ),
    inference(duplicate_literal_removal,[],[f6488])).

fof(f6488,plain,
    ( k1_funct_1(k6_relat_1(k3_xboole_0(k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1)))),sK4(k1_relat_1(sK1),sK1)) = sK4(k1_relat_1(sK1),sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k6_relat_1(k1_relat_1(sK1)) = sK1
    | ~ spl5_98
    | ~ spl5_100 ),
    inference(resolution,[],[f2627,f71])).

fof(f5564,plain,
    ( spl5_114
    | ~ spl5_60
    | ~ spl5_84 ),
    inference(avatar_split_clause,[],[f5092,f1721,f1056,f5562])).

fof(f5562,plain,
    ( spl5_114
  <=> k1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK1)))),sK3(k6_relat_1(k1_relat_1(sK1)),sK1)) = sK3(k6_relat_1(k1_relat_1(sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_114])])).

fof(f5092,plain,
    ( k1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK1)))),sK3(k6_relat_1(k1_relat_1(sK1)),sK1)) = sK3(k6_relat_1(k1_relat_1(sK1)),sK1)
    | ~ spl5_60
    | ~ spl5_84 ),
    inference(resolution,[],[f4889,f1057])).

fof(f4889,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(k6_relat_1(k1_relat_1(sK1)),sK1),X0)
        | k1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(X0)))),sK3(k6_relat_1(k1_relat_1(sK1)),sK1)) = sK3(k6_relat_1(k1_relat_1(sK1)),sK1) )
    | ~ spl5_60
    | ~ spl5_84 ),
    inference(subsumption_resolution,[],[f4888,f63])).

fof(f4888,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(k6_relat_1(k1_relat_1(sK1)),sK1),X0)
        | ~ v1_funct_1(k6_relat_1(X0))
        | k1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(X0)))),sK3(k6_relat_1(k1_relat_1(sK1)),sK1)) = sK3(k6_relat_1(k1_relat_1(sK1)),sK1) )
    | ~ spl5_60
    | ~ spl5_84 ),
    inference(subsumption_resolution,[],[f4887,f62])).

fof(f4887,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(k6_relat_1(k1_relat_1(sK1)),sK1),X0)
        | ~ v1_relat_1(k6_relat_1(X0))
        | ~ v1_funct_1(k6_relat_1(X0))
        | k1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(X0)))),sK3(k6_relat_1(k1_relat_1(sK1)),sK1)) = sK3(k6_relat_1(k1_relat_1(sK1)),sK1) )
    | ~ spl5_60
    | ~ spl5_84 ),
    inference(superposition,[],[f1936,f121])).

fof(f1936,plain,
    ( ! [X7] :
        ( ~ r2_hidden(sK3(k6_relat_1(k1_relat_1(sK1)),sK1),k1_relat_1(X7))
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7)
        | k1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(sK1),X7))),sK3(k6_relat_1(k1_relat_1(sK1)),sK1)) = sK3(k6_relat_1(k1_relat_1(sK1)),sK1) )
    | ~ spl5_60
    | ~ spl5_84 ),
    inference(subsumption_resolution,[],[f1935,f62])).

fof(f1935,plain,
    ( ! [X7] :
        ( ~ v1_funct_1(X7)
        | ~ v1_relat_1(X7)
        | ~ r2_hidden(sK3(k6_relat_1(k1_relat_1(sK1)),sK1),k1_relat_1(X7))
        | ~ v1_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(sK1),X7))))
        | k1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(sK1),X7))),sK3(k6_relat_1(k1_relat_1(sK1)),sK1)) = sK3(k6_relat_1(k1_relat_1(sK1)),sK1) )
    | ~ spl5_60
    | ~ spl5_84 ),
    inference(subsumption_resolution,[],[f1920,f63])).

fof(f1920,plain,
    ( ! [X7] :
        ( ~ v1_funct_1(X7)
        | ~ v1_relat_1(X7)
        | ~ r2_hidden(sK3(k6_relat_1(k1_relat_1(sK1)),sK1),k1_relat_1(X7))
        | ~ v1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(sK1),X7))))
        | ~ v1_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(sK1),X7))))
        | k1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(sK1),X7))),sK3(k6_relat_1(k1_relat_1(sK1)),sK1)) = sK3(k6_relat_1(k1_relat_1(sK1)),sK1) )
    | ~ spl5_60
    | ~ spl5_84 ),
    inference(resolution,[],[f1800,f69])).

fof(f4492,plain,
    ( spl5_112
    | ~ spl5_6
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f2142,f196,f136,f4490])).

fof(f4490,plain,
    ( spl5_112
  <=> k1_funct_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))) = sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_112])])).

fof(f2142,plain,
    ( k1_funct_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))) = sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl5_6
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f2127,f54])).

fof(f2127,plain,
    ( k1_funct_1(k6_relat_1(k3_xboole_0(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),sK0)),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))) = sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl5_6
    | ~ spl5_14 ),
    inference(resolution,[],[f605,f137])).

fof(f605,plain,
    ( ! [X36] :
        ( ~ r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),X36)
        | k1_funct_1(k6_relat_1(k3_xboole_0(X36,sK0)),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))) = sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))) )
    | ~ spl5_14 ),
    inference(resolution,[],[f180,f197])).

fof(f3343,plain,
    ( spl5_110
    | ~ spl5_0
    | ~ spl5_2
    | spl5_57
    | ~ spl5_98 ),
    inference(avatar_split_clause,[],[f3150,f2315,f892,f84,f77,f3341])).

fof(f3341,plain,
    ( spl5_110
  <=> k1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),k6_relat_1(k1_relat_1(sK1))))),sK4(k1_relat_1(sK1),sK1)) = sK4(k1_relat_1(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_110])])).

fof(f3150,plain,
    ( k1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),k6_relat_1(k1_relat_1(sK1))))),sK4(k1_relat_1(sK1),sK1)) = sK4(k1_relat_1(sK1),sK1)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_57
    | ~ spl5_98 ),
    inference(subsumption_resolution,[],[f3149,f893])).

fof(f3149,plain,
    ( k1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),k6_relat_1(k1_relat_1(sK1))))),sK4(k1_relat_1(sK1),sK1)) = sK4(k1_relat_1(sK1),sK1)
    | k6_relat_1(k1_relat_1(sK1)) = sK1
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_98 ),
    inference(subsumption_resolution,[],[f3148,f78])).

fof(f3148,plain,
    ( k1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),k6_relat_1(k1_relat_1(sK1))))),sK4(k1_relat_1(sK1),sK1)) = sK4(k1_relat_1(sK1),sK1)
    | ~ v1_relat_1(sK1)
    | k6_relat_1(k1_relat_1(sK1)) = sK1
    | ~ spl5_2
    | ~ spl5_98 ),
    inference(subsumption_resolution,[],[f3144,f85])).

fof(f3144,plain,
    ( k1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),k6_relat_1(k1_relat_1(sK1))))),sK4(k1_relat_1(sK1),sK1)) = sK4(k1_relat_1(sK1),sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k6_relat_1(k1_relat_1(sK1)) = sK1
    | ~ spl5_98 ),
    inference(resolution,[],[f2836,f71])).

fof(f2836,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(k1_relat_1(sK1),sK1),X0)
        | k1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),k6_relat_1(X0)))),sK4(k1_relat_1(sK1),sK1)) = sK4(k1_relat_1(sK1),sK1) )
    | ~ spl5_98 ),
    inference(subsumption_resolution,[],[f2835,f63])).

fof(f2835,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(k1_relat_1(sK1),sK1),X0)
        | ~ v1_funct_1(k6_relat_1(X0))
        | k1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),k6_relat_1(X0)))),sK4(k1_relat_1(sK1),sK1)) = sK4(k1_relat_1(sK1),sK1) )
    | ~ spl5_98 ),
    inference(subsumption_resolution,[],[f2830,f62])).

fof(f2830,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(k1_relat_1(sK1),sK1),X0)
        | ~ v1_relat_1(k6_relat_1(X0))
        | ~ v1_funct_1(k6_relat_1(X0))
        | k1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),k6_relat_1(X0)))),sK4(k1_relat_1(sK1),sK1)) = sK4(k1_relat_1(sK1),sK1) )
    | ~ spl5_98 ),
    inference(superposition,[],[f2639,f121])).

fof(f2639,plain,
    ( ! [X8] :
        ( ~ r2_hidden(sK4(k1_relat_1(sK1),sK1),k1_relat_1(X8))
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8)
        | k1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),X8))),sK4(k1_relat_1(sK1),sK1)) = sK4(k1_relat_1(sK1),sK1) )
    | ~ spl5_98 ),
    inference(subsumption_resolution,[],[f2638,f62])).

fof(f2638,plain,
    ( ! [X8] :
        ( ~ r2_hidden(sK4(k1_relat_1(sK1),sK1),k1_relat_1(X8))
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8)
        | ~ v1_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),X8))))
        | k1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),X8))),sK4(k1_relat_1(sK1),sK1)) = sK4(k1_relat_1(sK1),sK1) )
    | ~ spl5_98 ),
    inference(subsumption_resolution,[],[f2622,f63])).

fof(f2622,plain,
    ( ! [X8] :
        ( ~ r2_hidden(sK4(k1_relat_1(sK1),sK1),k1_relat_1(X8))
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8)
        | ~ v1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),X8))))
        | ~ v1_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),X8))))
        | k1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),X8))),sK4(k1_relat_1(sK1),sK1)) = sK4(k1_relat_1(sK1),sK1) )
    | ~ spl5_98 ),
    inference(resolution,[],[f2316,f69])).

fof(f3013,plain,
    ( spl5_108
    | ~ spl5_0
    | ~ spl5_2
    | spl5_57
    | ~ spl5_98 ),
    inference(avatar_split_clause,[],[f2834,f2315,f892,f84,f77,f3011])).

fof(f3011,plain,
    ( spl5_108
  <=> k1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1))),sK4(k1_relat_1(sK1),sK1)) = sK4(k1_relat_1(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_108])])).

fof(f2834,plain,
    ( k1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1))),sK4(k1_relat_1(sK1),sK1)) = sK4(k1_relat_1(sK1),sK1)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_57
    | ~ spl5_98 ),
    inference(subsumption_resolution,[],[f2833,f893])).

fof(f2833,plain,
    ( k1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1))),sK4(k1_relat_1(sK1),sK1)) = sK4(k1_relat_1(sK1),sK1)
    | k6_relat_1(k1_relat_1(sK1)) = sK1
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_98 ),
    inference(subsumption_resolution,[],[f2832,f85])).

fof(f2832,plain,
    ( ~ v1_funct_1(sK1)
    | k1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1))),sK4(k1_relat_1(sK1),sK1)) = sK4(k1_relat_1(sK1),sK1)
    | k6_relat_1(k1_relat_1(sK1)) = sK1
    | ~ spl5_0
    | ~ spl5_98 ),
    inference(subsumption_resolution,[],[f2831,f78])).

fof(f2831,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | k1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1))),sK4(k1_relat_1(sK1),sK1)) = sK4(k1_relat_1(sK1),sK1)
    | k6_relat_1(k1_relat_1(sK1)) = sK1
    | ~ spl5_98 ),
    inference(duplicate_literal_removal,[],[f2827])).

fof(f2827,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | k1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1))),sK4(k1_relat_1(sK1),sK1)) = sK4(k1_relat_1(sK1),sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k6_relat_1(k1_relat_1(sK1)) = sK1
    | ~ spl5_98 ),
    inference(resolution,[],[f2639,f71])).

fof(f2646,plain,
    ( spl5_106
    | spl5_73
    | spl5_95 ),
    inference(avatar_split_clause,[],[f1939,f1909,f1580,f2644])).

fof(f2644,plain,
    ( spl5_106
  <=> k1_funct_1(k6_relat_1(sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))),sK3(sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_funct_1(sK1,sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))))) = sK3(sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_funct_1(sK1,sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_106])])).

fof(f1580,plain,
    ( spl5_73
  <=> k1_funct_1(sK1,sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))) != sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).

fof(f1909,plain,
    ( spl5_95
  <=> ~ r2_hidden(sK3(sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_funct_1(sK1,sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))))),k1_funct_1(sK1,sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_95])])).

fof(f1939,plain,
    ( k1_funct_1(k6_relat_1(sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))),sK3(sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_funct_1(sK1,sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))))) = sK3(sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_funct_1(sK1,sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))))
    | ~ spl5_73
    | ~ spl5_95 ),
    inference(subsumption_resolution,[],[f1937,f1581])).

fof(f1581,plain,
    ( k1_funct_1(sK1,sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))) != sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))
    | ~ spl5_73 ),
    inference(avatar_component_clause,[],[f1580])).

fof(f1937,plain,
    ( k1_funct_1(k6_relat_1(sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))),sK3(sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_funct_1(sK1,sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))))) = sK3(sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_funct_1(sK1,sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))))
    | k1_funct_1(sK1,sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))) = sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))
    | ~ spl5_95 ),
    inference(resolution,[],[f1910,f184])).

fof(f184,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK3(X5,X6),X6)
      | k1_funct_1(k6_relat_1(X5),sK3(X5,X6)) = sK3(X5,X6)
      | X5 = X6 ) ),
    inference(subsumption_resolution,[],[f183,f62])).

fof(f183,plain,(
    ! [X6,X5] :
      ( ~ v1_relat_1(k6_relat_1(X5))
      | k1_funct_1(k6_relat_1(X5),sK3(X5,X6)) = sK3(X5,X6)
      | r2_hidden(sK3(X5,X6),X6)
      | X5 = X6 ) ),
    inference(subsumption_resolution,[],[f176,f63])).

fof(f176,plain,(
    ! [X6,X5] :
      ( ~ v1_funct_1(k6_relat_1(X5))
      | ~ v1_relat_1(k6_relat_1(X5))
      | k1_funct_1(k6_relat_1(X5),sK3(X5,X6)) = sK3(X5,X6)
      | r2_hidden(sK3(X5,X6),X6)
      | X5 = X6 ) ),
    inference(resolution,[],[f69,f48])).

fof(f1910,plain,
    ( ~ r2_hidden(sK3(sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_funct_1(sK1,sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))))),k1_funct_1(sK1,sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))))
    | ~ spl5_95 ),
    inference(avatar_component_clause,[],[f1909])).

fof(f2615,plain,
    ( spl5_104
    | spl5_73
    | spl5_89 ),
    inference(avatar_split_clause,[],[f1894,f1870,f1580,f2613])).

fof(f2613,plain,
    ( spl5_104
  <=> k1_funct_1(k6_relat_1(sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))),sK3(k1_funct_1(sK1,sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))),sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))))) = sK3(k1_funct_1(sK1,sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))),sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_104])])).

fof(f1870,plain,
    ( spl5_89
  <=> ~ r2_hidden(sK3(k1_funct_1(sK1,sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))),sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))),k1_funct_1(sK1,sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_89])])).

fof(f1894,plain,
    ( k1_funct_1(k6_relat_1(sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))),sK3(k1_funct_1(sK1,sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))),sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))))) = sK3(k1_funct_1(sK1,sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))),sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))))
    | ~ spl5_73
    | ~ spl5_89 ),
    inference(subsumption_resolution,[],[f1892,f1581])).

fof(f1892,plain,
    ( k1_funct_1(k6_relat_1(sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))),sK3(k1_funct_1(sK1,sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))),sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))))) = sK3(k1_funct_1(sK1,sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))),sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))))
    | k1_funct_1(sK1,sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))) = sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))
    | ~ spl5_89 ),
    inference(resolution,[],[f1871,f182])).

fof(f182,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK3(X4,X3),X4)
      | k1_funct_1(k6_relat_1(X3),sK3(X4,X3)) = sK3(X4,X3)
      | X3 = X4 ) ),
    inference(subsumption_resolution,[],[f181,f62])).

fof(f181,plain,(
    ! [X4,X3] :
      ( ~ v1_relat_1(k6_relat_1(X3))
      | k1_funct_1(k6_relat_1(X3),sK3(X4,X3)) = sK3(X4,X3)
      | r2_hidden(sK3(X4,X3),X4)
      | X3 = X4 ) ),
    inference(subsumption_resolution,[],[f175,f63])).

fof(f175,plain,(
    ! [X4,X3] :
      ( ~ v1_funct_1(k6_relat_1(X3))
      | ~ v1_relat_1(k6_relat_1(X3))
      | k1_funct_1(k6_relat_1(X3),sK3(X4,X3)) = sK3(X4,X3)
      | r2_hidden(sK3(X4,X3),X4)
      | X3 = X4 ) ),
    inference(resolution,[],[f69,f48])).

fof(f1871,plain,
    ( ~ r2_hidden(sK3(k1_funct_1(sK1,sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))),sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))),k1_funct_1(sK1,sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))))
    | ~ spl5_89 ),
    inference(avatar_component_clause,[],[f1870])).

fof(f2608,plain,
    ( spl5_102
    | ~ spl5_9
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f482,f368,f145,f2606])).

fof(f2606,plain,
    ( spl5_102
  <=> ! [X0] :
        ( ~ r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(X0))
        | r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(k5_relat_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(sK1))),X0)))
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_102])])).

fof(f368,plain,
    ( spl5_28
  <=> k1_funct_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(sK1))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))) = sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f482,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k3_xboole_0(sK0,k1_relat_1(sK1)))
        | ~ r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(k5_relat_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(sK1))),X0))) )
    | ~ spl5_28 ),
    inference(forward_demodulation,[],[f481,f121])).

fof(f481,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(X0))
        | ~ v1_funct_1(X0)
        | ~ r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(sK1)))))
        | ~ v1_relat_1(X0)
        | r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(k5_relat_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(sK1))),X0))) )
    | ~ spl5_28 ),
    inference(subsumption_resolution,[],[f480,f63])).

fof(f480,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(sK1))))
        | ~ r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(sK1)))))
        | ~ v1_relat_1(X0)
        | r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(k5_relat_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(sK1))),X0))) )
    | ~ spl5_28 ),
    inference(subsumption_resolution,[],[f478,f62])).

fof(f478,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(sK1))))
        | ~ v1_funct_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(sK1))))
        | ~ r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(sK1)))))
        | ~ v1_relat_1(X0)
        | r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(k5_relat_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(sK1))),X0))) )
    | ~ spl5_28 ),
    inference(superposition,[],[f60,f369])).

fof(f369,plain,
    ( k1_funct_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(sK1))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))) = sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f368])).

fof(f2450,plain,
    ( ~ spl5_0
    | ~ spl5_2
    | spl5_57
    | spl5_101 ),
    inference(avatar_contradiction_clause,[],[f2449])).

fof(f2449,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_57
    | ~ spl5_101 ),
    inference(subsumption_resolution,[],[f2448,f893])).

fof(f2448,plain,
    ( k6_relat_1(k1_relat_1(sK1)) = sK1
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_101 ),
    inference(subsumption_resolution,[],[f2447,f78])).

fof(f2447,plain,
    ( ~ v1_relat_1(sK1)
    | k6_relat_1(k1_relat_1(sK1)) = sK1
    | ~ spl5_2
    | ~ spl5_101 ),
    inference(subsumption_resolution,[],[f2446,f85])).

fof(f2446,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k6_relat_1(k1_relat_1(sK1)) = sK1
    | ~ spl5_101 ),
    inference(resolution,[],[f2322,f71])).

fof(f2322,plain,
    ( ~ r2_hidden(sK4(k1_relat_1(sK1),sK1),k1_relat_1(sK1))
    | ~ spl5_101 ),
    inference(avatar_component_clause,[],[f2321])).

fof(f2321,plain,
    ( spl5_101
  <=> ~ r2_hidden(sK4(k1_relat_1(sK1),sK1),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_101])])).

fof(f2323,plain,
    ( spl5_98
    | ~ spl5_101
    | ~ spl5_54 ),
    inference(avatar_split_clause,[],[f1679,f889,f2321,f2315])).

fof(f889,plain,
    ( spl5_54
  <=> k1_funct_1(k6_relat_1(k1_relat_1(sK1)),sK4(k1_relat_1(sK1),sK1)) = sK4(k1_relat_1(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).

fof(f1679,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(k1_relat_1(sK1),sK1),k1_relat_1(sK1))
        | ~ r2_hidden(sK4(k1_relat_1(sK1),sK1),k1_relat_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | r2_hidden(sK4(k1_relat_1(sK1),sK1),k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),X0))) )
    | ~ spl5_54 ),
    inference(forward_demodulation,[],[f1678,f121])).

fof(f1678,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(k1_relat_1(sK1),sK1),k1_relat_1(X0))
        | ~ v1_funct_1(X0)
        | ~ r2_hidden(sK4(k1_relat_1(sK1),sK1),k1_relat_1(k6_relat_1(k1_relat_1(sK1))))
        | ~ v1_relat_1(X0)
        | r2_hidden(sK4(k1_relat_1(sK1),sK1),k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),X0))) )
    | ~ spl5_54 ),
    inference(subsumption_resolution,[],[f1677,f63])).

fof(f1677,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(k1_relat_1(sK1),sK1),k1_relat_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_1(k6_relat_1(k1_relat_1(sK1)))
        | ~ r2_hidden(sK4(k1_relat_1(sK1),sK1),k1_relat_1(k6_relat_1(k1_relat_1(sK1))))
        | ~ v1_relat_1(X0)
        | r2_hidden(sK4(k1_relat_1(sK1),sK1),k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),X0))) )
    | ~ spl5_54 ),
    inference(subsumption_resolution,[],[f1675,f62])).

fof(f1675,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(k1_relat_1(sK1),sK1),k1_relat_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(k6_relat_1(k1_relat_1(sK1)))
        | ~ v1_funct_1(k6_relat_1(k1_relat_1(sK1)))
        | ~ r2_hidden(sK4(k1_relat_1(sK1),sK1),k1_relat_1(k6_relat_1(k1_relat_1(sK1))))
        | ~ v1_relat_1(X0)
        | r2_hidden(sK4(k1_relat_1(sK1),sK1),k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),X0))) )
    | ~ spl5_54 ),
    inference(superposition,[],[f60,f890])).

fof(f890,plain,
    ( k1_funct_1(k6_relat_1(k1_relat_1(sK1)),sK4(k1_relat_1(sK1),sK1)) = sK4(k1_relat_1(sK1),sK1)
    | ~ spl5_54 ),
    inference(avatar_component_clause,[],[f889])).

fof(f2241,plain,
    ( spl5_64
    | spl5_78
    | spl5_67 ),
    inference(avatar_split_clause,[],[f1345,f1333,f1648,f1209])).

fof(f1209,plain,
    ( spl5_64
  <=> k1_funct_1(sK1,sK4(k1_relat_1(sK1),sK1)) = sK4(k1_relat_1(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).

fof(f1648,plain,
    ( spl5_78
  <=> k1_funct_1(k6_relat_1(sK4(k1_relat_1(sK1),sK1)),sK3(k1_funct_1(sK1,sK4(k1_relat_1(sK1),sK1)),sK4(k1_relat_1(sK1),sK1))) = sK3(k1_funct_1(sK1,sK4(k1_relat_1(sK1),sK1)),sK4(k1_relat_1(sK1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_78])])).

fof(f1333,plain,
    ( spl5_67
  <=> ~ r2_hidden(sK3(k1_funct_1(sK1,sK4(k1_relat_1(sK1),sK1)),sK4(k1_relat_1(sK1),sK1)),k1_funct_1(sK1,sK4(k1_relat_1(sK1),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_67])])).

fof(f1345,plain,
    ( k1_funct_1(k6_relat_1(sK4(k1_relat_1(sK1),sK1)),sK3(k1_funct_1(sK1,sK4(k1_relat_1(sK1),sK1)),sK4(k1_relat_1(sK1),sK1))) = sK3(k1_funct_1(sK1,sK4(k1_relat_1(sK1),sK1)),sK4(k1_relat_1(sK1),sK1))
    | k1_funct_1(sK1,sK4(k1_relat_1(sK1),sK1)) = sK4(k1_relat_1(sK1),sK1)
    | ~ spl5_67 ),
    inference(resolution,[],[f1334,f182])).

fof(f1334,plain,
    ( ~ r2_hidden(sK3(k1_funct_1(sK1,sK4(k1_relat_1(sK1),sK1)),sK4(k1_relat_1(sK1),sK1)),k1_funct_1(sK1,sK4(k1_relat_1(sK1),sK1)))
    | ~ spl5_67 ),
    inference(avatar_component_clause,[],[f1333])).

fof(f1979,plain,
    ( spl5_96
    | spl5_65
    | spl5_81 ),
    inference(avatar_split_clause,[],[f1668,f1657,f1206,f1977])).

fof(f1977,plain,
    ( spl5_96
  <=> k1_funct_1(k6_relat_1(k1_funct_1(sK1,sK4(k1_relat_1(sK1),sK1))),sK3(sK4(k1_relat_1(sK1),sK1),k1_funct_1(sK1,sK4(k1_relat_1(sK1),sK1)))) = sK3(sK4(k1_relat_1(sK1),sK1),k1_funct_1(sK1,sK4(k1_relat_1(sK1),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_96])])).

fof(f1206,plain,
    ( spl5_65
  <=> k1_funct_1(sK1,sK4(k1_relat_1(sK1),sK1)) != sK4(k1_relat_1(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_65])])).

fof(f1657,plain,
    ( spl5_81
  <=> ~ r2_hidden(sK3(sK4(k1_relat_1(sK1),sK1),k1_funct_1(sK1,sK4(k1_relat_1(sK1),sK1))),sK4(k1_relat_1(sK1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_81])])).

fof(f1668,plain,
    ( k1_funct_1(k6_relat_1(k1_funct_1(sK1,sK4(k1_relat_1(sK1),sK1))),sK3(sK4(k1_relat_1(sK1),sK1),k1_funct_1(sK1,sK4(k1_relat_1(sK1),sK1)))) = sK3(sK4(k1_relat_1(sK1),sK1),k1_funct_1(sK1,sK4(k1_relat_1(sK1),sK1)))
    | ~ spl5_65
    | ~ spl5_81 ),
    inference(subsumption_resolution,[],[f1666,f1207])).

fof(f1207,plain,
    ( k1_funct_1(sK1,sK4(k1_relat_1(sK1),sK1)) != sK4(k1_relat_1(sK1),sK1)
    | ~ spl5_65 ),
    inference(avatar_component_clause,[],[f1206])).

fof(f1666,plain,
    ( k1_funct_1(k6_relat_1(k1_funct_1(sK1,sK4(k1_relat_1(sK1),sK1))),sK3(sK4(k1_relat_1(sK1),sK1),k1_funct_1(sK1,sK4(k1_relat_1(sK1),sK1)))) = sK3(sK4(k1_relat_1(sK1),sK1),k1_funct_1(sK1,sK4(k1_relat_1(sK1),sK1)))
    | k1_funct_1(sK1,sK4(k1_relat_1(sK1),sK1)) = sK4(k1_relat_1(sK1),sK1)
    | ~ spl5_81 ),
    inference(resolution,[],[f1658,f182])).

fof(f1658,plain,
    ( ~ r2_hidden(sK3(sK4(k1_relat_1(sK1),sK1),k1_funct_1(sK1,sK4(k1_relat_1(sK1),sK1))),sK4(k1_relat_1(sK1),sK1))
    | ~ spl5_81 ),
    inference(avatar_component_clause,[],[f1657])).

fof(f1950,plain,
    ( spl5_92
    | spl5_73
    | spl5_95 ),
    inference(avatar_split_clause,[],[f1943,f1909,f1580,f1900])).

fof(f1900,plain,
    ( spl5_92
  <=> r2_hidden(sK3(sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_funct_1(sK1,sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))))),sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_92])])).

fof(f1943,plain,
    ( r2_hidden(sK3(sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_funct_1(sK1,sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))))),sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))))
    | ~ spl5_73
    | ~ spl5_95 ),
    inference(subsumption_resolution,[],[f1938,f1581])).

fof(f1938,plain,
    ( r2_hidden(sK3(sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_funct_1(sK1,sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))))),sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))))
    | k1_funct_1(sK1,sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))) = sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))
    | ~ spl5_95 ),
    inference(resolution,[],[f1910,f48])).

fof(f1944,plain,
    ( spl5_90
    | spl5_73
    | spl5_89 ),
    inference(avatar_split_clause,[],[f1898,f1870,f1580,f1873])).

fof(f1873,plain,
    ( spl5_90
  <=> r2_hidden(sK3(k1_funct_1(sK1,sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))),sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))),sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_90])])).

fof(f1898,plain,
    ( r2_hidden(sK3(k1_funct_1(sK1,sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))),sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))),sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))))
    | ~ spl5_73
    | ~ spl5_89 ),
    inference(subsumption_resolution,[],[f1893,f1581])).

fof(f1893,plain,
    ( r2_hidden(sK3(k1_funct_1(sK1,sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))),sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))),sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))))
    | k1_funct_1(sK1,sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))) = sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))
    | ~ spl5_89 ),
    inference(resolution,[],[f1871,f48])).

fof(f1942,plain,
    ( spl5_73
    | spl5_93
    | spl5_95 ),
    inference(avatar_contradiction_clause,[],[f1941])).

fof(f1941,plain,
    ( $false
    | ~ spl5_73
    | ~ spl5_93
    | ~ spl5_95 ),
    inference(subsumption_resolution,[],[f1940,f1581])).

fof(f1940,plain,
    ( k1_funct_1(sK1,sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))) = sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))
    | ~ spl5_93
    | ~ spl5_95 ),
    inference(subsumption_resolution,[],[f1938,f1904])).

fof(f1904,plain,
    ( ~ r2_hidden(sK3(sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_funct_1(sK1,sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))))),sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))))
    | ~ spl5_93 ),
    inference(avatar_component_clause,[],[f1903])).

fof(f1903,plain,
    ( spl5_93
  <=> ~ r2_hidden(sK3(sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_funct_1(sK1,sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))))),sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_93])])).

fof(f1911,plain,
    ( ~ spl5_93
    | ~ spl5_95
    | spl5_73 ),
    inference(avatar_split_clause,[],[f1865,f1580,f1909,f1903])).

fof(f1865,plain,
    ( ~ r2_hidden(sK3(sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_funct_1(sK1,sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))))),k1_funct_1(sK1,sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))))
    | ~ r2_hidden(sK3(sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_funct_1(sK1,sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))))),sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))))
    | ~ spl5_73 ),
    inference(extensionality_resolution,[],[f49,f1581])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | ~ r2_hidden(sK3(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1897,plain,
    ( spl5_73
    | spl5_89
    | spl5_91 ),
    inference(avatar_contradiction_clause,[],[f1896])).

fof(f1896,plain,
    ( $false
    | ~ spl5_73
    | ~ spl5_89
    | ~ spl5_91 ),
    inference(subsumption_resolution,[],[f1895,f1581])).

fof(f1895,plain,
    ( k1_funct_1(sK1,sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))) = sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))
    | ~ spl5_89
    | ~ spl5_91 ),
    inference(subsumption_resolution,[],[f1893,f1877])).

fof(f1877,plain,
    ( ~ r2_hidden(sK3(k1_funct_1(sK1,sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))),sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))),sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))))
    | ~ spl5_91 ),
    inference(avatar_component_clause,[],[f1876])).

fof(f1876,plain,
    ( spl5_91
  <=> ~ r2_hidden(sK3(k1_funct_1(sK1,sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))),sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))),sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_91])])).

fof(f1878,plain,
    ( ~ spl5_89
    | ~ spl5_91
    | spl5_73 ),
    inference(avatar_split_clause,[],[f1864,f1580,f1876,f1870])).

fof(f1864,plain,
    ( ~ r2_hidden(sK3(k1_funct_1(sK1,sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))),sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))),sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))))
    | ~ r2_hidden(sK3(k1_funct_1(sK1,sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))),sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))),k1_funct_1(sK1,sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))))
    | ~ spl5_73 ),
    inference(extensionality_resolution,[],[f49,f1581])).

fof(f1855,plain,
    ( spl5_86
    | spl5_57
    | spl5_75 ),
    inference(avatar_split_clause,[],[f1631,f1620,f892,f1853])).

fof(f1620,plain,
    ( spl5_75
  <=> ~ r2_hidden(sK3(sK1,k6_relat_1(k1_relat_1(sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_75])])).

fof(f1631,plain,
    ( k1_funct_1(k6_relat_1(k6_relat_1(k1_relat_1(sK1))),sK3(sK1,k6_relat_1(k1_relat_1(sK1)))) = sK3(sK1,k6_relat_1(k1_relat_1(sK1)))
    | ~ spl5_57
    | ~ spl5_75 ),
    inference(subsumption_resolution,[],[f1629,f893])).

fof(f1629,plain,
    ( k1_funct_1(k6_relat_1(k6_relat_1(k1_relat_1(sK1))),sK3(sK1,k6_relat_1(k1_relat_1(sK1)))) = sK3(sK1,k6_relat_1(k1_relat_1(sK1)))
    | k6_relat_1(k1_relat_1(sK1)) = sK1
    | ~ spl5_75 ),
    inference(resolution,[],[f1621,f182])).

fof(f1621,plain,
    ( ~ r2_hidden(sK3(sK1,k6_relat_1(k1_relat_1(sK1))),sK1)
    | ~ spl5_75 ),
    inference(avatar_component_clause,[],[f1620])).

fof(f1723,plain,
    ( spl5_84
    | spl5_57
    | spl5_59 ),
    inference(avatar_split_clause,[],[f1603,f1053,f892,f1721])).

fof(f1053,plain,
    ( spl5_59
  <=> ~ r2_hidden(sK3(k6_relat_1(k1_relat_1(sK1)),sK1),k6_relat_1(k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_59])])).

fof(f1603,plain,
    ( k1_funct_1(k6_relat_1(sK1),sK3(k6_relat_1(k1_relat_1(sK1)),sK1)) = sK3(k6_relat_1(k1_relat_1(sK1)),sK1)
    | ~ spl5_57
    | ~ spl5_59 ),
    inference(subsumption_resolution,[],[f1065,f893])).

fof(f1065,plain,
    ( k1_funct_1(k6_relat_1(sK1),sK3(k6_relat_1(k1_relat_1(sK1)),sK1)) = sK3(k6_relat_1(k1_relat_1(sK1)),sK1)
    | k6_relat_1(k1_relat_1(sK1)) = sK1
    | ~ spl5_59 ),
    inference(resolution,[],[f1054,f182])).

fof(f1054,plain,
    ( ~ r2_hidden(sK3(k6_relat_1(k1_relat_1(sK1)),sK1),k6_relat_1(k1_relat_1(sK1)))
    | ~ spl5_59 ),
    inference(avatar_component_clause,[],[f1053])).

fof(f1674,plain,
    ( spl5_65
    | spl5_81
    | spl5_83 ),
    inference(avatar_contradiction_clause,[],[f1673])).

fof(f1673,plain,
    ( $false
    | ~ spl5_65
    | ~ spl5_81
    | ~ spl5_83 ),
    inference(subsumption_resolution,[],[f1672,f1207])).

fof(f1672,plain,
    ( k1_funct_1(sK1,sK4(k1_relat_1(sK1),sK1)) = sK4(k1_relat_1(sK1),sK1)
    | ~ spl5_81
    | ~ spl5_83 ),
    inference(subsumption_resolution,[],[f1670,f1658])).

fof(f1670,plain,
    ( r2_hidden(sK3(sK4(k1_relat_1(sK1),sK1),k1_funct_1(sK1,sK4(k1_relat_1(sK1),sK1))),sK4(k1_relat_1(sK1),sK1))
    | k1_funct_1(sK1,sK4(k1_relat_1(sK1),sK1)) = sK4(k1_relat_1(sK1),sK1)
    | ~ spl5_83 ),
    inference(resolution,[],[f1664,f48])).

fof(f1664,plain,
    ( ~ r2_hidden(sK3(sK4(k1_relat_1(sK1),sK1),k1_funct_1(sK1,sK4(k1_relat_1(sK1),sK1))),k1_funct_1(sK1,sK4(k1_relat_1(sK1),sK1)))
    | ~ spl5_83 ),
    inference(avatar_component_clause,[],[f1663])).

fof(f1663,plain,
    ( spl5_83
  <=> ~ r2_hidden(sK3(sK4(k1_relat_1(sK1),sK1),k1_funct_1(sK1,sK4(k1_relat_1(sK1),sK1))),k1_funct_1(sK1,sK4(k1_relat_1(sK1),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_83])])).

fof(f1665,plain,
    ( ~ spl5_81
    | ~ spl5_83
    | spl5_65 ),
    inference(avatar_split_clause,[],[f1652,f1206,f1663,f1657])).

fof(f1652,plain,
    ( ~ r2_hidden(sK3(sK4(k1_relat_1(sK1),sK1),k1_funct_1(sK1,sK4(k1_relat_1(sK1),sK1))),k1_funct_1(sK1,sK4(k1_relat_1(sK1),sK1)))
    | ~ r2_hidden(sK3(sK4(k1_relat_1(sK1),sK1),k1_funct_1(sK1,sK4(k1_relat_1(sK1),sK1))),sK4(k1_relat_1(sK1),sK1))
    | ~ spl5_65 ),
    inference(extensionality_resolution,[],[f49,f1207])).

fof(f1650,plain,
    ( spl5_78
    | ~ spl5_68 ),
    inference(avatar_split_clause,[],[f1613,f1336,f1648])).

fof(f1336,plain,
    ( spl5_68
  <=> r2_hidden(sK3(k1_funct_1(sK1,sK4(k1_relat_1(sK1),sK1)),sK4(k1_relat_1(sK1),sK1)),sK4(k1_relat_1(sK1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).

fof(f1613,plain,
    ( k1_funct_1(k6_relat_1(sK4(k1_relat_1(sK1),sK1)),sK3(k1_funct_1(sK1,sK4(k1_relat_1(sK1),sK1)),sK4(k1_relat_1(sK1),sK1))) = sK3(k1_funct_1(sK1,sK4(k1_relat_1(sK1),sK1)),sK4(k1_relat_1(sK1),sK1))
    | ~ spl5_68 ),
    inference(subsumption_resolution,[],[f1612,f62])).

fof(f1612,plain,
    ( ~ v1_relat_1(k6_relat_1(sK4(k1_relat_1(sK1),sK1)))
    | k1_funct_1(k6_relat_1(sK4(k1_relat_1(sK1),sK1)),sK3(k1_funct_1(sK1,sK4(k1_relat_1(sK1),sK1)),sK4(k1_relat_1(sK1),sK1))) = sK3(k1_funct_1(sK1,sK4(k1_relat_1(sK1),sK1)),sK4(k1_relat_1(sK1),sK1))
    | ~ spl5_68 ),
    inference(subsumption_resolution,[],[f1611,f63])).

fof(f1611,plain,
    ( ~ v1_funct_1(k6_relat_1(sK4(k1_relat_1(sK1),sK1)))
    | ~ v1_relat_1(k6_relat_1(sK4(k1_relat_1(sK1),sK1)))
    | k1_funct_1(k6_relat_1(sK4(k1_relat_1(sK1),sK1)),sK3(k1_funct_1(sK1,sK4(k1_relat_1(sK1),sK1)),sK4(k1_relat_1(sK1),sK1))) = sK3(k1_funct_1(sK1,sK4(k1_relat_1(sK1),sK1)),sK4(k1_relat_1(sK1),sK1))
    | ~ spl5_68 ),
    inference(resolution,[],[f1337,f69])).

fof(f1337,plain,
    ( r2_hidden(sK3(k1_funct_1(sK1,sK4(k1_relat_1(sK1),sK1)),sK4(k1_relat_1(sK1),sK1)),sK4(k1_relat_1(sK1),sK1))
    | ~ spl5_68 ),
    inference(avatar_component_clause,[],[f1336])).

fof(f1643,plain,
    ( spl5_64
    | spl5_68
    | spl5_67 ),
    inference(avatar_split_clause,[],[f1346,f1333,f1336,f1209])).

fof(f1346,plain,
    ( r2_hidden(sK3(k1_funct_1(sK1,sK4(k1_relat_1(sK1),sK1)),sK4(k1_relat_1(sK1),sK1)),sK4(k1_relat_1(sK1),sK1))
    | k1_funct_1(sK1,sK4(k1_relat_1(sK1),sK1)) = sK4(k1_relat_1(sK1),sK1)
    | ~ spl5_67 ),
    inference(resolution,[],[f1334,f48])).

fof(f1637,plain,
    ( spl5_57
    | spl5_75
    | spl5_77 ),
    inference(avatar_contradiction_clause,[],[f1636])).

fof(f1636,plain,
    ( $false
    | ~ spl5_57
    | ~ spl5_75
    | ~ spl5_77 ),
    inference(subsumption_resolution,[],[f1635,f893])).

fof(f1635,plain,
    ( k6_relat_1(k1_relat_1(sK1)) = sK1
    | ~ spl5_75
    | ~ spl5_77 ),
    inference(subsumption_resolution,[],[f1633,f1621])).

fof(f1633,plain,
    ( r2_hidden(sK3(sK1,k6_relat_1(k1_relat_1(sK1))),sK1)
    | k6_relat_1(k1_relat_1(sK1)) = sK1
    | ~ spl5_77 ),
    inference(resolution,[],[f1627,f48])).

fof(f1627,plain,
    ( ~ r2_hidden(sK3(sK1,k6_relat_1(k1_relat_1(sK1))),k6_relat_1(k1_relat_1(sK1)))
    | ~ spl5_77 ),
    inference(avatar_component_clause,[],[f1626])).

fof(f1626,plain,
    ( spl5_77
  <=> ~ r2_hidden(sK3(sK1,k6_relat_1(k1_relat_1(sK1))),k6_relat_1(k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_77])])).

fof(f1628,plain,
    ( ~ spl5_75
    | ~ spl5_77
    | spl5_57 ),
    inference(avatar_split_clause,[],[f1615,f892,f1626,f1620])).

fof(f1615,plain,
    ( ~ r2_hidden(sK3(sK1,k6_relat_1(k1_relat_1(sK1))),k6_relat_1(k1_relat_1(sK1)))
    | ~ r2_hidden(sK3(sK1,k6_relat_1(k1_relat_1(sK1))),sK1)
    | ~ spl5_57 ),
    inference(extensionality_resolution,[],[f49,f893])).

fof(f1602,plain,
    ( ~ spl5_0
    | ~ spl5_2
    | spl5_57
    | ~ spl5_64 ),
    inference(avatar_contradiction_clause,[],[f1601])).

fof(f1601,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_57
    | ~ spl5_64 ),
    inference(subsumption_resolution,[],[f893,f1587])).

fof(f1587,plain,
    ( k6_relat_1(k1_relat_1(sK1)) = sK1
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_64 ),
    inference(subsumption_resolution,[],[f1586,f78])).

fof(f1586,plain,
    ( ~ v1_relat_1(sK1)
    | k6_relat_1(k1_relat_1(sK1)) = sK1
    | ~ spl5_2
    | ~ spl5_64 ),
    inference(subsumption_resolution,[],[f1379,f85])).

fof(f1379,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k6_relat_1(k1_relat_1(sK1)) = sK1
    | ~ spl5_64 ),
    inference(trivial_inequality_removal,[],[f1376])).

fof(f1376,plain,
    ( sK4(k1_relat_1(sK1),sK1) != sK4(k1_relat_1(sK1),sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k6_relat_1(k1_relat_1(sK1)) = sK1
    | ~ spl5_64 ),
    inference(superposition,[],[f70,f1210])).

fof(f1210,plain,
    ( k1_funct_1(sK1,sK4(k1_relat_1(sK1),sK1)) = sK4(k1_relat_1(sK1),sK1)
    | ~ spl5_64 ),
    inference(avatar_component_clause,[],[f1209])).

fof(f70,plain,(
    ! [X1] :
      ( k1_funct_1(X1,sK4(k1_relat_1(X1),X1)) != sK4(k1_relat_1(X1),X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k6_relat_1(k1_relat_1(X1)) = X1 ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != X0
      | k1_funct_1(X1,sK4(X0,X1)) != sK4(X0,X1)
      | k6_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1600,plain,
    ( ~ spl5_0
    | ~ spl5_2
    | ~ spl5_60
    | spl5_63
    | ~ spl5_64 ),
    inference(avatar_contradiction_clause,[],[f1599])).

fof(f1599,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_60
    | ~ spl5_63
    | ~ spl5_64 ),
    inference(subsumption_resolution,[],[f1598,f1084])).

fof(f1084,plain,
    ( ~ r2_hidden(sK3(sK1,sK1),sK1)
    | ~ spl5_63 ),
    inference(avatar_component_clause,[],[f1083])).

fof(f1083,plain,
    ( spl5_63
  <=> ~ r2_hidden(sK3(sK1,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).

fof(f1598,plain,
    ( r2_hidden(sK3(sK1,sK1),sK1)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_60
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f1057,f1587])).

fof(f1597,plain,
    ( ~ spl5_0
    | ~ spl5_2
    | ~ spl5_38
    | ~ spl5_64
    | spl5_73 ),
    inference(avatar_contradiction_clause,[],[f1596])).

fof(f1596,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_38
    | ~ spl5_64
    | ~ spl5_73 ),
    inference(subsumption_resolution,[],[f1581,f1595])).

fof(f1595,plain,
    ( k1_funct_1(sK1,sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))) = sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_38
    | ~ spl5_64 ),
    inference(forward_demodulation,[],[f458,f1587])).

fof(f458,plain,
    ( k1_funct_1(k6_relat_1(k1_relat_1(sK1)),sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))) = sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))
    | ~ spl5_38 ),
    inference(avatar_component_clause,[],[f457])).

fof(f457,plain,
    ( spl5_38
  <=> k1_funct_1(k6_relat_1(k1_relat_1(sK1)),sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))) = sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f1585,plain,
    ( spl5_72
    | ~ spl5_38
    | spl5_59
    | spl5_61 ),
    inference(avatar_split_clause,[],[f1071,f1059,f1053,f457,f1583])).

fof(f1583,plain,
    ( spl5_72
  <=> k1_funct_1(sK1,sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))) = sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_72])])).

fof(f1059,plain,
    ( spl5_61
  <=> ~ r2_hidden(sK3(k6_relat_1(k1_relat_1(sK1)),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).

fof(f1071,plain,
    ( k1_funct_1(sK1,sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))) = sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))
    | ~ spl5_38
    | ~ spl5_59
    | ~ spl5_61 ),
    inference(backward_demodulation,[],[f1068,f458])).

fof(f1068,plain,
    ( k6_relat_1(k1_relat_1(sK1)) = sK1
    | ~ spl5_59
    | ~ spl5_61 ),
    inference(subsumption_resolution,[],[f1066,f1060])).

fof(f1060,plain,
    ( ~ r2_hidden(sK3(k6_relat_1(k1_relat_1(sK1)),sK1),sK1)
    | ~ spl5_61 ),
    inference(avatar_component_clause,[],[f1059])).

fof(f1066,plain,
    ( r2_hidden(sK3(k6_relat_1(k1_relat_1(sK1)),sK1),sK1)
    | k6_relat_1(k1_relat_1(sK1)) = sK1
    | ~ spl5_59 ),
    inference(resolution,[],[f1054,f48])).

fof(f1361,plain,
    ( ~ spl5_71
    | spl5_67
    | spl5_69 ),
    inference(avatar_split_clause,[],[f1351,f1339,f1333,f1359])).

fof(f1359,plain,
    ( spl5_71
  <=> ~ r2_hidden(sK3(sK4(k1_relat_1(sK1),sK1),sK4(k1_relat_1(sK1),sK1)),sK4(k1_relat_1(sK1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_71])])).

fof(f1339,plain,
    ( spl5_69
  <=> ~ r2_hidden(sK3(k1_funct_1(sK1,sK4(k1_relat_1(sK1),sK1)),sK4(k1_relat_1(sK1),sK1)),sK4(k1_relat_1(sK1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_69])])).

fof(f1351,plain,
    ( ~ r2_hidden(sK3(sK4(k1_relat_1(sK1),sK1),sK4(k1_relat_1(sK1),sK1)),sK4(k1_relat_1(sK1),sK1))
    | ~ spl5_67
    | ~ spl5_69 ),
    inference(backward_demodulation,[],[f1348,f1334])).

fof(f1348,plain,
    ( k1_funct_1(sK1,sK4(k1_relat_1(sK1),sK1)) = sK4(k1_relat_1(sK1),sK1)
    | ~ spl5_67
    | ~ spl5_69 ),
    inference(subsumption_resolution,[],[f1346,f1340])).

fof(f1340,plain,
    ( ~ r2_hidden(sK3(k1_funct_1(sK1,sK4(k1_relat_1(sK1),sK1)),sK4(k1_relat_1(sK1),sK1)),sK4(k1_relat_1(sK1),sK1))
    | ~ spl5_69 ),
    inference(avatar_component_clause,[],[f1339])).

fof(f1354,plain,
    ( spl5_64
    | spl5_67
    | spl5_69 ),
    inference(avatar_split_clause,[],[f1348,f1339,f1333,f1209])).

fof(f1350,plain,
    ( spl5_65
    | spl5_67
    | spl5_69 ),
    inference(avatar_contradiction_clause,[],[f1349])).

fof(f1349,plain,
    ( $false
    | ~ spl5_65
    | ~ spl5_67
    | ~ spl5_69 ),
    inference(subsumption_resolution,[],[f1348,f1207])).

fof(f1341,plain,
    ( ~ spl5_67
    | ~ spl5_69
    | spl5_65 ),
    inference(avatar_split_clause,[],[f1327,f1206,f1339,f1333])).

fof(f1327,plain,
    ( ~ r2_hidden(sK3(k1_funct_1(sK1,sK4(k1_relat_1(sK1),sK1)),sK4(k1_relat_1(sK1),sK1)),sK4(k1_relat_1(sK1),sK1))
    | ~ r2_hidden(sK3(k1_funct_1(sK1,sK4(k1_relat_1(sK1),sK1)),sK4(k1_relat_1(sK1),sK1)),k1_funct_1(sK1,sK4(k1_relat_1(sK1),sK1)))
    | ~ spl5_65 ),
    inference(extensionality_resolution,[],[f49,f1207])).

fof(f1211,plain,
    ( spl5_64
    | ~ spl5_54
    | spl5_59
    | spl5_61 ),
    inference(avatar_split_clause,[],[f1076,f1059,f1053,f889,f1209])).

fof(f1076,plain,
    ( k1_funct_1(sK1,sK4(k1_relat_1(sK1),sK1)) = sK4(k1_relat_1(sK1),sK1)
    | ~ spl5_54
    | ~ spl5_59
    | ~ spl5_61 ),
    inference(backward_demodulation,[],[f1068,f890])).

fof(f1090,plain,
    ( spl5_56
    | spl5_59
    | spl5_61 ),
    inference(avatar_split_clause,[],[f1068,f1059,f1053,f895])).

fof(f895,plain,
    ( spl5_56
  <=> k6_relat_1(k1_relat_1(sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).

fof(f1085,plain,
    ( ~ spl5_63
    | spl5_59
    | spl5_61 ),
    inference(avatar_split_clause,[],[f1077,f1059,f1053,f1083])).

fof(f1077,plain,
    ( ~ r2_hidden(sK3(sK1,sK1),sK1)
    | ~ spl5_59
    | ~ spl5_61 ),
    inference(backward_demodulation,[],[f1068,f1054])).

fof(f1070,plain,
    ( spl5_57
    | spl5_59
    | spl5_61 ),
    inference(avatar_contradiction_clause,[],[f1069])).

fof(f1069,plain,
    ( $false
    | ~ spl5_57
    | ~ spl5_59
    | ~ spl5_61 ),
    inference(subsumption_resolution,[],[f1068,f893])).

fof(f1061,plain,
    ( ~ spl5_59
    | ~ spl5_61
    | spl5_57 ),
    inference(avatar_split_clause,[],[f1047,f892,f1059,f1053])).

fof(f1047,plain,
    ( ~ r2_hidden(sK3(k6_relat_1(k1_relat_1(sK1)),sK1),sK1)
    | ~ r2_hidden(sK3(k6_relat_1(k1_relat_1(sK1)),sK1),k6_relat_1(k1_relat_1(sK1)))
    | ~ spl5_57 ),
    inference(extensionality_resolution,[],[f49,f893])).

fof(f897,plain,
    ( spl5_54
    | spl5_56
    | ~ spl5_0
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f836,f84,f77,f895,f889])).

fof(f836,plain,
    ( k6_relat_1(k1_relat_1(sK1)) = sK1
    | k1_funct_1(k6_relat_1(k1_relat_1(sK1)),sK4(k1_relat_1(sK1),sK1)) = sK4(k1_relat_1(sK1),sK1)
    | ~ spl5_0
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f834,f78])).

fof(f834,plain,
    ( ~ v1_relat_1(sK1)
    | k6_relat_1(k1_relat_1(sK1)) = sK1
    | k1_funct_1(k6_relat_1(k1_relat_1(sK1)),sK4(k1_relat_1(sK1),sK1)) = sK4(k1_relat_1(sK1),sK1)
    | ~ spl5_2 ),
    inference(resolution,[],[f192,f85])).

fof(f192,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k6_relat_1(k1_relat_1(X0)) = X0
      | k1_funct_1(k6_relat_1(k1_relat_1(X0)),sK4(k1_relat_1(X0),X0)) = sK4(k1_relat_1(X0),X0) ) ),
    inference(subsumption_resolution,[],[f191,f62])).

fof(f191,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k6_relat_1(k1_relat_1(X0)) = X0
      | ~ v1_relat_1(k6_relat_1(k1_relat_1(X0)))
      | k1_funct_1(k6_relat_1(k1_relat_1(X0)),sK4(k1_relat_1(X0),X0)) = sK4(k1_relat_1(X0),X0) ) ),
    inference(subsumption_resolution,[],[f189,f63])).

fof(f189,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k6_relat_1(k1_relat_1(X0)) = X0
      | ~ v1_funct_1(k6_relat_1(k1_relat_1(X0)))
      | ~ v1_relat_1(k6_relat_1(k1_relat_1(X0)))
      | k1_funct_1(k6_relat_1(k1_relat_1(X0)),sK4(k1_relat_1(X0),X0)) = sK4(k1_relat_1(X0),X0) ) ),
    inference(resolution,[],[f71,f69])).

fof(f559,plain,
    ( spl5_48
    | spl5_51
    | spl5_53 ),
    inference(avatar_split_clause,[],[f554,f549,f543,f519])).

fof(f519,plain,
    ( spl5_48
  <=> k1_funct_1(k6_relat_1(k1_relat_1(sK1)),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))) = sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f543,plain,
    ( spl5_51
  <=> ~ r2_hidden(sK3(k1_funct_1(k6_relat_1(k1_relat_1(sK1)),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))),k1_funct_1(k6_relat_1(k1_relat_1(sK1)),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).

fof(f549,plain,
    ( spl5_53
  <=> ~ r2_hidden(sK3(k1_funct_1(k6_relat_1(k1_relat_1(sK1)),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).

fof(f554,plain,
    ( k1_funct_1(k6_relat_1(k1_relat_1(sK1)),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))) = sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl5_51
    | ~ spl5_53 ),
    inference(subsumption_resolution,[],[f553,f550])).

fof(f550,plain,
    ( ~ r2_hidden(sK3(k1_funct_1(k6_relat_1(k1_relat_1(sK1)),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))))
    | ~ spl5_53 ),
    inference(avatar_component_clause,[],[f549])).

fof(f553,plain,
    ( r2_hidden(sK3(k1_funct_1(k6_relat_1(k1_relat_1(sK1)),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))))
    | k1_funct_1(k6_relat_1(k1_relat_1(sK1)),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))) = sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl5_51 ),
    inference(resolution,[],[f544,f48])).

fof(f544,plain,
    ( ~ r2_hidden(sK3(k1_funct_1(k6_relat_1(k1_relat_1(sK1)),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))),k1_funct_1(k6_relat_1(k1_relat_1(sK1)),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))))
    | ~ spl5_51 ),
    inference(avatar_component_clause,[],[f543])).

fof(f556,plain,
    ( spl5_49
    | spl5_51
    | spl5_53 ),
    inference(avatar_contradiction_clause,[],[f555])).

fof(f555,plain,
    ( $false
    | ~ spl5_49
    | ~ spl5_51
    | ~ spl5_53 ),
    inference(subsumption_resolution,[],[f554,f517])).

fof(f517,plain,
    ( k1_funct_1(k6_relat_1(k1_relat_1(sK1)),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))) != sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl5_49 ),
    inference(avatar_component_clause,[],[f516])).

fof(f516,plain,
    ( spl5_49
  <=> k1_funct_1(k6_relat_1(k1_relat_1(sK1)),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))) != sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).

fof(f551,plain,
    ( ~ spl5_51
    | ~ spl5_53
    | spl5_49 ),
    inference(avatar_split_clause,[],[f537,f516,f549,f543])).

fof(f537,plain,
    ( ~ r2_hidden(sK3(k1_funct_1(k6_relat_1(k1_relat_1(sK1)),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))))
    | ~ r2_hidden(sK3(k1_funct_1(k6_relat_1(k1_relat_1(sK1)),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))),k1_funct_1(k6_relat_1(k1_relat_1(sK1)),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))))
    | ~ spl5_49 ),
    inference(extensionality_resolution,[],[f49,f517])).

fof(f521,plain,
    ( spl5_48
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f498,f202,f519])).

fof(f202,plain,
    ( spl5_16
  <=> r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f498,plain,
    ( k1_funct_1(k6_relat_1(k1_relat_1(sK1)),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))) = sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f497,f62])).

fof(f497,plain,
    ( ~ v1_relat_1(k6_relat_1(k1_relat_1(sK1)))
    | k1_funct_1(k6_relat_1(k1_relat_1(sK1)),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))) = sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f496,f63])).

fof(f496,plain,
    ( ~ v1_funct_1(k6_relat_1(k1_relat_1(sK1)))
    | ~ v1_relat_1(k6_relat_1(k1_relat_1(sK1)))
    | k1_funct_1(k6_relat_1(k1_relat_1(sK1)),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))) = sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl5_16 ),
    inference(resolution,[],[f203,f69])).

fof(f203,plain,
    ( r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(sK1))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f202])).

fof(f514,plain,
    ( ~ spl5_45
    | ~ spl5_47
    | spl5_43 ),
    inference(avatar_split_clause,[],[f500,f486,f512,f506])).

fof(f506,plain,
    ( spl5_45
  <=> ~ r2_hidden(sK3(k1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))),k1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f512,plain,
    ( spl5_47
  <=> ~ r2_hidden(sK3(k1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).

fof(f486,plain,
    ( spl5_43
  <=> k1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))) != sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f500,plain,
    ( ~ r2_hidden(sK3(k1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))))
    | ~ r2_hidden(sK3(k1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))),k1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))))
    | ~ spl5_43 ),
    inference(extensionality_resolution,[],[f49,f487])).

fof(f487,plain,
    ( k1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))) != sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl5_43 ),
    inference(avatar_component_clause,[],[f486])).

fof(f491,plain,
    ( spl5_42
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f383,f136,f489])).

fof(f489,plain,
    ( spl5_42
  <=> k1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))) = sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f383,plain,
    ( k1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))) = sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f382,f62])).

fof(f382,plain,
    ( ~ v1_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))))
    | k1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))) = sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f376,f63])).

fof(f376,plain,
    ( ~ v1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))))
    | ~ v1_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))))
    | k1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))) = sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl5_6 ),
    inference(resolution,[],[f137,f69])).

fof(f469,plain,
    ( spl5_28
    | spl5_35
    | spl5_37 ),
    inference(avatar_split_clause,[],[f446,f441,f435,f368])).

fof(f435,plain,
    ( spl5_35
  <=> ~ r2_hidden(sK3(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_funct_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(sK1))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f441,plain,
    ( spl5_37
  <=> ~ r2_hidden(sK3(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_funct_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(sK1))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))))),k1_funct_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(sK1))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f446,plain,
    ( k1_funct_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(sK1))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))) = sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl5_35
    | ~ spl5_37 ),
    inference(subsumption_resolution,[],[f445,f436])).

fof(f436,plain,
    ( ~ r2_hidden(sK3(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_funct_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(sK1))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))))
    | ~ spl5_35 ),
    inference(avatar_component_clause,[],[f435])).

fof(f445,plain,
    ( r2_hidden(sK3(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_funct_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(sK1))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))))
    | k1_funct_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(sK1))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))) = sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl5_37 ),
    inference(resolution,[],[f442,f48])).

fof(f442,plain,
    ( ~ r2_hidden(sK3(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_funct_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(sK1))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))))),k1_funct_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(sK1))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))))
    | ~ spl5_37 ),
    inference(avatar_component_clause,[],[f441])).

fof(f466,plain,
    ( ~ spl5_41
    | spl5_35
    | spl5_37 ),
    inference(avatar_split_clause,[],[f449,f441,f435,f464])).

fof(f464,plain,
    ( spl5_41
  <=> ~ r2_hidden(sK3(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f449,plain,
    ( ~ r2_hidden(sK3(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))))
    | ~ spl5_35
    | ~ spl5_37 ),
    inference(backward_demodulation,[],[f446,f436])).

fof(f459,plain,
    ( spl5_38
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f325,f320,f457])).

fof(f320,plain,
    ( spl5_20
  <=> r2_hidden(sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f325,plain,
    ( k1_funct_1(k6_relat_1(k1_relat_1(sK1)),sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))) = sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f324,f62])).

fof(f324,plain,
    ( ~ v1_relat_1(k6_relat_1(k1_relat_1(sK1)))
    | k1_funct_1(k6_relat_1(k1_relat_1(sK1)),sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))) = sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f323,f63])).

fof(f323,plain,
    ( ~ v1_funct_1(k6_relat_1(k1_relat_1(sK1)))
    | ~ v1_relat_1(k6_relat_1(k1_relat_1(sK1)))
    | k1_funct_1(k6_relat_1(k1_relat_1(sK1)),sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))) = sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))
    | ~ spl5_20 ),
    inference(resolution,[],[f321,f69])).

fof(f321,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_relat_1(sK1))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f320])).

fof(f448,plain,
    ( spl5_29
    | spl5_35
    | spl5_37 ),
    inference(avatar_contradiction_clause,[],[f447])).

fof(f447,plain,
    ( $false
    | ~ spl5_29
    | ~ spl5_35
    | ~ spl5_37 ),
    inference(subsumption_resolution,[],[f446,f366])).

fof(f366,plain,
    ( k1_funct_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(sK1))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))) != sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f365])).

fof(f365,plain,
    ( spl5_29
  <=> k1_funct_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(sK1))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))) != sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f443,plain,
    ( ~ spl5_35
    | ~ spl5_37
    | spl5_29 ),
    inference(avatar_split_clause,[],[f393,f365,f441,f435])).

fof(f393,plain,
    ( ~ r2_hidden(sK3(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_funct_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(sK1))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))))),k1_funct_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(sK1))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))))
    | ~ r2_hidden(sK3(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_funct_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(sK1))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))))
    | ~ spl5_29 ),
    inference(extensionality_resolution,[],[f49,f366])).

fof(f419,plain,
    ( spl5_29
    | spl5_31
    | spl5_33 ),
    inference(avatar_contradiction_clause,[],[f418])).

fof(f418,plain,
    ( $false
    | ~ spl5_29
    | ~ spl5_31
    | ~ spl5_33 ),
    inference(subsumption_resolution,[],[f417,f366])).

fof(f417,plain,
    ( k1_funct_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(sK1))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))) = sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl5_31
    | ~ spl5_33 ),
    inference(subsumption_resolution,[],[f416,f405])).

fof(f405,plain,
    ( ~ r2_hidden(sK3(k1_funct_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(sK1))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))))
    | ~ spl5_33 ),
    inference(avatar_component_clause,[],[f404])).

fof(f404,plain,
    ( spl5_33
  <=> ~ r2_hidden(sK3(k1_funct_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(sK1))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f416,plain,
    ( r2_hidden(sK3(k1_funct_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(sK1))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))))
    | k1_funct_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(sK1))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))) = sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl5_31 ),
    inference(resolution,[],[f399,f48])).

fof(f399,plain,
    ( ~ r2_hidden(sK3(k1_funct_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(sK1))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))),k1_funct_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(sK1))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))))
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f398])).

fof(f398,plain,
    ( spl5_31
  <=> ~ r2_hidden(sK3(k1_funct_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(sK1))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))),k1_funct_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(sK1))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f406,plain,
    ( ~ spl5_31
    | ~ spl5_33
    | spl5_29 ),
    inference(avatar_split_clause,[],[f392,f365,f404,f398])).

fof(f392,plain,
    ( ~ r2_hidden(sK3(k1_funct_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(sK1))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))))
    | ~ r2_hidden(sK3(k1_funct_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(sK1))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))),k1_funct_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(sK1))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))))
    | ~ spl5_29 ),
    inference(extensionality_resolution,[],[f49,f366])).

fof(f370,plain,
    ( spl5_28
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f342,f142,f368])).

fof(f142,plain,
    ( spl5_8
  <=> r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k3_xboole_0(sK0,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f342,plain,
    ( k1_funct_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(sK1))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))) = sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f341,f62])).

fof(f341,plain,
    ( ~ v1_relat_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(sK1))))
    | k1_funct_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(sK1))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))) = sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f336,f63])).

fof(f336,plain,
    ( ~ v1_funct_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(sK1))))
    | ~ v1_relat_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(sK1))))
    | k1_funct_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(sK1))),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))) = sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl5_8 ),
    inference(resolution,[],[f143,f69])).

fof(f143,plain,
    ( r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k3_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f142])).

fof(f363,plain,
    ( spl5_26
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f315,f301,f361])).

fof(f361,plain,
    ( spl5_26
  <=> k1_funct_1(k6_relat_1(sK0),sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))) = sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f301,plain,
    ( spl5_18
  <=> r2_hidden(sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f315,plain,
    ( k1_funct_1(k6_relat_1(sK0),sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))) = sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f314,f62])).

fof(f314,plain,
    ( ~ v1_relat_1(k6_relat_1(sK0))
    | k1_funct_1(k6_relat_1(sK0),sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))) = sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f313,f63])).

fof(f313,plain,
    ( ~ v1_funct_1(k6_relat_1(sK0))
    | ~ v1_relat_1(k6_relat_1(sK0))
    | k1_funct_1(k6_relat_1(sK0),sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))) = sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))
    | ~ spl5_18 ),
    inference(resolution,[],[f302,f69])).

fof(f302,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),sK0)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f301])).

fof(f356,plain,
    ( spl5_24
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f310,f155,f354])).

fof(f354,plain,
    ( spl5_24
  <=> k1_funct_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(sK1))),sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))) = sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f155,plain,
    ( spl5_10
  <=> r2_hidden(sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k3_xboole_0(sK0,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f310,plain,
    ( k1_funct_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(sK1))),sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))) = sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f309,f62])).

fof(f309,plain,
    ( ~ v1_relat_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(sK1))))
    | k1_funct_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(sK1))),sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))) = sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f306,f63])).

fof(f306,plain,
    ( ~ v1_funct_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(sK1))))
    | ~ v1_relat_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(sK1))))
    | k1_funct_1(k6_relat_1(k3_xboole_0(sK0,k1_relat_1(sK1))),sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))) = sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))
    | ~ spl5_10 ),
    inference(resolution,[],[f156,f69])).

fof(f156,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k3_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f155])).

fof(f346,plain,
    ( spl5_16
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f335,f142,f202])).

fof(f335,plain,
    ( r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(sK1))
    | ~ spl5_8 ),
    inference(resolution,[],[f143,f66])).

fof(f344,plain,
    ( spl5_14
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f334,f142,f196])).

fof(f334,plain,
    ( r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),sK0)
    | ~ spl5_8 ),
    inference(resolution,[],[f143,f67])).

fof(f340,plain,
    ( ~ spl5_8
    | spl5_17 ),
    inference(avatar_contradiction_clause,[],[f339])).

fof(f339,plain,
    ( $false
    | ~ spl5_8
    | ~ spl5_17 ),
    inference(subsumption_resolution,[],[f335,f206])).

fof(f338,plain,
    ( ~ spl5_8
    | spl5_15 ),
    inference(avatar_contradiction_clause,[],[f337])).

fof(f337,plain,
    ( $false
    | ~ spl5_8
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f334,f200])).

fof(f200,plain,
    ( ~ r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),sK0)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl5_15
  <=> ~ r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f332,plain,
    ( spl5_22
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f281,f196,f330])).

fof(f281,plain,
    ( k1_funct_1(k6_relat_1(sK0),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))) = sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f280,f62])).

fof(f280,plain,
    ( ~ v1_relat_1(k6_relat_1(sK0))
    | k1_funct_1(k6_relat_1(sK0),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))) = sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f279,f63])).

fof(f279,plain,
    ( ~ v1_funct_1(k6_relat_1(sK0))
    | ~ v1_relat_1(k6_relat_1(sK0))
    | k1_funct_1(k6_relat_1(sK0),sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))) = sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl5_14 ),
    inference(resolution,[],[f197,f69])).

fof(f322,plain,
    ( spl5_20
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f305,f155,f320])).

fof(f305,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_relat_1(sK1))
    | ~ spl5_10 ),
    inference(resolution,[],[f156,f66])).

fof(f312,plain,
    ( spl5_18
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f304,f155,f301])).

fof(f304,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),sK0)
    | ~ spl5_10 ),
    inference(resolution,[],[f156,f67])).

fof(f308,plain,
    ( ~ spl5_10
    | spl5_19 ),
    inference(avatar_contradiction_clause,[],[f307])).

fof(f307,plain,
    ( $false
    | ~ spl5_10
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f304,f299])).

fof(f299,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),sK0)
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f298])).

fof(f298,plain,
    ( spl5_19
  <=> ~ r2_hidden(sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f303,plain,
    ( spl5_18
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f256,f161,f84,f77,f301])).

fof(f161,plain,
    ( spl5_12
  <=> r2_hidden(sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f256,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f255,f121])).

fof(f255,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_relat_1(k6_relat_1(sK0)))
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f254,f78])).

fof(f254,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_relat_1(k6_relat_1(sK0)))
    | ~ v1_relat_1(sK1)
    | ~ spl5_2
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f253,f63])).

fof(f253,plain,
    ( ~ v1_funct_1(k6_relat_1(sK0))
    | r2_hidden(sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_relat_1(k6_relat_1(sK0)))
    | ~ v1_relat_1(sK1)
    | ~ spl5_2
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f252,f62])).

fof(f252,plain,
    ( ~ v1_relat_1(k6_relat_1(sK0))
    | ~ v1_funct_1(k6_relat_1(sK0))
    | r2_hidden(sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_relat_1(k6_relat_1(sK0)))
    | ~ v1_relat_1(sK1)
    | ~ spl5_2
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f243,f85])).

fof(f243,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(k6_relat_1(sK0))
    | ~ v1_funct_1(k6_relat_1(sK0))
    | r2_hidden(sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_relat_1(k6_relat_1(sK0)))
    | ~ v1_relat_1(sK1)
    | ~ spl5_12 ),
    inference(resolution,[],[f58,f162])).

fof(f162,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f161])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f258,plain,
    ( spl5_14
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f249,f136,f84,f77,f196])).

fof(f249,plain,
    ( r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f248,f121])).

fof(f248,plain,
    ( r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(k6_relat_1(sK0)))
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f247,f78])).

fof(f247,plain,
    ( r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(k6_relat_1(sK0)))
    | ~ v1_relat_1(sK1)
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f246,f63])).

fof(f246,plain,
    ( ~ v1_funct_1(k6_relat_1(sK0))
    | r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(k6_relat_1(sK0)))
    | ~ v1_relat_1(sK1)
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f245,f62])).

fof(f245,plain,
    ( ~ v1_relat_1(k6_relat_1(sK0))
    | ~ v1_funct_1(k6_relat_1(sK0))
    | r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(k6_relat_1(sK0)))
    | ~ v1_relat_1(sK1)
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f242,f85])).

fof(f242,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(k6_relat_1(sK0))
    | ~ v1_funct_1(k6_relat_1(sK0))
    | r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(k6_relat_1(sK0)))
    | ~ v1_relat_1(sK1)
    | ~ spl5_6 ),
    inference(resolution,[],[f58,f137])).

fof(f251,plain,
    ( ~ spl5_0
    | ~ spl5_2
    | ~ spl5_6
    | spl5_15 ),
    inference(avatar_contradiction_clause,[],[f250])).

fof(f250,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f249,f200])).

fof(f207,plain,
    ( ~ spl5_15
    | ~ spl5_17
    | spl5_9 ),
    inference(avatar_split_clause,[],[f149,f145,f205,f199])).

fof(f149,plain,
    ( ~ r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(sK1))
    | ~ r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),sK0)
    | ~ spl5_9 ),
    inference(resolution,[],[f146,f65])).

fof(f172,plain,
    ( spl5_5
    | spl5_11
    | spl5_13 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | ~ spl5_5
    | ~ spl5_11
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f170,f92])).

fof(f170,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) = k3_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl5_11
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f169,f159])).

fof(f159,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k3_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl5_11
  <=> ~ r2_hidden(sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k3_xboole_0(sK0,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f169,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k3_xboole_0(sK0,k1_relat_1(sK1)))
    | k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) = k3_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl5_13 ),
    inference(resolution,[],[f165,f48])).

fof(f165,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl5_13
  <=> ~ r2_hidden(sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f166,plain,
    ( ~ spl5_11
    | ~ spl5_13
    | spl5_5 ),
    inference(avatar_split_clause,[],[f130,f91,f164,f158])).

fof(f130,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))
    | ~ r2_hidden(sK3(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k3_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl5_5 ),
    inference(extensionality_resolution,[],[f49,f92])).

fof(f153,plain,
    ( spl5_5
    | spl5_7
    | spl5_9 ),
    inference(avatar_contradiction_clause,[],[f152])).

fof(f152,plain,
    ( $false
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f151,f92])).

fof(f151,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) = k3_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl5_7
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f150,f146])).

fof(f150,plain,
    ( r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k3_xboole_0(sK0,k1_relat_1(sK1)))
    | k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) = k3_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl5_7 ),
    inference(resolution,[],[f140,f48])).

fof(f147,plain,
    ( ~ spl5_7
    | ~ spl5_9
    | spl5_5 ),
    inference(avatar_split_clause,[],[f129,f91,f145,f139])).

fof(f129,plain,
    ( ~ r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k3_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ r2_hidden(sK3(k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)),k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))
    | ~ spl5_5 ),
    inference(extensionality_resolution,[],[f49,f92])).

fof(f93,plain,(
    ~ spl5_5 ),
    inference(avatar_split_clause,[],[f72,f91])).

fof(f72,plain,(
    k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) != k3_xboole_0(sK0,k1_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f54,f40])).

fof(f40,plain,(
    k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) != k3_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) != k3_xboole_0(k1_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) != k3_xboole_0(k1_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t37_funct_1.p',t37_funct_1)).

fof(f86,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f39,f84])).

fof(f39,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f79,plain,(
    spl5_0 ),
    inference(avatar_split_clause,[],[f38,f77])).

fof(f38,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
