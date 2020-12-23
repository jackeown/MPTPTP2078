%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t43_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:23 EDT 2019

% Result     : Theorem 219.44s
% Output     : Refutation 219.44s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 345 expanded)
%              Number of leaves         :   21 ( 106 expanded)
%              Depth                    :   15
%              Number of atoms          :  464 (1360 expanded)
%              Number of equality atoms :  130 ( 488 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f57073,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f131,f1585,f18719,f18728,f33600,f57008,f57054,f57072])).

fof(f57072,plain,
    ( spl6_5
    | ~ spl6_56
    | ~ spl6_60 ),
    inference(avatar_contradiction_clause,[],[f57071])).

fof(f57071,plain,
    ( $false
    | ~ spl6_5
    | ~ spl6_56
    | ~ spl6_60 ),
    inference(subsumption_resolution,[],[f57070,f107])).

fof(f107,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(subsumption_resolution,[],[f106,f67])).

fof(f67,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t43_funct_1.p',dt_k6_relat_1)).

fof(f106,plain,(
    ! [X0] :
      ( k1_relat_1(k6_relat_1(X0)) = X0
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f100,f70])).

fof(f70,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t43_funct_1.p',fc3_funct_1)).

fof(f100,plain,(
    ! [X0] :
      ( k1_relat_1(k6_relat_1(X0)) = X0
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | k6_relat_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( k1_funct_1(X1,sK4(X0,X1)) != sK4(X0,X1)
            & r2_hidden(sK4(X0,X1),X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f57,f58])).

fof(f58,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( k1_funct_1(X1,sK4(X0,X1)) != sK4(X0,X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t43_funct_1.p',t34_funct_1)).

fof(f57070,plain,
    ( k3_xboole_0(sK0,sK1) != k1_relat_1(k6_relat_1(k3_xboole_0(sK0,sK1)))
    | ~ spl6_5
    | ~ spl6_56
    | ~ spl6_60 ),
    inference(forward_demodulation,[],[f57069,f163])).

fof(f163,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ),
    inference(forward_demodulation,[],[f160,f107])).

fof(f160,plain,(
    ! [X0,X1] : k3_xboole_0(k1_relat_1(k6_relat_1(X0)),X1) = k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ),
    inference(unit_resulting_resolution,[],[f67,f70,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t43_funct_1.p',t37_funct_1)).

fof(f57069,plain,
    ( k1_relat_1(k6_relat_1(k3_xboole_0(sK0,sK1))) != k1_relat_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))
    | ~ spl6_5
    | ~ spl6_56
    | ~ spl6_60 ),
    inference(subsumption_resolution,[],[f57068,f67])).

fof(f57068,plain,
    ( k1_relat_1(k6_relat_1(k3_xboole_0(sK0,sK1))) != k1_relat_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))
    | ~ v1_relat_1(k6_relat_1(k3_xboole_0(sK0,sK1)))
    | ~ spl6_5
    | ~ spl6_56
    | ~ spl6_60 ),
    inference(subsumption_resolution,[],[f57067,f70])).

fof(f57067,plain,
    ( k1_relat_1(k6_relat_1(k3_xboole_0(sK0,sK1))) != k1_relat_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))
    | ~ v1_funct_1(k6_relat_1(k3_xboole_0(sK0,sK1)))
    | ~ v1_relat_1(k6_relat_1(k3_xboole_0(sK0,sK1)))
    | ~ spl6_5
    | ~ spl6_56
    | ~ spl6_60 ),
    inference(subsumption_resolution,[],[f57066,f144])).

fof(f144,plain,(
    ! [X0,X1] : v1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(unit_resulting_resolution,[],[f67,f67,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t43_funct_1.p',dt_k5_relat_1)).

fof(f57066,plain,
    ( k1_relat_1(k6_relat_1(k3_xboole_0(sK0,sK1))) != k1_relat_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))
    | ~ v1_funct_1(k6_relat_1(k3_xboole_0(sK0,sK1)))
    | ~ v1_relat_1(k6_relat_1(k3_xboole_0(sK0,sK1)))
    | ~ spl6_5
    | ~ spl6_56
    | ~ spl6_60 ),
    inference(subsumption_resolution,[],[f57065,f159])).

fof(f159,plain,(
    ! [X0,X1] : v1_funct_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(unit_resulting_resolution,[],[f67,f70,f67,f70,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t43_funct_1.p',fc2_funct_1)).

fof(f57065,plain,
    ( k1_relat_1(k6_relat_1(k3_xboole_0(sK0,sK1))) != k1_relat_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))
    | ~ v1_funct_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))
    | ~ v1_funct_1(k6_relat_1(k3_xboole_0(sK0,sK1)))
    | ~ v1_relat_1(k6_relat_1(k3_xboole_0(sK0,sK1)))
    | ~ spl6_5
    | ~ spl6_56
    | ~ spl6_60 ),
    inference(subsumption_resolution,[],[f57064,f130])).

fof(f130,plain,
    ( k6_relat_1(k3_xboole_0(sK0,sK1)) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl6_5
  <=> k6_relat_1(k3_xboole_0(sK0,sK1)) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f57064,plain,
    ( k6_relat_1(k3_xboole_0(sK0,sK1)) = k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))
    | k1_relat_1(k6_relat_1(k3_xboole_0(sK0,sK1))) != k1_relat_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))
    | ~ v1_funct_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))
    | ~ v1_funct_1(k6_relat_1(k3_xboole_0(sK0,sK1)))
    | ~ v1_relat_1(k6_relat_1(k3_xboole_0(sK0,sK1)))
    | ~ spl6_56
    | ~ spl6_60 ),
    inference(subsumption_resolution,[],[f57063,f33599])).

fof(f33599,plain,
    ( k1_funct_1(k6_relat_1(k3_xboole_0(sK0,sK1)),sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))) = sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))
    | ~ spl6_56 ),
    inference(avatar_component_clause,[],[f33598])).

fof(f33598,plain,
    ( spl6_56
  <=> k1_funct_1(k6_relat_1(k3_xboole_0(sK0,sK1)),sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))) = sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).

fof(f57063,plain,
    ( k1_funct_1(k6_relat_1(k3_xboole_0(sK0,sK1)),sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))) != sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))
    | k6_relat_1(k3_xboole_0(sK0,sK1)) = k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))
    | k1_relat_1(k6_relat_1(k3_xboole_0(sK0,sK1))) != k1_relat_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))
    | ~ v1_funct_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))
    | ~ v1_funct_1(k6_relat_1(k3_xboole_0(sK0,sK1)))
    | ~ v1_relat_1(k6_relat_1(k3_xboole_0(sK0,sK1)))
    | ~ spl6_60 ),
    inference(superposition,[],[f73,f57053])).

fof(f57053,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)),sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))) = sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))
    | ~ spl6_60 ),
    inference(avatar_component_clause,[],[f57052])).

fof(f57052,plain,
    ( spl6_60
  <=> k1_funct_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)),sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))) = sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1))
      | X0 = X1
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1))
            & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f51])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t43_funct_1.p',t9_funct_1)).

fof(f57054,plain,
    ( spl6_60
    | ~ spl6_34
    | ~ spl6_36
    | ~ spl6_58 ),
    inference(avatar_split_clause,[],[f57010,f57006,f18726,f18717,f57052])).

fof(f18717,plain,
    ( spl6_34
  <=> r2_hidden(sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f18726,plain,
    ( spl6_36
  <=> r2_hidden(sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f57006,plain,
    ( spl6_58
  <=> k1_funct_1(k6_relat_1(sK0),k1_funct_1(k6_relat_1(sK1),sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))))) = k1_funct_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)),sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).

fof(f57010,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)),sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))) = sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))
    | ~ spl6_34
    | ~ spl6_36
    | ~ spl6_58 ),
    inference(forward_demodulation,[],[f57009,f18738])).

fof(f18738,plain,
    ( k1_funct_1(k6_relat_1(sK0),sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))) = sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))
    | ~ spl6_34 ),
    inference(unit_resulting_resolution,[],[f18718,f105])).

fof(f105,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,X0)
      | k1_funct_1(k6_relat_1(X0),X3) = X3 ) ),
    inference(subsumption_resolution,[],[f104,f67])).

fof(f104,plain,(
    ! [X0,X3] :
      ( k1_funct_1(k6_relat_1(X0),X3) = X3
      | ~ r2_hidden(X3,X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f99,f70])).

fof(f99,plain,(
    ! [X0,X3] :
      ( k1_funct_1(k6_relat_1(X0),X3) = X3
      | ~ r2_hidden(X3,X0)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(X1,X3) = X3
      | ~ r2_hidden(X3,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f18718,plain,
    ( r2_hidden(sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))),sK0)
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f18717])).

fof(f57009,plain,
    ( k1_funct_1(k6_relat_1(sK0),sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))) = k1_funct_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)),sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))))
    | ~ spl6_36
    | ~ spl6_58 ),
    inference(forward_demodulation,[],[f57007,f18759])).

fof(f18759,plain,
    ( k1_funct_1(k6_relat_1(sK1),sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))) = sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))
    | ~ spl6_36 ),
    inference(unit_resulting_resolution,[],[f18727,f105])).

fof(f18727,plain,
    ( r2_hidden(sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))),sK1)
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f18726])).

fof(f57007,plain,
    ( k1_funct_1(k6_relat_1(sK0),k1_funct_1(k6_relat_1(sK1),sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))))) = k1_funct_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)),sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))))
    | ~ spl6_58 ),
    inference(avatar_component_clause,[],[f57006])).

fof(f57008,plain,
    ( spl6_58
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f2831,f1583,f57006])).

fof(f1583,plain,
    ( spl6_6
  <=> r2_hidden(sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f2831,plain,
    ( k1_funct_1(k6_relat_1(sK0),k1_funct_1(k6_relat_1(sK1),sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))))) = k1_funct_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)),sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))))
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f1584,f1128])).

fof(f1128,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_xboole_0(X2,X1))
      | k1_funct_1(k6_relat_1(X2),k1_funct_1(k6_relat_1(X1),X0)) = k1_funct_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X0) ) ),
    inference(forward_demodulation,[],[f1127,f163])).

fof(f1127,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))))
      | k1_funct_1(k6_relat_1(X2),k1_funct_1(k6_relat_1(X1),X0)) = k1_funct_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X0) ) ),
    inference(subsumption_resolution,[],[f1124,f67])).

fof(f1124,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))))
      | ~ v1_relat_1(k6_relat_1(X1))
      | k1_funct_1(k6_relat_1(X2),k1_funct_1(k6_relat_1(X1),X0)) = k1_funct_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X0) ) ),
    inference(resolution,[],[f224,f70])).

fof(f224,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))))
      | ~ v1_relat_1(X1)
      | k1_funct_1(k6_relat_1(X2),k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,k6_relat_1(X2)),X0) ) ),
    inference(subsumption_resolution,[],[f222,f67])).

fof(f222,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k1_funct_1(k6_relat_1(X2),k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,k6_relat_1(X2)),X0)
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(resolution,[],[f87,f70])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0)
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0)
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
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
           => k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t43_funct_1.p',t22_funct_1)).

fof(f1584,plain,
    ( r2_hidden(sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))),k3_xboole_0(sK0,sK1))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f1583])).

fof(f33600,plain,
    ( spl6_56
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f1595,f1583,f33598])).

fof(f1595,plain,
    ( k1_funct_1(k6_relat_1(k3_xboole_0(sK0,sK1)),sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))) = sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f1584,f105])).

fof(f18728,plain,
    ( spl6_36
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f1587,f1583,f18726])).

fof(f1587,plain,
    ( r2_hidden(sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))),sK1)
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f1584,f102])).

fof(f102,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f62,f63])).

fof(f63,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t43_funct_1.p',d4_xboole_0)).

fof(f18719,plain,
    ( spl6_34
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f1586,f1583,f18717])).

fof(f1586,plain,
    ( r2_hidden(sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))),sK0)
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f1584,f103])).

fof(f103,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f1585,plain,
    ( spl6_6
    | spl6_5 ),
    inference(avatar_split_clause,[],[f376,f129,f1583])).

fof(f376,plain,
    ( r2_hidden(sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))),k3_xboole_0(sK0,sK1))
    | ~ spl6_5 ),
    inference(unit_resulting_resolution,[],[f159,f144,f130,f163,f214])).

fof(f214,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | r2_hidden(sK2(k6_relat_1(X0),X1),X0)
      | k1_relat_1(X1) != X0
      | ~ v1_relat_1(X1)
      | k6_relat_1(X0) = X1 ) ),
    inference(forward_demodulation,[],[f213,f107])).

fof(f213,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(k6_relat_1(X0),X1),X0)
      | k1_relat_1(X1) != k1_relat_1(k6_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k6_relat_1(X0) = X1 ) ),
    inference(forward_demodulation,[],[f212,f107])).

fof(f212,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(k6_relat_1(X0),X1),k1_relat_1(k6_relat_1(X0)))
      | k1_relat_1(X1) != k1_relat_1(k6_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k6_relat_1(X0) = X1 ) ),
    inference(subsumption_resolution,[],[f210,f67])).

fof(f210,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(k6_relat_1(X0),X1),k1_relat_1(k6_relat_1(X0)))
      | k1_relat_1(X1) != k1_relat_1(k6_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k6_relat_1(X0) = X1
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(resolution,[],[f72,f70])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(sK2(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | X0 = X1
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f131,plain,(
    ~ spl6_5 ),
    inference(avatar_split_clause,[],[f65,f129])).

fof(f65,plain,(
    k6_relat_1(k3_xboole_0(sK0,sK1)) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    k6_relat_1(k3_xboole_0(sK0,sK1)) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f49])).

fof(f49,plain,
    ( ? [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) != k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))
   => k6_relat_1(k3_xboole_0(sK0,sK1)) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) != k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t43_funct_1.p',t43_funct_1)).
%------------------------------------------------------------------------------
