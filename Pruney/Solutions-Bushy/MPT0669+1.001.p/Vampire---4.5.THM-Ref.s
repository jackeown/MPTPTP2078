%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0669+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:25 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 148 expanded)
%              Number of leaves         :   10 (  45 expanded)
%              Depth                    :   13
%              Number of atoms          :  257 ( 598 expanded)
%              Number of equality atoms :   10 (  42 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f103,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f43,f55,f60,f79,f84,f97,f102])).

fof(f102,plain,
    ( spl7_6
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f101,f58,f53,f77])).

fof(f77,plain,
    ( spl7_6
  <=> sP6(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f53,plain,
    ( spl7_4
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f58,plain,
    ( spl7_5
  <=> r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f101,plain,
    ( sP6(sK0,sK2,sK1)
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f100,f54])).

fof(f54,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f100,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | sP6(sK0,sK2,sK1)
    | ~ spl7_5 ),
    inference(resolution,[],[f59,f19])).

fof(f19,plain,(
    ! [X4,X2,X0] :
      ( ~ r2_hidden(k1_funct_1(X2,X4),X0)
      | ~ r2_hidden(X4,k1_relat_1(X2))
      | sP6(X4,X2,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( k1_funct_1(X2,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) ) ) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( k1_funct_1(X2,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) ) ) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X2,X3) = k1_funct_1(X1,X3) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) ) ) ) ) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X2,X3) = k1_funct_1(X1,X3) )
              & ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X3),X0)
                    & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_funct_1)).

fof(f59,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f58])).

fof(f97,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(avatar_contradiction_clause,[],[f96])).

fof(f96,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f95,f91])).

fof(f91,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f85,f59])).

fof(f85,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | ~ r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f14,f80])).

fof(f80,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl7_6 ),
    inference(resolution,[],[f78,f20])).

fof(f20,plain,(
    ! [X4,X2,X0] :
      ( ~ sP6(X4,X2,X0)
      | r2_hidden(X4,k1_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f78,plain,
    ( sP6(sK0,sK2,sK1)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f77])).

fof(f14,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | ~ r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <~> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <~> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
        <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_funct_1)).

fof(f95,plain,
    ( r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f94,f44])).

fof(f44,plain,
    ( ! [X0] : v1_relat_1(k8_relat_1(X0,sK2))
    | ~ spl7_1 ),
    inference(resolution,[],[f38,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | v1_relat_1(k8_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f38,plain,
    ( v1_relat_1(sK2)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl7_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f94,plain,
    ( ~ v1_relat_1(k8_relat_1(sK1,sK2))
    | r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f93,f42])).

fof(f42,plain,
    ( v1_funct_1(sK2)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl7_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f93,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(k8_relat_1(sK1,sK2))
    | r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f92,f38])).

fof(f92,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(k8_relat_1(sK1,sK2))
    | r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f82,f47])).

fof(f47,plain,
    ( ! [X1] : v1_funct_1(k8_relat_1(X1,sK2))
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f46,f38])).

fof(f46,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(sK2)
        | v1_funct_1(k8_relat_1(X1,sK2)) )
    | ~ spl7_2 ),
    inference(resolution,[],[f42,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | v1_funct_1(k8_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_funct_1)).

fof(f82,plain,
    ( ~ v1_funct_1(k8_relat_1(sK1,sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(k8_relat_1(sK1,sK2))
    | r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))
    | ~ spl7_6 ),
    inference(resolution,[],[f78,f35])).

fof(f35,plain,(
    ! [X4,X2,X0] :
      ( ~ sP6(X4,X2,X0)
      | ~ v1_funct_1(k8_relat_1(X0,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(k8_relat_1(X0,X2))
      | r2_hidden(X4,k1_relat_1(k8_relat_1(X0,X2))) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ sP6(X4,X2,X0)
      | r2_hidden(X4,k1_relat_1(X1))
      | k8_relat_1(X0,X2) != X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f84,plain,
    ( spl7_5
    | ~ spl7_6 ),
    inference(avatar_contradiction_clause,[],[f83])).

fof(f83,plain,
    ( $false
    | spl7_5
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f81,f69])).

fof(f69,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | spl7_5 ),
    inference(avatar_component_clause,[],[f58])).

fof(f81,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | ~ spl7_6 ),
    inference(resolution,[],[f78,f21])).

fof(f21,plain,(
    ! [X4,X2,X0] :
      ( ~ sP6(X4,X2,X0)
      | r2_hidden(k1_funct_1(X2,X4),X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f79,plain,
    ( spl7_6
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f75,f50,f41,f37,f77])).

fof(f50,plain,
    ( spl7_3
  <=> r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f75,plain,
    ( sP6(sK0,sK2,sK1)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f74,f44])).

fof(f74,plain,
    ( sP6(sK0,sK2,sK1)
    | ~ v1_relat_1(k8_relat_1(sK1,sK2))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f73,f42])).

fof(f73,plain,
    ( ~ v1_funct_1(sK2)
    | sP6(sK0,sK2,sK1)
    | ~ v1_relat_1(k8_relat_1(sK1,sK2))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f72,f38])).

fof(f72,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | sP6(sK0,sK2,sK1)
    | ~ v1_relat_1(k8_relat_1(sK1,sK2))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f71,f47])).

fof(f71,plain,
    ( ~ v1_funct_1(k8_relat_1(sK1,sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | sP6(sK0,sK2,sK1)
    | ~ v1_relat_1(k8_relat_1(sK1,sK2))
    | ~ spl7_3 ),
    inference(resolution,[],[f51,f34])).

fof(f34,plain,(
    ! [X4,X2,X0] :
      ( ~ r2_hidden(X4,k1_relat_1(k8_relat_1(X0,X2)))
      | ~ v1_funct_1(k8_relat_1(X0,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | sP6(X4,X2,X0)
      | ~ v1_relat_1(k8_relat_1(X0,X2)) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | sP6(X4,X2,X0)
      | ~ r2_hidden(X4,k1_relat_1(X1))
      | k8_relat_1(X0,X2) != X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f51,plain,
    ( r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f60,plain,
    ( spl7_3
    | spl7_5 ),
    inference(avatar_split_clause,[],[f16,f58,f50])).

fof(f16,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f8])).

fof(f55,plain,
    ( spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f15,f53,f50])).

fof(f15,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f8])).

fof(f43,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f18,f41])).

fof(f18,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f39,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f17,f37])).

fof(f17,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f8])).

%------------------------------------------------------------------------------
