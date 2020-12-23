%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t44_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:23 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 161 expanded)
%              Number of leaves         :   13 (  50 expanded)
%              Depth                    :   14
%              Number of atoms          :  294 ( 662 expanded)
%              Number of equality atoms :   65 ( 194 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f899,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f78,f82,f86,f116,f145,f165,f237,f796,f892])).

fof(f892,plain,
    ( ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10
    | spl7_25
    | ~ spl7_36
    | ~ spl7_94 ),
    inference(avatar_contradiction_clause,[],[f891])).

fof(f891,plain,
    ( $false
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_25
    | ~ spl7_36
    | ~ spl7_94 ),
    inference(subsumption_resolution,[],[f890,f164])).

fof(f164,plain,
    ( k1_funct_1(sK1,sK2(k2_relat_1(sK0),sK1)) != sK2(k2_relat_1(sK0),sK1)
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl7_25
  <=> k1_funct_1(sK1,sK2(k2_relat_1(sK0),sK1)) != sK2(k2_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f890,plain,
    ( k1_funct_1(sK1,sK2(k2_relat_1(sK0),sK1)) = sK2(k2_relat_1(sK0),sK1)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_36
    | ~ spl7_94 ),
    inference(forward_demodulation,[],[f889,f248])).

fof(f248,plain,
    ( k1_funct_1(sK0,sK5(sK0,sK2(k2_relat_1(sK0),sK1))) = sK2(k2_relat_1(sK0),sK1)
    | ~ spl7_36 ),
    inference(resolution,[],[f236,f54])).

fof(f54,plain,(
    ! [X2,X0] :
      ( ~ sP4(X2,X0)
      | k1_funct_1(X0,sK5(X0,X2)) = X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t44_funct_1.p',d5_funct_1)).

fof(f236,plain,
    ( sP4(sK2(k2_relat_1(sK0),sK1),sK0)
    | ~ spl7_36 ),
    inference(avatar_component_clause,[],[f235])).

fof(f235,plain,
    ( spl7_36
  <=> sP4(sK2(k2_relat_1(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f889,plain,
    ( k1_funct_1(sK1,sK2(k2_relat_1(sK0),sK1)) = k1_funct_1(sK0,sK5(sK0,sK2(k2_relat_1(sK0),sK1)))
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_36
    | ~ spl7_94 ),
    inference(forward_demodulation,[],[f888,f115])).

fof(f115,plain,
    ( k5_relat_1(sK0,sK1) = sK0
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl7_10
  <=> k5_relat_1(sK0,sK1) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f888,plain,
    ( k1_funct_1(sK1,sK2(k2_relat_1(sK0),sK1)) = k1_funct_1(k5_relat_1(sK0,sK1),sK5(sK0,sK2(k2_relat_1(sK0),sK1)))
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_36
    | ~ spl7_94 ),
    inference(forward_demodulation,[],[f887,f248])).

fof(f887,plain,
    ( k1_funct_1(k5_relat_1(sK0,sK1),sK5(sK0,sK2(k2_relat_1(sK0),sK1))) = k1_funct_1(sK1,k1_funct_1(sK0,sK5(sK0,sK2(k2_relat_1(sK0),sK1))))
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_94 ),
    inference(subsumption_resolution,[],[f886,f85])).

fof(f85,plain,
    ( v1_funct_1(sK0)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl7_6
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f886,plain,
    ( ~ v1_funct_1(sK0)
    | k1_funct_1(k5_relat_1(sK0,sK1),sK5(sK0,sK2(k2_relat_1(sK0),sK1))) = k1_funct_1(sK1,k1_funct_1(sK0,sK5(sK0,sK2(k2_relat_1(sK0),sK1))))
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_94 ),
    inference(subsumption_resolution,[],[f877,f81])).

fof(f81,plain,
    ( v1_relat_1(sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl7_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f877,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | k1_funct_1(k5_relat_1(sK0,sK1),sK5(sK0,sK2(k2_relat_1(sK0),sK1))) = k1_funct_1(sK1,k1_funct_1(sK0,sK5(sK0,sK2(k2_relat_1(sK0),sK1))))
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_94 ),
    inference(resolution,[],[f795,f93])).

fof(f93,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X2,k1_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | k1_funct_1(k5_relat_1(X1,sK1),X2) = k1_funct_1(sK1,k1_funct_1(X1,X2)) )
    | ~ spl7_0
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f89,f73])).

fof(f73,plain,
    ( v1_relat_1(sK1)
    | ~ spl7_0 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl7_0
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_0])])).

fof(f89,plain,
    ( ! [X2,X1] :
        ( ~ v1_funct_1(X1)
        | ~ v1_relat_1(sK1)
        | ~ v1_relat_1(X1)
        | ~ r2_hidden(X2,k1_relat_1(X1))
        | k1_funct_1(k5_relat_1(X1,sK1),X2) = k1_funct_1(sK1,k1_funct_1(X1,X2)) )
    | ~ spl7_2 ),
    inference(resolution,[],[f77,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t44_funct_1.p',t23_funct_1)).

fof(f77,plain,
    ( v1_funct_1(sK1)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl7_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f795,plain,
    ( r2_hidden(sK5(sK0,sK2(k2_relat_1(sK0),sK1)),k1_relat_1(sK0))
    | ~ spl7_94 ),
    inference(avatar_component_clause,[],[f794])).

fof(f794,plain,
    ( spl7_94
  <=> r2_hidden(sK5(sK0,sK2(k2_relat_1(sK0),sK1)),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_94])])).

fof(f796,plain,
    ( spl7_94
    | ~ spl7_36 ),
    inference(avatar_split_clause,[],[f247,f235,f794])).

fof(f247,plain,
    ( r2_hidden(sK5(sK0,sK2(k2_relat_1(sK0),sK1)),k1_relat_1(sK0))
    | ~ spl7_36 ),
    inference(resolution,[],[f236,f53])).

fof(f53,plain,(
    ! [X2,X0] :
      ( ~ sP4(X2,X0)
      | r2_hidden(sK5(X0,X2),k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f237,plain,
    ( spl7_36
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f155,f143,f84,f80,f235])).

fof(f143,plain,
    ( spl7_20
  <=> r2_hidden(sK2(k2_relat_1(sK0),sK1),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f155,plain,
    ( sP4(sK2(k2_relat_1(sK0),sK1),sK0)
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f154,f81])).

fof(f154,plain,
    ( sP4(sK2(k2_relat_1(sK0),sK1),sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl7_6
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f149,f85])).

fof(f149,plain,
    ( ~ v1_funct_1(sK0)
    | sP4(sK2(k2_relat_1(sK0),sK1),sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl7_20 ),
    inference(resolution,[],[f144,f68])).

fof(f68,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | sP4(X2,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | sP4(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f144,plain,
    ( r2_hidden(sK2(k2_relat_1(sK0),sK1),k2_relat_1(sK0))
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f143])).

fof(f165,plain,
    ( ~ spl7_25
    | ~ spl7_0
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f99,f76,f72,f163])).

fof(f99,plain,
    ( k1_funct_1(sK1,sK2(k2_relat_1(sK0),sK1)) != sK2(k2_relat_1(sK0),sK1)
    | ~ spl7_0
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f98,f39])).

fof(f39,plain,(
    k2_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k6_relat_1(k1_relat_1(X1)) != X1
          & k5_relat_1(X0,X1) = X0
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k6_relat_1(k1_relat_1(X1)) != X1
          & k5_relat_1(X0,X1) = X0
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k5_relat_1(X0,X1) = X0
                & k2_relat_1(X0) = k1_relat_1(X1) )
             => k6_relat_1(k1_relat_1(X1)) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = X0
              & k2_relat_1(X0) = k1_relat_1(X1) )
           => k6_relat_1(k1_relat_1(X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t44_funct_1.p',t44_funct_1)).

fof(f98,plain,
    ( k1_funct_1(sK1,sK2(k1_relat_1(sK1),sK1)) != sK2(k1_relat_1(sK1),sK1)
    | ~ spl7_0
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f97,f41])).

fof(f41,plain,(
    k6_relat_1(k1_relat_1(sK1)) != sK1 ),
    inference(cnf_transformation,[],[f22])).

fof(f97,plain,
    ( k1_funct_1(sK1,sK2(k1_relat_1(sK1),sK1)) != sK2(k1_relat_1(sK1),sK1)
    | k6_relat_1(k1_relat_1(sK1)) = sK1
    | ~ spl7_0
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f91,f73])).

fof(f91,plain,
    ( ~ v1_relat_1(sK1)
    | k1_funct_1(sK1,sK2(k1_relat_1(sK1),sK1)) != sK2(k1_relat_1(sK1),sK1)
    | k6_relat_1(k1_relat_1(sK1)) = sK1
    | ~ spl7_2 ),
    inference(resolution,[],[f77,f66])).

fof(f66,plain,(
    ! [X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k1_funct_1(X1,sK2(k1_relat_1(X1),X1)) != sK2(k1_relat_1(X1),X1)
      | k6_relat_1(k1_relat_1(X1)) = X1 ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != X0
      | k1_funct_1(X1,sK2(X0,X1)) != sK2(X0,X1)
      | k6_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t44_funct_1.p',t34_funct_1)).

fof(f145,plain,
    ( spl7_20
    | ~ spl7_0
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f96,f76,f72,f143])).

fof(f96,plain,
    ( r2_hidden(sK2(k2_relat_1(sK0),sK1),k2_relat_1(sK0))
    | ~ spl7_0
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f95,f39])).

fof(f95,plain,
    ( r2_hidden(sK2(k1_relat_1(sK1),sK1),k1_relat_1(sK1))
    | ~ spl7_0
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f94,f41])).

fof(f94,plain,
    ( r2_hidden(sK2(k1_relat_1(sK1),sK1),k1_relat_1(sK1))
    | k6_relat_1(k1_relat_1(sK1)) = sK1
    | ~ spl7_0
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f90,f73])).

fof(f90,plain,
    ( ~ v1_relat_1(sK1)
    | r2_hidden(sK2(k1_relat_1(sK1),sK1),k1_relat_1(sK1))
    | k6_relat_1(k1_relat_1(sK1)) = sK1
    | ~ spl7_2 ),
    inference(resolution,[],[f77,f67])).

fof(f67,plain,(
    ! [X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r2_hidden(sK2(k1_relat_1(X1),X1),k1_relat_1(X1))
      | k6_relat_1(k1_relat_1(X1)) = X1 ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != X0
      | r2_hidden(sK2(X0,X1),X0)
      | k6_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f116,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f40,f114])).

fof(f40,plain,(
    k5_relat_1(sK0,sK1) = sK0 ),
    inference(cnf_transformation,[],[f22])).

fof(f86,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f43,f84])).

fof(f43,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f82,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f42,f80])).

fof(f42,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f78,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f38,f76])).

fof(f38,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f74,plain,(
    spl7_0 ),
    inference(avatar_split_clause,[],[f37,f72])).

fof(f37,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
