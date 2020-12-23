%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_6__t9_yellow_6.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:56 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 293 expanded)
%              Number of leaves         :   21 ( 120 expanded)
%              Depth                    :   17
%              Number of atoms          :  748 (1345 expanded)
%              Number of equality atoms :   58 (  95 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f323,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f73,f77,f81,f85,f89,f93,f136,f140,f151,f155,f159,f163,f251,f321,f322])).

fof(f322,plain,
    ( k1_funct_1(sK1,sK2) != k10_pralg_1(sK0,sK1,sK2)
    | k1_funct_1(k12_pralg_1(sK0,sK1),sK2) != u1_struct_0(k1_funct_1(sK1,sK2))
    | k1_funct_1(k12_pralg_1(sK0,sK1),sK2) = u1_struct_0(k10_pralg_1(sK0,sK1,sK2)) ),
    introduced(theory_axiom,[])).

fof(f321,plain,
    ( spl7_60
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_20
    | ~ spl7_22
    | ~ spl7_24
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f292,f161,f157,f153,f149,f134,f91,f87,f75,f71,f67,f319])).

fof(f319,plain,
    ( spl7_60
  <=> k1_funct_1(k12_pralg_1(sK0,sK1),sK2) = u1_struct_0(k1_funct_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).

fof(f67,plain,
    ( spl7_0
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_0])])).

fof(f71,plain,
    ( spl7_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f75,plain,
    ( spl7_4
  <=> v2_pralg_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f87,plain,
    ( spl7_10
  <=> v4_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f91,plain,
    ( spl7_12
  <=> v1_partfun1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f134,plain,
    ( spl7_14
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f149,plain,
    ( spl7_20
  <=> v1_relat_1(k12_pralg_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f153,plain,
    ( spl7_22
  <=> v1_funct_1(k12_pralg_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f157,plain,
    ( spl7_24
  <=> v4_relat_1(k12_pralg_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f161,plain,
    ( spl7_26
  <=> v1_partfun1(k12_pralg_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f292,plain,
    ( k1_funct_1(k12_pralg_1(sK0,sK1),sK2) = u1_struct_0(k1_funct_1(sK1,sK2))
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_20
    | ~ spl7_22
    | ~ spl7_24
    | ~ spl7_26 ),
    inference(forward_demodulation,[],[f290,f284])).

fof(f284,plain,
    ( k1_funct_1(sK1,sK2) = sK4(sK1,k12_pralg_1(sK0,sK1),sK2)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_20
    | ~ spl7_22
    | ~ spl7_24
    | ~ spl7_26 ),
    inference(resolution,[],[f189,f135])).

fof(f135,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f134])).

fof(f189,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK0)
        | k1_funct_1(sK1,X1) = sK4(sK1,k12_pralg_1(sK0,sK1),X1) )
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_22
    | ~ spl7_24
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f188,f68])).

fof(f68,plain,
    ( v1_relat_1(sK1)
    | ~ spl7_0 ),
    inference(avatar_component_clause,[],[f67])).

fof(f188,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(sK1)
        | ~ r2_hidden(X1,sK0)
        | k1_funct_1(sK1,X1) = sK4(sK1,k12_pralg_1(sK0,sK1),X1) )
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_22
    | ~ spl7_24
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f187,f154])).

fof(f154,plain,
    ( v1_funct_1(k12_pralg_1(sK0,sK1))
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f153])).

fof(f187,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(k12_pralg_1(sK0,sK1))
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(X1,sK0)
        | k1_funct_1(sK1,X1) = sK4(sK1,k12_pralg_1(sK0,sK1),X1) )
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_24
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f186,f158])).

fof(f158,plain,
    ( v4_relat_1(k12_pralg_1(sK0,sK1),sK0)
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f157])).

fof(f186,plain,
    ( ! [X1] :
        ( ~ v4_relat_1(k12_pralg_1(sK0,sK1),sK0)
        | ~ v1_funct_1(k12_pralg_1(sK0,sK1))
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(X1,sK0)
        | k1_funct_1(sK1,X1) = sK4(sK1,k12_pralg_1(sK0,sK1),X1) )
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f185,f150])).

fof(f150,plain,
    ( v1_relat_1(k12_pralg_1(sK0,sK1))
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f149])).

fof(f185,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(k12_pralg_1(sK0,sK1))
        | ~ v4_relat_1(k12_pralg_1(sK0,sK1),sK0)
        | ~ v1_funct_1(k12_pralg_1(sK0,sK1))
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(X1,sK0)
        | k1_funct_1(sK1,X1) = sK4(sK1,k12_pralg_1(sK0,sK1),X1) )
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f184,f76])).

fof(f76,plain,
    ( v2_pralg_1(sK1)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f75])).

fof(f184,plain,
    ( ! [X1] :
        ( ~ v2_pralg_1(sK1)
        | ~ v1_relat_1(k12_pralg_1(sK0,sK1))
        | ~ v4_relat_1(k12_pralg_1(sK0,sK1),sK0)
        | ~ v1_funct_1(k12_pralg_1(sK0,sK1))
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(X1,sK0)
        | k1_funct_1(sK1,X1) = sK4(sK1,k12_pralg_1(sK0,sK1),X1) )
    | ~ spl7_2
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f183,f92])).

fof(f92,plain,
    ( v1_partfun1(sK1,sK0)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f91])).

fof(f183,plain,
    ( ! [X1] :
        ( ~ v1_partfun1(sK1,sK0)
        | ~ v2_pralg_1(sK1)
        | ~ v1_relat_1(k12_pralg_1(sK0,sK1))
        | ~ v4_relat_1(k12_pralg_1(sK0,sK1),sK0)
        | ~ v1_funct_1(k12_pralg_1(sK0,sK1))
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(X1,sK0)
        | k1_funct_1(sK1,X1) = sK4(sK1,k12_pralg_1(sK0,sK1),X1) )
    | ~ spl7_2
    | ~ spl7_10
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f182,f72])).

fof(f72,plain,
    ( v1_funct_1(sK1)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f182,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(sK1)
        | ~ v1_partfun1(sK1,sK0)
        | ~ v2_pralg_1(sK1)
        | ~ v1_relat_1(k12_pralg_1(sK0,sK1))
        | ~ v4_relat_1(k12_pralg_1(sK0,sK1),sK0)
        | ~ v1_funct_1(k12_pralg_1(sK0,sK1))
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(X1,sK0)
        | k1_funct_1(sK1,X1) = sK4(sK1,k12_pralg_1(sK0,sK1),X1) )
    | ~ spl7_10
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f165,f88])).

fof(f88,plain,
    ( v4_relat_1(sK1,sK0)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f87])).

fof(f165,plain,
    ( ! [X1] :
        ( ~ v4_relat_1(sK1,sK0)
        | ~ v1_funct_1(sK1)
        | ~ v1_partfun1(sK1,sK0)
        | ~ v2_pralg_1(sK1)
        | ~ v1_relat_1(k12_pralg_1(sK0,sK1))
        | ~ v4_relat_1(k12_pralg_1(sK0,sK1),sK0)
        | ~ v1_funct_1(k12_pralg_1(sK0,sK1))
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(X1,sK0)
        | k1_funct_1(sK1,X1) = sK4(sK1,k12_pralg_1(sK0,sK1),X1) )
    | ~ spl7_26 ),
    inference(resolution,[],[f162,f63])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_partfun1(k12_pralg_1(X0,X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v2_pralg_1(X1)
      | ~ v1_relat_1(k12_pralg_1(X0,X1))
      | ~ v4_relat_1(k12_pralg_1(X0,X1),X0)
      | ~ v1_funct_1(k12_pralg_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X3,X0)
      | k1_funct_1(X1,X3) = sK4(X1,k12_pralg_1(X0,X1),X3) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v2_pralg_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ v1_partfun1(X2,X0)
      | ~ r2_hidden(X3,X0)
      | k1_funct_1(X1,X3) = sK4(X1,X2,X3)
      | k12_pralg_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k12_pralg_1(X0,X1) = X2
          <=> ! [X3] :
                ( ? [X4] :
                    ( k1_funct_1(X2,X3) = u1_struct_0(X4)
                    & k1_funct_1(X1,X3) = X4
                    & l1_struct_0(X4) )
                | ~ r2_hidden(X3,X0) ) )
          | ~ v1_partfun1(X2,X0)
          | ~ v1_funct_1(X2)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k12_pralg_1(X0,X1) = X2
          <=> ! [X3] :
                ( ? [X4] :
                    ( k1_funct_1(X2,X3) = u1_struct_0(X4)
                    & k1_funct_1(X1,X3) = X4
                    & l1_struct_0(X4) )
                | ~ r2_hidden(X3,X0) ) )
          | ~ v1_partfun1(X2,X0)
          | ~ v1_funct_1(X2)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v2_pralg_1(X1)
        & v1_partfun1(X1,X0)
        & v1_funct_1(X1)
        & v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2)
            & v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => ( k12_pralg_1(X0,X1) = X2
          <=> ! [X3] :
                ~ ( ! [X4] :
                      ( l1_struct_0(X4)
                     => ~ ( k1_funct_1(X2,X3) = u1_struct_0(X4)
                          & k1_funct_1(X1,X3) = X4 ) )
                  & r2_hidden(X3,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t9_yellow_6.p',d13_pralg_1)).

fof(f162,plain,
    ( v1_partfun1(k12_pralg_1(sK0,sK1),sK0)
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f161])).

fof(f290,plain,
    ( k1_funct_1(k12_pralg_1(sK0,sK1),sK2) = u1_struct_0(sK4(sK1,k12_pralg_1(sK0,sK1),sK2))
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_20
    | ~ spl7_22
    | ~ spl7_24
    | ~ spl7_26 ),
    inference(resolution,[],[f197,f135])).

fof(f197,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK0)
        | k1_funct_1(k12_pralg_1(sK0,sK1),X2) = u1_struct_0(sK4(sK1,k12_pralg_1(sK0,sK1),X2)) )
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_22
    | ~ spl7_24
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f196,f68])).

fof(f196,plain,
    ( ! [X2] :
        ( ~ v1_relat_1(sK1)
        | ~ r2_hidden(X2,sK0)
        | k1_funct_1(k12_pralg_1(sK0,sK1),X2) = u1_struct_0(sK4(sK1,k12_pralg_1(sK0,sK1),X2)) )
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_22
    | ~ spl7_24
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f195,f154])).

fof(f195,plain,
    ( ! [X2] :
        ( ~ v1_funct_1(k12_pralg_1(sK0,sK1))
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(X2,sK0)
        | k1_funct_1(k12_pralg_1(sK0,sK1),X2) = u1_struct_0(sK4(sK1,k12_pralg_1(sK0,sK1),X2)) )
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_24
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f194,f158])).

fof(f194,plain,
    ( ! [X2] :
        ( ~ v4_relat_1(k12_pralg_1(sK0,sK1),sK0)
        | ~ v1_funct_1(k12_pralg_1(sK0,sK1))
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(X2,sK0)
        | k1_funct_1(k12_pralg_1(sK0,sK1),X2) = u1_struct_0(sK4(sK1,k12_pralg_1(sK0,sK1),X2)) )
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f193,f150])).

fof(f193,plain,
    ( ! [X2] :
        ( ~ v1_relat_1(k12_pralg_1(sK0,sK1))
        | ~ v4_relat_1(k12_pralg_1(sK0,sK1),sK0)
        | ~ v1_funct_1(k12_pralg_1(sK0,sK1))
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(X2,sK0)
        | k1_funct_1(k12_pralg_1(sK0,sK1),X2) = u1_struct_0(sK4(sK1,k12_pralg_1(sK0,sK1),X2)) )
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f192,f76])).

fof(f192,plain,
    ( ! [X2] :
        ( ~ v2_pralg_1(sK1)
        | ~ v1_relat_1(k12_pralg_1(sK0,sK1))
        | ~ v4_relat_1(k12_pralg_1(sK0,sK1),sK0)
        | ~ v1_funct_1(k12_pralg_1(sK0,sK1))
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(X2,sK0)
        | k1_funct_1(k12_pralg_1(sK0,sK1),X2) = u1_struct_0(sK4(sK1,k12_pralg_1(sK0,sK1),X2)) )
    | ~ spl7_2
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f191,f92])).

fof(f191,plain,
    ( ! [X2] :
        ( ~ v1_partfun1(sK1,sK0)
        | ~ v2_pralg_1(sK1)
        | ~ v1_relat_1(k12_pralg_1(sK0,sK1))
        | ~ v4_relat_1(k12_pralg_1(sK0,sK1),sK0)
        | ~ v1_funct_1(k12_pralg_1(sK0,sK1))
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(X2,sK0)
        | k1_funct_1(k12_pralg_1(sK0,sK1),X2) = u1_struct_0(sK4(sK1,k12_pralg_1(sK0,sK1),X2)) )
    | ~ spl7_2
    | ~ spl7_10
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f190,f72])).

fof(f190,plain,
    ( ! [X2] :
        ( ~ v1_funct_1(sK1)
        | ~ v1_partfun1(sK1,sK0)
        | ~ v2_pralg_1(sK1)
        | ~ v1_relat_1(k12_pralg_1(sK0,sK1))
        | ~ v4_relat_1(k12_pralg_1(sK0,sK1),sK0)
        | ~ v1_funct_1(k12_pralg_1(sK0,sK1))
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(X2,sK0)
        | k1_funct_1(k12_pralg_1(sK0,sK1),X2) = u1_struct_0(sK4(sK1,k12_pralg_1(sK0,sK1),X2)) )
    | ~ spl7_10
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f166,f88])).

fof(f166,plain,
    ( ! [X2] :
        ( ~ v4_relat_1(sK1,sK0)
        | ~ v1_funct_1(sK1)
        | ~ v1_partfun1(sK1,sK0)
        | ~ v2_pralg_1(sK1)
        | ~ v1_relat_1(k12_pralg_1(sK0,sK1))
        | ~ v4_relat_1(k12_pralg_1(sK0,sK1),sK0)
        | ~ v1_funct_1(k12_pralg_1(sK0,sK1))
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(X2,sK0)
        | k1_funct_1(k12_pralg_1(sK0,sK1),X2) = u1_struct_0(sK4(sK1,k12_pralg_1(sK0,sK1),X2)) )
    | ~ spl7_26 ),
    inference(resolution,[],[f162,f62])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_partfun1(k12_pralg_1(X0,X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v2_pralg_1(X1)
      | ~ v1_relat_1(k12_pralg_1(X0,X1))
      | ~ v4_relat_1(k12_pralg_1(X0,X1),X0)
      | ~ v1_funct_1(k12_pralg_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X3,X0)
      | k1_funct_1(k12_pralg_1(X0,X1),X3) = u1_struct_0(sK4(X1,k12_pralg_1(X0,X1),X3)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v2_pralg_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ v1_partfun1(X2,X0)
      | ~ r2_hidden(X3,X0)
      | k1_funct_1(X2,X3) = u1_struct_0(sK4(X1,X2,X3))
      | k12_pralg_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f251,plain,
    ( spl7_36
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | spl7_7
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f224,f91,f87,f83,f79,f75,f71,f67,f249])).

fof(f249,plain,
    ( spl7_36
  <=> k1_funct_1(sK1,sK2) = k10_pralg_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f79,plain,
    ( spl7_7
  <=> ~ v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f83,plain,
    ( spl7_8
  <=> m1_subset_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f224,plain,
    ( k1_funct_1(sK1,sK2) = k10_pralg_1(sK0,sK1,sK2)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(resolution,[],[f107,f84])).

fof(f84,plain,
    ( m1_subset_1(sK2,sK0)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f83])).

fof(f107,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | k1_funct_1(sK1,X0) = k10_pralg_1(sK0,sK1,X0) )
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_7
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f106,f76])).

fof(f106,plain,
    ( ! [X0] :
        ( ~ v2_pralg_1(sK1)
        | ~ m1_subset_1(X0,sK0)
        | k1_funct_1(sK1,X0) = k10_pralg_1(sK0,sK1,X0) )
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_7
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f105,f80])).

fof(f80,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f79])).

fof(f105,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK0)
        | ~ v2_pralg_1(sK1)
        | ~ m1_subset_1(X0,sK0)
        | k1_funct_1(sK1,X0) = k10_pralg_1(sK0,sK1,X0) )
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f104,f72])).

fof(f104,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK1)
        | v1_xboole_0(sK0)
        | ~ v2_pralg_1(sK1)
        | ~ m1_subset_1(X0,sK0)
        | k1_funct_1(sK1,X0) = k10_pralg_1(sK0,sK1,X0) )
    | ~ spl7_0
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f103,f88])).

fof(f103,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK1,sK0)
        | ~ v1_funct_1(sK1)
        | v1_xboole_0(sK0)
        | ~ v2_pralg_1(sK1)
        | ~ m1_subset_1(X0,sK0)
        | k1_funct_1(sK1,X0) = k10_pralg_1(sK0,sK1,X0) )
    | ~ spl7_0
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f96,f68])).

fof(f96,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK1)
        | ~ v4_relat_1(sK1,sK0)
        | ~ v1_funct_1(sK1)
        | v1_xboole_0(sK0)
        | ~ v2_pralg_1(sK1)
        | ~ m1_subset_1(X0,sK0)
        | k1_funct_1(sK1,X0) = k10_pralg_1(sK0,sK1,X0) )
    | ~ spl7_12 ),
    inference(resolution,[],[f92,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_funct_1(X1)
      | v1_xboole_0(X0)
      | ~ v2_pralg_1(X1)
      | ~ m1_subset_1(X2,X0)
      | k1_funct_1(X1,X2) = k10_pralg_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X1,X2) = k10_pralg_1(X0,X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X1,X2) = k10_pralg_1(X0,X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & v2_pralg_1(X1)
        & v1_partfun1(X1,X0)
        & v1_funct_1(X1)
        & v4_relat_1(X1,X0)
        & v1_relat_1(X1)
        & ~ v1_xboole_0(X0) )
     => k1_funct_1(X1,X2) = k10_pralg_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t9_yellow_6.p',redefinition_k10_pralg_1)).

fof(f163,plain,
    ( spl7_26
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f132,f91,f87,f75,f71,f67,f161])).

fof(f132,plain,
    ( v1_partfun1(k12_pralg_1(sK0,sK1),sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f131,f76])).

fof(f131,plain,
    ( ~ v2_pralg_1(sK1)
    | v1_partfun1(k12_pralg_1(sK0,sK1),sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f130,f68])).

fof(f130,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v2_pralg_1(sK1)
    | v1_partfun1(k12_pralg_1(sK0,sK1),sK0)
    | ~ spl7_2
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f129,f72])).

fof(f129,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v2_pralg_1(sK1)
    | v1_partfun1(k12_pralg_1(sK0,sK1),sK0)
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f102,f88])).

fof(f102,plain,
    ( ~ v4_relat_1(sK1,sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v2_pralg_1(sK1)
    | v1_partfun1(k12_pralg_1(sK0,sK1),sK0)
    | ~ spl7_12 ),
    inference(resolution,[],[f92,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_pralg_1(X1)
      | v1_partfun1(k12_pralg_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(k12_pralg_1(X0,X1),X0)
        & v1_funct_1(k12_pralg_1(X0,X1))
        & v4_relat_1(k12_pralg_1(X0,X1),X0)
        & v1_relat_1(k12_pralg_1(X0,X1)) )
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(k12_pralg_1(X0,X1),X0)
        & v1_funct_1(k12_pralg_1(X0,X1))
        & v4_relat_1(k12_pralg_1(X0,X1),X0)
        & v1_relat_1(k12_pralg_1(X0,X1)) )
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v2_pralg_1(X1)
        & v1_partfun1(X1,X0)
        & v1_funct_1(X1)
        & v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(k12_pralg_1(X0,X1),X0)
        & v1_funct_1(k12_pralg_1(X0,X1))
        & v4_relat_1(k12_pralg_1(X0,X1),X0)
        & v1_relat_1(k12_pralg_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t9_yellow_6.p',dt_k12_pralg_1)).

fof(f159,plain,
    ( spl7_24
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f124,f91,f87,f75,f71,f67,f157])).

fof(f124,plain,
    ( v4_relat_1(k12_pralg_1(sK0,sK1),sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f123,f76])).

fof(f123,plain,
    ( ~ v2_pralg_1(sK1)
    | v4_relat_1(k12_pralg_1(sK0,sK1),sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f122,f68])).

fof(f122,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v2_pralg_1(sK1)
    | v4_relat_1(k12_pralg_1(sK0,sK1),sK0)
    | ~ spl7_2
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f121,f72])).

fof(f121,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v2_pralg_1(sK1)
    | v4_relat_1(k12_pralg_1(sK0,sK1),sK0)
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f100,f88])).

fof(f100,plain,
    ( ~ v4_relat_1(sK1,sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v2_pralg_1(sK1)
    | v4_relat_1(k12_pralg_1(sK0,sK1),sK0)
    | ~ spl7_12 ),
    inference(resolution,[],[f92,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_pralg_1(X1)
      | v4_relat_1(k12_pralg_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f155,plain,
    ( spl7_22
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f128,f91,f87,f75,f71,f67,f153])).

fof(f128,plain,
    ( v1_funct_1(k12_pralg_1(sK0,sK1))
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f127,f76])).

fof(f127,plain,
    ( ~ v2_pralg_1(sK1)
    | v1_funct_1(k12_pralg_1(sK0,sK1))
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f126,f68])).

fof(f126,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v2_pralg_1(sK1)
    | v1_funct_1(k12_pralg_1(sK0,sK1))
    | ~ spl7_2
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f125,f72])).

fof(f125,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v2_pralg_1(sK1)
    | v1_funct_1(k12_pralg_1(sK0,sK1))
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f101,f88])).

fof(f101,plain,
    ( ~ v4_relat_1(sK1,sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v2_pralg_1(sK1)
    | v1_funct_1(k12_pralg_1(sK0,sK1))
    | ~ spl7_12 ),
    inference(resolution,[],[f92,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_pralg_1(X1)
      | v1_funct_1(k12_pralg_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f151,plain,
    ( spl7_20
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f120,f91,f87,f75,f71,f67,f149])).

fof(f120,plain,
    ( v1_relat_1(k12_pralg_1(sK0,sK1))
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f119,f76])).

fof(f119,plain,
    ( ~ v2_pralg_1(sK1)
    | v1_relat_1(k12_pralg_1(sK0,sK1))
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f118,f68])).

fof(f118,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v2_pralg_1(sK1)
    | v1_relat_1(k12_pralg_1(sK0,sK1))
    | ~ spl7_2
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f117,f72])).

fof(f117,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v2_pralg_1(sK1)
    | v1_relat_1(k12_pralg_1(sK0,sK1))
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f99,f88])).

fof(f99,plain,
    ( ~ v4_relat_1(sK1,sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v2_pralg_1(sK1)
    | v1_relat_1(k12_pralg_1(sK0,sK1))
    | ~ spl7_12 ),
    inference(resolution,[],[f92,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_pralg_1(X1)
      | v1_relat_1(k12_pralg_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f140,plain,(
    ~ spl7_17 ),
    inference(avatar_split_clause,[],[f37,f138])).

fof(f138,plain,
    ( spl7_17
  <=> k1_funct_1(k12_pralg_1(sK0,sK1),sK2) != u1_struct_0(k10_pralg_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f37,plain,(
    k1_funct_1(k12_pralg_1(sK0,sK1),sK2) != u1_struct_0(k10_pralg_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_funct_1(k12_pralg_1(X0,X1),X2) != u1_struct_0(k10_pralg_1(X0,X1,X2))
              & m1_subset_1(X2,X0) )
          & v2_pralg_1(X1)
          & v1_partfun1(X1,X0)
          & v1_funct_1(X1)
          & v4_relat_1(X1,X0)
          & v1_relat_1(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_funct_1(k12_pralg_1(X0,X1),X2) != u1_struct_0(k10_pralg_1(X0,X1,X2))
              & m1_subset_1(X2,X0) )
          & v2_pralg_1(X1)
          & v1_partfun1(X1,X0)
          & v1_funct_1(X1)
          & v4_relat_1(X1,X0)
          & v1_relat_1(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( v2_pralg_1(X1)
              & v1_partfun1(X1,X0)
              & v1_funct_1(X1)
              & v4_relat_1(X1,X0)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,X0)
               => k1_funct_1(k12_pralg_1(X0,X1),X2) = u1_struct_0(k10_pralg_1(X0,X1,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v2_pralg_1(X1)
            & v1_partfun1(X1,X0)
            & v1_funct_1(X1)
            & v4_relat_1(X1,X0)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => k1_funct_1(k12_pralg_1(X0,X1),X2) = u1_struct_0(k10_pralg_1(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t9_yellow_6.p',t9_yellow_6)).

fof(f136,plain,
    ( spl7_14
    | spl7_7
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f95,f83,f79,f134])).

fof(f95,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f94,f80])).

fof(f94,plain,
    ( v1_xboole_0(sK0)
    | r2_hidden(sK2,sK0)
    | ~ spl7_8 ),
    inference(resolution,[],[f84,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t9_yellow_6.p',t2_subset)).

fof(f93,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f41,f91])).

fof(f41,plain,(
    v1_partfun1(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f89,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f39,f87])).

fof(f39,plain,(
    v4_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f85,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f36,f83])).

fof(f36,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f81,plain,(
    ~ spl7_7 ),
    inference(avatar_split_clause,[],[f43,f79])).

fof(f43,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f77,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f42,f75])).

fof(f42,plain,(
    v2_pralg_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f73,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f40,f71])).

fof(f40,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f69,plain,(
    spl7_0 ),
    inference(avatar_split_clause,[],[f38,f67])).

fof(f38,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
