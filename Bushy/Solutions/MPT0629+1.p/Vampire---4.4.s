%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t25_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:22 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 185 expanded)
%              Number of leaves         :   16 (  67 expanded)
%              Depth                    :   12
%              Number of atoms          :  373 ( 677 expanded)
%              Number of equality atoms :   21 (  45 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1043,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f75,f79,f83,f99,f103,f156,f259,f994,f1031,f1042])).

fof(f1042,plain,
    ( ~ spl7_4
    | ~ spl7_6
    | spl7_9
    | ~ spl7_104 ),
    inference(avatar_contradiction_clause,[],[f1041])).

fof(f1041,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_9
    | ~ spl7_104 ),
    inference(subsumption_resolution,[],[f1040,f98])).

fof(f98,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl7_9
  <=> ~ r2_hidden(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f1040,plain,
    ( r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_104 ),
    inference(subsumption_resolution,[],[f1039,f78])).

fof(f78,plain,
    ( v1_relat_1(sK1)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl7_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f1039,plain,
    ( ~ v1_relat_1(sK1)
    | r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl7_6
    | ~ spl7_104 ),
    inference(subsumption_resolution,[],[f1038,f82])).

fof(f82,plain,
    ( v1_funct_1(sK1)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl7_6
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f1038,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl7_104 ),
    inference(resolution,[],[f1030,f66])).

fof(f66,plain,(
    ! [X2,X0] :
      ( ~ sP4(X2,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ sP4(X2,X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/funct_1__t25_funct_1.p',d5_funct_1)).

fof(f1030,plain,
    ( sP4(sK0,sK1)
    | ~ spl7_104 ),
    inference(avatar_component_clause,[],[f1029])).

fof(f1029,plain,
    ( spl7_104
  <=> sP4(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_104])])).

fof(f1031,plain,
    ( spl7_104
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_26
    | ~ spl7_38
    | ~ spl7_96 ),
    inference(avatar_split_clause,[],[f1019,f992,f257,f154,f81,f77,f73,f69,f1029])).

fof(f69,plain,
    ( spl7_0
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_0])])).

fof(f73,plain,
    ( spl7_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f154,plain,
    ( spl7_26
  <=> sP4(sK0,k5_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f257,plain,
    ( spl7_38
  <=> r2_hidden(sK5(k5_relat_1(sK2,sK1),sK0),k1_relat_1(k5_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f992,plain,
    ( spl7_96
  <=> r2_hidden(k1_funct_1(sK2,sK5(k5_relat_1(sK2,sK1),sK0)),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_96])])).

fof(f1019,plain,
    ( sP4(sK0,sK1)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_26
    | ~ spl7_38
    | ~ spl7_96 ),
    inference(forward_demodulation,[],[f1015,f275])).

fof(f275,plain,
    ( k1_funct_1(sK1,k1_funct_1(sK2,sK5(k5_relat_1(sK2,sK1),sK0))) = sK0
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_26
    | ~ spl7_38 ),
    inference(forward_demodulation,[],[f274,f161])).

fof(f161,plain,
    ( k1_funct_1(k5_relat_1(sK2,sK1),sK5(k5_relat_1(sK2,sK1),sK0)) = sK0
    | ~ spl7_26 ),
    inference(resolution,[],[f155,f49])).

fof(f49,plain,(
    ! [X2,X0] :
      ( ~ sP4(X2,X0)
      | k1_funct_1(X0,sK5(X0,X2)) = X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f155,plain,
    ( sP4(sK0,k5_relat_1(sK2,sK1))
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f154])).

fof(f274,plain,
    ( k1_funct_1(k5_relat_1(sK2,sK1),sK5(k5_relat_1(sK2,sK1),sK0)) = k1_funct_1(sK1,k1_funct_1(sK2,sK5(k5_relat_1(sK2,sK1),sK0)))
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_38 ),
    inference(subsumption_resolution,[],[f273,f78])).

fof(f273,plain,
    ( ~ v1_relat_1(sK1)
    | k1_funct_1(k5_relat_1(sK2,sK1),sK5(k5_relat_1(sK2,sK1),sK0)) = k1_funct_1(sK1,k1_funct_1(sK2,sK5(k5_relat_1(sK2,sK1),sK0)))
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_38 ),
    inference(subsumption_resolution,[],[f272,f74])).

fof(f74,plain,
    ( v1_funct_1(sK2)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f272,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK1)
    | k1_funct_1(k5_relat_1(sK2,sK1),sK5(k5_relat_1(sK2,sK1),sK0)) = k1_funct_1(sK1,k1_funct_1(sK2,sK5(k5_relat_1(sK2,sK1),sK0)))
    | ~ spl7_0
    | ~ spl7_6
    | ~ spl7_38 ),
    inference(subsumption_resolution,[],[f271,f70])).

fof(f70,plain,
    ( v1_relat_1(sK2)
    | ~ spl7_0 ),
    inference(avatar_component_clause,[],[f69])).

fof(f271,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK1)
    | k1_funct_1(k5_relat_1(sK2,sK1),sK5(k5_relat_1(sK2,sK1),sK0)) = k1_funct_1(sK1,k1_funct_1(sK2,sK5(k5_relat_1(sK2,sK1),sK0)))
    | ~ spl7_6
    | ~ spl7_38 ),
    inference(subsumption_resolution,[],[f264,f82])).

fof(f264,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK1)
    | k1_funct_1(k5_relat_1(sK2,sK1),sK5(k5_relat_1(sK2,sK1),sK0)) = k1_funct_1(sK1,k1_funct_1(sK2,sK5(k5_relat_1(sK2,sK1),sK0)))
    | ~ spl7_38 ),
    inference(resolution,[],[f258,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X1)
      | k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0)
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0)
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
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
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
           => k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t25_funct_1.p',t22_funct_1)).

fof(f258,plain,
    ( r2_hidden(sK5(k5_relat_1(sK2,sK1),sK0),k1_relat_1(k5_relat_1(sK2,sK1)))
    | ~ spl7_38 ),
    inference(avatar_component_clause,[],[f257])).

fof(f1015,plain,
    ( sP4(k1_funct_1(sK1,k1_funct_1(sK2,sK5(k5_relat_1(sK2,sK1),sK0))),sK1)
    | ~ spl7_96 ),
    inference(resolution,[],[f993,f67])).

fof(f67,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(X0))
      | sP4(k1_funct_1(X0,X3),X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | sP4(X2,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f993,plain,
    ( r2_hidden(k1_funct_1(sK2,sK5(k5_relat_1(sK2,sK1),sK0)),k1_relat_1(sK1))
    | ~ spl7_96 ),
    inference(avatar_component_clause,[],[f992])).

fof(f994,plain,
    ( spl7_96
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_38 ),
    inference(avatar_split_clause,[],[f283,f257,f81,f77,f73,f69,f992])).

fof(f283,plain,
    ( r2_hidden(k1_funct_1(sK2,sK5(k5_relat_1(sK2,sK1),sK0)),k1_relat_1(sK1))
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_38 ),
    inference(subsumption_resolution,[],[f282,f78])).

fof(f282,plain,
    ( r2_hidden(k1_funct_1(sK2,sK5(k5_relat_1(sK2,sK1),sK0)),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_38 ),
    inference(subsumption_resolution,[],[f281,f74])).

fof(f281,plain,
    ( ~ v1_funct_1(sK2)
    | r2_hidden(k1_funct_1(sK2,sK5(k5_relat_1(sK2,sK1),sK0)),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl7_0
    | ~ spl7_6
    | ~ spl7_38 ),
    inference(subsumption_resolution,[],[f280,f70])).

fof(f280,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | r2_hidden(k1_funct_1(sK2,sK5(k5_relat_1(sK2,sK1),sK0)),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl7_6
    | ~ spl7_38 ),
    inference(subsumption_resolution,[],[f266,f82])).

fof(f266,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | r2_hidden(k1_funct_1(sK2,sK5(k5_relat_1(sK2,sK1),sK0)),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl7_38 ),
    inference(resolution,[],[f258,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t25_funct_1.p',t21_funct_1)).

fof(f259,plain,
    ( spl7_38
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f160,f154,f257])).

fof(f160,plain,
    ( r2_hidden(sK5(k5_relat_1(sK2,sK1),sK0),k1_relat_1(k5_relat_1(sK2,sK1)))
    | ~ spl7_26 ),
    inference(resolution,[],[f155,f48])).

fof(f48,plain,(
    ! [X2,X0] :
      ( ~ sP4(X2,X0)
      | r2_hidden(sK5(X0,X2),k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f156,plain,
    ( spl7_26
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f149,f101,f81,f77,f73,f69,f154])).

fof(f101,plain,
    ( spl7_10
  <=> r2_hidden(sK0,k2_relat_1(k5_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f149,plain,
    ( sP4(sK0,k5_relat_1(sK2,sK1))
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f114,f148])).

fof(f148,plain,
    ( v1_funct_1(k5_relat_1(sK2,sK1))
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f146,f78])).

fof(f146,plain,
    ( ~ v1_relat_1(sK1)
    | v1_funct_1(k5_relat_1(sK2,sK1))
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(resolution,[],[f88,f82])).

fof(f88,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | v1_funct_1(k5_relat_1(sK2,X1)) )
    | ~ spl7_0
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f86,f70])).

fof(f86,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(sK2)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | v1_funct_1(k5_relat_1(sK2,X1)) )
    | ~ spl7_2 ),
    inference(resolution,[],[f74,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | v1_funct_1(k5_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t25_funct_1.p',fc2_funct_1)).

fof(f114,plain,
    ( ~ v1_funct_1(k5_relat_1(sK2,sK1))
    | sP4(sK0,k5_relat_1(sK2,sK1))
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f104,f113])).

fof(f113,plain,
    ( v1_relat_1(k5_relat_1(sK2,sK1))
    | ~ spl7_0
    | ~ spl7_4 ),
    inference(resolution,[],[f84,f78])).

fof(f84,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | v1_relat_1(k5_relat_1(sK2,X0)) )
    | ~ spl7_0 ),
    inference(resolution,[],[f70,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | v1_relat_1(k5_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t25_funct_1.p',dt_k5_relat_1)).

fof(f104,plain,
    ( ~ v1_funct_1(k5_relat_1(sK2,sK1))
    | sP4(sK0,k5_relat_1(sK2,sK1))
    | ~ v1_relat_1(k5_relat_1(sK2,sK1))
    | ~ spl7_10 ),
    inference(resolution,[],[f102,f65])).

fof(f65,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | sP4(X2,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | sP4(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f102,plain,
    ( r2_hidden(sK0,k2_relat_1(k5_relat_1(sK2,sK1)))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f101])).

fof(f103,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f41,f101])).

fof(f41,plain,(
    r2_hidden(sK0,k2_relat_1(k5_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X0,k2_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X0,k2_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))
             => r2_hidden(X0,k2_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))
           => r2_hidden(X0,k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t25_funct_1.p',t25_funct_1)).

fof(f99,plain,(
    ~ spl7_9 ),
    inference(avatar_split_clause,[],[f42,f97])).

fof(f42,plain,(
    ~ r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f83,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f44,f81])).

fof(f44,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f79,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f43,f77])).

fof(f43,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f75,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f40,f73])).

fof(f40,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f71,plain,(
    spl7_0 ),
    inference(avatar_split_clause,[],[f39,f69])).

fof(f39,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
