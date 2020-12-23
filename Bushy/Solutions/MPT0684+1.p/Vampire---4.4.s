%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t138_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:15 EDT 2019

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :  189 ( 528 expanded)
%              Number of leaves         :   34 ( 189 expanded)
%              Depth                    :   13
%              Number of atoms          :  608 (1589 expanded)
%              Number of equality atoms :   33 ( 183 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f961,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f83,f90,f112,f131,f137,f152,f159,f168,f184,f217,f233,f250,f319,f405,f410,f433,f504,f515,f520,f564,f600,f657,f691,f826,f878,f909,f919,f920,f960])).

fof(f960,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | spl6_31
    | ~ spl6_32 ),
    inference(avatar_contradiction_clause,[],[f959])).

fof(f959,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_31
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f958,f511])).

fof(f511,plain,
    ( r2_hidden(sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k10_relat_1(sK2,sK1))
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f510])).

fof(f510,plain,
    ( spl6_32
  <=> r2_hidden(sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f958,plain,
    ( ~ r2_hidden(sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k10_relat_1(sK2,sK1))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_31 ),
    inference(subsumption_resolution,[],[f957,f75])).

fof(f75,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_0 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl6_0
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_0])])).

fof(f957,plain,
    ( ~ v1_relat_1(sK2)
    | ~ r2_hidden(sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k10_relat_1(sK2,sK1))
    | ~ spl6_2
    | ~ spl6_31 ),
    inference(subsumption_resolution,[],[f956,f82])).

fof(f82,plain,
    ( v1_funct_1(sK2)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl6_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f956,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ r2_hidden(sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k10_relat_1(sK2,sK1))
    | ~ spl6_31 ),
    inference(resolution,[],[f432,f62])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X0,X3),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(k1_funct_1(X0,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t138_funct_1.p',d13_funct_1)).

fof(f432,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))),sK1)
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f431])).

fof(f431,plain,
    ( spl6_31
  <=> ~ r2_hidden(k1_funct_1(sK2,sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f920,plain,
    ( spl6_32
    | spl6_9
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f917,f157,f123,f510])).

fof(f123,plain,
    ( spl6_9
  <=> ~ r2_hidden(sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f157,plain,
    ( spl6_16
  <=> r2_hidden(sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k10_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f917,plain,
    ( r2_hidden(sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k10_relat_1(sK2,sK1))
    | ~ spl6_9
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f916,f158])).

fof(f158,plain,
    ( r2_hidden(sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k10_relat_1(sK2,sK0))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f157])).

fof(f916,plain,
    ( ~ r2_hidden(sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k10_relat_1(sK2,sK0))
    | r2_hidden(sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k10_relat_1(sK2,sK1))
    | ~ spl6_9 ),
    inference(resolution,[],[f124,f64])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k6_subset_1(X0,X1))
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(forward_demodulation,[],[f58,f47])).

fof(f47,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t138_funct_1.p',redefinition_k6_subset_1)).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t138_funct_1.p',d5_xboole_0)).

fof(f124,plain,
    ( ~ r2_hidden(sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f123])).

fof(f919,plain,
    ( spl6_9
    | ~ spl6_16
    | spl6_33 ),
    inference(avatar_contradiction_clause,[],[f918])).

fof(f918,plain,
    ( $false
    | ~ spl6_9
    | ~ spl6_16
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f917,f514])).

fof(f514,plain,
    ( ~ r2_hidden(sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k10_relat_1(sK2,sK1))
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f513])).

fof(f513,plain,
    ( spl6_33
  <=> ~ r2_hidden(sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f909,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | ~ spl6_18
    | ~ spl6_30
    | spl6_33 ),
    inference(avatar_contradiction_clause,[],[f908])).

fof(f908,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_18
    | ~ spl6_30
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f907,f514])).

fof(f907,plain,
    ( r2_hidden(sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k10_relat_1(sK2,sK1))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_18
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f906,f75])).

fof(f906,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k10_relat_1(sK2,sK1))
    | ~ spl6_2
    | ~ spl6_18
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f905,f183])).

fof(f183,plain,
    ( r2_hidden(sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k1_relat_1(sK2))
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl6_18
  <=> r2_hidden(sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f905,plain,
    ( ~ r2_hidden(sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | r2_hidden(sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k10_relat_1(sK2,sK1))
    | ~ spl6_2
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f904,f82])).

fof(f904,plain,
    ( ~ v1_funct_1(sK2)
    | ~ r2_hidden(sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | r2_hidden(sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k10_relat_1(sK2,sK1))
    | ~ spl6_30 ),
    inference(resolution,[],[f429,f61])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(k1_funct_1(X0,X3),X1)
      | r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f429,plain,
    ( r2_hidden(k1_funct_1(sK2,sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))),sK1)
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f428])).

fof(f428,plain,
    ( spl6_30
  <=> r2_hidden(k1_funct_1(sK2,sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f878,plain,
    ( spl6_30
    | ~ spl6_0
    | ~ spl6_2
    | spl6_11
    | ~ spl6_18
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f655,f317,f182,f129,f81,f74,f428])).

fof(f129,plain,
    ( spl6_11
  <=> ~ r2_hidden(sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k10_relat_1(sK2,k6_subset_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f317,plain,
    ( spl6_26
  <=> r2_hidden(k1_funct_1(sK2,sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f655,plain,
    ( r2_hidden(k1_funct_1(sK2,sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))),sK1)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_11
    | ~ spl6_18
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f654,f318])).

fof(f318,plain,
    ( r2_hidden(k1_funct_1(sK2,sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))),sK0)
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f317])).

fof(f654,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))),sK0)
    | r2_hidden(k1_funct_1(sK2,sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))),sK1)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_11
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f653,f82])).

fof(f653,plain,
    ( ~ v1_funct_1(sK2)
    | ~ r2_hidden(k1_funct_1(sK2,sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))),sK0)
    | r2_hidden(k1_funct_1(sK2,sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))),sK1)
    | ~ spl6_0
    | ~ spl6_11
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f652,f75])).

fof(f652,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ r2_hidden(k1_funct_1(sK2,sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))),sK0)
    | r2_hidden(k1_funct_1(sK2,sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))),sK1)
    | ~ spl6_11
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f641,f183])).

fof(f641,plain,
    ( ~ r2_hidden(sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ r2_hidden(k1_funct_1(sK2,sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))),sK0)
    | r2_hidden(k1_funct_1(sK2,sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))),sK1)
    | ~ spl6_11 ),
    inference(resolution,[],[f198,f130])).

fof(f130,plain,
    ( ~ r2_hidden(sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f129])).

fof(f198,plain,(
    ! [X6,X4,X5,X3] :
      ( r2_hidden(X4,k10_relat_1(X3,k6_subset_1(X5,X6)))
      | ~ r2_hidden(X4,k1_relat_1(X3))
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X3)
      | ~ r2_hidden(k1_funct_1(X3,X4),X5)
      | r2_hidden(k1_funct_1(X3,X4),X6) ) ),
    inference(resolution,[],[f61,f64])).

fof(f826,plain,
    ( spl6_24
    | spl6_5
    | spl6_13 ),
    inference(avatar_split_clause,[],[f411,f144,f88,f245])).

fof(f245,plain,
    ( spl6_24
  <=> r2_hidden(sK4(k10_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f88,plain,
    ( spl6_5
  <=> k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) != k10_relat_1(sK2,k6_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f144,plain,
    ( spl6_13
  <=> ~ r2_hidden(sK4(k10_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,k6_subset_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f411,plain,
    ( r2_hidden(sK4(k10_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK0))
    | ~ spl6_5
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f406,f89])).

fof(f89,plain,
    ( k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) != k10_relat_1(sK2,k6_subset_1(sK0,sK1))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f88])).

fof(f406,plain,
    ( r2_hidden(sK4(k10_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK0))
    | k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = k10_relat_1(sK2,k6_subset_1(sK0,sK1))
    | ~ spl6_13 ),
    inference(resolution,[],[f145,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,k6_subset_1(X1,X2)),X1)
      | r2_hidden(sK4(X0,k6_subset_1(X1,X2)),X0)
      | k6_subset_1(X1,X2) = X0 ) ),
    inference(resolution,[],[f45,f66])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k6_subset_1(X0,X1))
      | r2_hidden(X3,X0) ) ),
    inference(forward_demodulation,[],[f60,f47])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r2_hidden(sK4(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t138_funct_1.p',t2_tarski)).

fof(f145,plain,
    ( ~ r2_hidden(sK4(k10_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f144])).

fof(f691,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | spl6_5
    | spl6_13
    | spl6_29 ),
    inference(avatar_contradiction_clause,[],[f690])).

fof(f690,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_13
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f689,f411])).

fof(f689,plain,
    ( ~ r2_hidden(sK4(k10_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK0))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f688,f75])).

fof(f688,plain,
    ( ~ v1_relat_1(sK2)
    | ~ r2_hidden(sK4(k10_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK0))
    | ~ spl6_2
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f687,f82])).

fof(f687,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ r2_hidden(sK4(k10_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK0))
    | ~ spl6_29 ),
    inference(resolution,[],[f401,f62])).

fof(f401,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK4(k10_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK0)
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f400])).

fof(f400,plain,
    ( spl6_29
  <=> ~ r2_hidden(k1_funct_1(sK2,sK4(k10_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f657,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | spl6_11
    | ~ spl6_18
    | ~ spl6_26
    | spl6_31 ),
    inference(avatar_contradiction_clause,[],[f656])).

fof(f656,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_11
    | ~ spl6_18
    | ~ spl6_26
    | ~ spl6_31 ),
    inference(subsumption_resolution,[],[f655,f432])).

fof(f600,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | ~ spl6_16
    | spl6_27 ),
    inference(avatar_contradiction_clause,[],[f599])).

fof(f599,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_16
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f598,f158])).

fof(f598,plain,
    ( ~ r2_hidden(sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k10_relat_1(sK2,sK0))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f597,f75])).

fof(f597,plain,
    ( ~ v1_relat_1(sK2)
    | ~ r2_hidden(sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k10_relat_1(sK2,sK0))
    | ~ spl6_2
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f596,f82])).

fof(f596,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ r2_hidden(sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k10_relat_1(sK2,sK0))
    | ~ spl6_27 ),
    inference(resolution,[],[f315,f62])).

fof(f315,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))),sK0)
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f314])).

fof(f314,plain,
    ( spl6_27
  <=> ~ r2_hidden(k1_funct_1(sK2,sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f564,plain,
    ( spl6_18
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f521,f157,f81,f74,f182])).

fof(f521,plain,
    ( r2_hidden(sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k1_relat_1(sK2))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f517,f75])).

fof(f517,plain,
    ( r2_hidden(sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl6_2
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f516,f82])).

fof(f516,plain,
    ( ~ v1_funct_1(sK2)
    | r2_hidden(sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl6_16 ),
    inference(resolution,[],[f158,f63])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k10_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | r2_hidden(X3,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f520,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | ~ spl6_16
    | spl6_19 ),
    inference(avatar_contradiction_clause,[],[f519])).

fof(f519,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_16
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f518,f75])).

fof(f518,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl6_2
    | ~ spl6_16
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f517,f180])).

fof(f180,plain,
    ( ~ r2_hidden(sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k1_relat_1(sK2))
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl6_19
  <=> ~ r2_hidden(sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f515,plain,
    ( ~ spl6_33
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f139,f120,f513])).

fof(f120,plain,
    ( spl6_8
  <=> r2_hidden(sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f139,plain,
    ( ~ r2_hidden(sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k10_relat_1(sK2,sK1))
    | ~ spl6_8 ),
    inference(resolution,[],[f121,f65])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k6_subset_1(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(forward_demodulation,[],[f59,f47])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f121,plain,
    ( r2_hidden(sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f120])).

fof(f504,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | spl6_17
    | ~ spl6_18
    | ~ spl6_26 ),
    inference(avatar_contradiction_clause,[],[f503])).

fof(f503,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f502,f155])).

fof(f155,plain,
    ( ~ r2_hidden(sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k10_relat_1(sK2,sK0))
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl6_17
  <=> ~ r2_hidden(sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k10_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f502,plain,
    ( r2_hidden(sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k10_relat_1(sK2,sK0))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_18
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f501,f75])).

fof(f501,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k10_relat_1(sK2,sK0))
    | ~ spl6_2
    | ~ spl6_18
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f500,f183])).

fof(f500,plain,
    ( ~ r2_hidden(sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | r2_hidden(sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k10_relat_1(sK2,sK0))
    | ~ spl6_2
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f499,f82])).

fof(f499,plain,
    ( ~ v1_funct_1(sK2)
    | ~ r2_hidden(sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | r2_hidden(sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k10_relat_1(sK2,sK0))
    | ~ spl6_26 ),
    inference(resolution,[],[f318,f61])).

fof(f433,plain,
    ( ~ spl6_31
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f310,f126,f81,f74,f431])).

fof(f126,plain,
    ( spl6_10
  <=> r2_hidden(sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k10_relat_1(sK2,k6_subset_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f310,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))),sK1)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f309,f82])).

fof(f309,plain,
    ( ~ v1_funct_1(sK2)
    | ~ r2_hidden(k1_funct_1(sK2,sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))),sK1)
    | ~ spl6_0
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f303,f75])).

fof(f303,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ r2_hidden(k1_funct_1(sK2,sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))),sK1)
    | ~ spl6_10 ),
    inference(resolution,[],[f176,f127])).

fof(f127,plain,
    ( r2_hidden(sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f126])).

fof(f176,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_hidden(X5,k10_relat_1(X4,k6_subset_1(X6,X7)))
      | ~ v1_relat_1(X4)
      | ~ v1_funct_1(X4)
      | ~ r2_hidden(k1_funct_1(X4,X5),X7) ) ),
    inference(resolution,[],[f62,f65])).

fof(f410,plain,
    ( spl6_5
    | spl6_13
    | spl6_25 ),
    inference(avatar_contradiction_clause,[],[f409])).

fof(f409,plain,
    ( $false
    | ~ spl6_5
    | ~ spl6_13
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f408,f89])).

fof(f408,plain,
    ( k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = k10_relat_1(sK2,k6_subset_1(sK0,sK1))
    | ~ spl6_13
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f406,f249])).

fof(f249,plain,
    ( ~ r2_hidden(sK4(k10_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK0))
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f248])).

fof(f248,plain,
    ( spl6_25
  <=> ~ r2_hidden(sK4(k10_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f405,plain,
    ( spl6_28
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f294,f141,f81,f74,f403])).

fof(f403,plain,
    ( spl6_28
  <=> r2_hidden(k1_funct_1(sK2,sK4(k10_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f141,plain,
    ( spl6_12
  <=> r2_hidden(sK4(k10_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,k6_subset_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f294,plain,
    ( r2_hidden(k1_funct_1(sK2,sK4(k10_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK0)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f293,f82])).

fof(f293,plain,
    ( ~ v1_funct_1(sK2)
    | r2_hidden(k1_funct_1(sK2,sK4(k10_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK0)
    | ~ spl6_0
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f286,f75])).

fof(f286,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | r2_hidden(k1_funct_1(sK2,sK4(k10_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK0)
    | ~ spl6_12 ),
    inference(resolution,[],[f175,f142])).

fof(f142,plain,
    ( r2_hidden(sK4(k10_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f141])).

fof(f175,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X1,k10_relat_1(X0,k6_subset_1(X2,X3)))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(k1_funct_1(X0,X1),X2) ) ),
    inference(resolution,[],[f62,f66])).

fof(f319,plain,
    ( spl6_26
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f292,f126,f81,f74,f317])).

fof(f292,plain,
    ( r2_hidden(k1_funct_1(sK2,sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))),sK0)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f291,f82])).

fof(f291,plain,
    ( ~ v1_funct_1(sK2)
    | r2_hidden(k1_funct_1(sK2,sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))),sK0)
    | ~ spl6_0
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f285,f75])).

fof(f285,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | r2_hidden(k1_funct_1(sK2,sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))),sK0)
    | ~ spl6_10 ),
    inference(resolution,[],[f175,f127])).

fof(f250,plain,
    ( spl6_22
    | ~ spl6_25
    | spl6_15 ),
    inference(avatar_split_clause,[],[f165,f150,f248,f242])).

fof(f242,plain,
    ( spl6_22
  <=> r2_hidden(sK4(k10_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f150,plain,
    ( spl6_15
  <=> ~ r2_hidden(sK4(k10_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f165,plain,
    ( ~ r2_hidden(sK4(k10_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK0))
    | r2_hidden(sK4(k10_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK1))
    | ~ spl6_15 ),
    inference(resolution,[],[f151,f64])).

fof(f151,plain,
    ( ~ r2_hidden(sK4(k10_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f150])).

fof(f233,plain,
    ( spl6_20
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f220,f141,f81,f74,f231])).

fof(f231,plain,
    ( spl6_20
  <=> r2_hidden(sK4(k10_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f220,plain,
    ( r2_hidden(sK4(k10_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k1_relat_1(sK2))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f219,f75])).

fof(f219,plain,
    ( r2_hidden(sK4(k10_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f218,f82])).

fof(f218,plain,
    ( ~ v1_funct_1(sK2)
    | r2_hidden(sK4(k10_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl6_12 ),
    inference(resolution,[],[f142,f63])).

fof(f217,plain,
    ( spl6_12
    | spl6_5
    | spl6_15 ),
    inference(avatar_split_clause,[],[f169,f150,f88,f141])).

fof(f169,plain,
    ( r2_hidden(sK4(k10_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))
    | ~ spl6_5
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f164,f89])).

fof(f164,plain,
    ( r2_hidden(sK4(k10_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))
    | k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = k10_relat_1(sK2,k6_subset_1(sK0,sK1))
    | ~ spl6_15 ),
    inference(resolution,[],[f151,f45])).

fof(f184,plain,
    ( spl6_18
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f174,f126,f81,f74,f182])).

fof(f174,plain,
    ( r2_hidden(sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k1_relat_1(sK2))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f173,f75])).

fof(f173,plain,
    ( r2_hidden(sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f172,f82])).

fof(f172,plain,
    ( ~ v1_funct_1(sK2)
    | r2_hidden(sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl6_10 ),
    inference(resolution,[],[f63,f127])).

fof(f168,plain,
    ( spl6_5
    | spl6_13
    | spl6_15 ),
    inference(avatar_contradiction_clause,[],[f167])).

fof(f167,plain,
    ( $false
    | ~ spl6_5
    | ~ spl6_13
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f166,f89])).

fof(f166,plain,
    ( k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = k10_relat_1(sK2,k6_subset_1(sK0,sK1))
    | ~ spl6_13
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f164,f145])).

fof(f159,plain,
    ( spl6_16
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f138,f120,f157])).

fof(f138,plain,
    ( r2_hidden(sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k10_relat_1(sK2,sK0))
    | ~ spl6_8 ),
    inference(resolution,[],[f121,f66])).

fof(f152,plain,
    ( ~ spl6_13
    | ~ spl6_15
    | spl6_5 ),
    inference(avatar_split_clause,[],[f114,f88,f150,f144])).

fof(f114,plain,
    ( ~ r2_hidden(sK4(k10_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))
    | ~ r2_hidden(sK4(k10_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))
    | ~ spl6_5 ),
    inference(extensionality_resolution,[],[f46,f89])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | ~ r2_hidden(sK4(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f137,plain,
    ( spl6_5
    | spl6_9
    | spl6_11 ),
    inference(avatar_contradiction_clause,[],[f136])).

fof(f136,plain,
    ( $false
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f135,f89])).

fof(f135,plain,
    ( k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = k10_relat_1(sK2,k6_subset_1(sK0,sK1))
    | ~ spl6_9
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f133,f130])).

fof(f133,plain,
    ( r2_hidden(sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))
    | k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = k10_relat_1(sK2,k6_subset_1(sK0,sK1))
    | ~ spl6_9 ),
    inference(resolution,[],[f124,f45])).

fof(f131,plain,
    ( ~ spl6_9
    | ~ spl6_11
    | spl6_5 ),
    inference(avatar_split_clause,[],[f113,f88,f129,f123])).

fof(f113,plain,
    ( ~ r2_hidden(sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))
    | ~ r2_hidden(sK4(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))),k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))
    | ~ spl6_5 ),
    inference(extensionality_resolution,[],[f46,f89])).

fof(f112,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f96,f110])).

fof(f110,plain,
    ( spl6_6
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f96,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f51,f91])).

fof(f91,plain,(
    ! [X0] : k6_subset_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[],[f47,f49])).

fof(f49,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/funct_1__t138_funct_1.p',t4_boole)).

fof(f51,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t138_funct_1.p',dt_k6_subset_1)).

fof(f90,plain,(
    ~ spl6_5 ),
    inference(avatar_split_clause,[],[f37,f88])).

fof(f37,plain,(
    k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) != k10_relat_1(sK2,k6_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) != k10_relat_1(X2,k6_subset_1(X0,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) != k10_relat_1(X2,k6_subset_1(X0,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t138_funct_1.p',t138_funct_1)).

fof(f83,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f36,f81])).

fof(f36,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f76,plain,(
    spl6_0 ),
    inference(avatar_split_clause,[],[f35,f74])).

fof(f35,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
