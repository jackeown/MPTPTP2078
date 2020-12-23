%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t50_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:24 EDT 2019

% Result     : Theorem 4.13s
% Output     : Refutation 4.13s
% Verified   : 
% Statistics : Number of formulae       :  175 ( 340 expanded)
%              Number of leaves         :   39 ( 144 expanded)
%              Depth                    :   15
%              Number of atoms          :  771 (1811 expanded)
%              Number of equality atoms :  202 ( 596 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f63174,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f125,f132,f139,f146,f153,f167,f174,f181,f188,f195,f333,f351,f390,f420,f567,f663,f949,f5223,f8371,f11543,f11561,f19638,f62011,f63173])).

fof(f63173,plain,
    ( ~ spl11_42
    | spl11_65
    | ~ spl11_4390 ),
    inference(avatar_contradiction_clause,[],[f63172])).

fof(f63172,plain,
    ( $false
    | ~ spl11_42
    | ~ spl11_65
    | ~ spl11_4390 ),
    inference(subsumption_resolution,[],[f63171,f419])).

fof(f419,plain,
    ( k1_funct_1(sK2,sK9(sK0,sK2)) != sK9(sK0,sK2)
    | ~ spl11_65 ),
    inference(avatar_component_clause,[],[f418])).

fof(f418,plain,
    ( spl11_65
  <=> k1_funct_1(sK2,sK9(sK0,sK2)) != sK9(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_65])])).

fof(f63171,plain,
    ( k1_funct_1(sK2,sK9(sK0,sK2)) = sK9(sK0,sK2)
    | ~ spl11_42
    | ~ spl11_4390 ),
    inference(subsumption_resolution,[],[f63146,f332])).

fof(f332,plain,
    ( r2_hidden(sK9(sK0,sK2),sK0)
    | ~ spl11_42 ),
    inference(avatar_component_clause,[],[f331])).

fof(f331,plain,
    ( spl11_42
  <=> r2_hidden(sK9(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_42])])).

fof(f63146,plain,
    ( ~ r2_hidden(sK9(sK0,sK2),sK0)
    | k1_funct_1(sK2,sK9(sK0,sK2)) = sK9(sK0,sK2)
    | ~ spl11_4390 ),
    inference(equality_resolution,[],[f62002])).

fof(f62002,plain,
    ( ! [X1] :
        ( k1_funct_1(sK1,X1) != k1_funct_1(sK1,sK9(sK0,sK2))
        | ~ r2_hidden(X1,sK0)
        | k1_funct_1(sK2,sK9(sK0,sK2)) = X1 )
    | ~ spl11_4390 ),
    inference(avatar_component_clause,[],[f62001])).

fof(f62001,plain,
    ( spl11_4390
  <=> ! [X1] :
        ( ~ r2_hidden(X1,sK0)
        | k1_funct_1(sK1,X1) != k1_funct_1(sK1,sK9(sK0,sK2))
        | k1_funct_1(sK2,sK9(sK0,sK2)) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4390])])).

fof(f62011,plain,
    ( spl11_4390
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_8
    | ~ spl11_12
    | ~ spl11_894
    | ~ spl11_1362 ),
    inference(avatar_split_clause,[],[f26745,f11559,f8369,f165,f151,f130,f123,f62001])).

fof(f123,plain,
    ( spl11_0
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_0])])).

fof(f130,plain,
    ( spl11_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f151,plain,
    ( spl11_8
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f165,plain,
    ( spl11_12
  <=> k1_relat_1(sK1) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f8369,plain,
    ( spl11_894
  <=> k1_funct_1(sK1,sK9(sK0,sK2)) = k1_funct_1(sK1,k1_funct_1(sK2,sK9(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_894])])).

fof(f11559,plain,
    ( spl11_1362
  <=> r2_hidden(k1_funct_1(sK2,sK9(sK0,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1362])])).

fof(f26745,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK0)
        | k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK9(sK0,sK2))
        | k1_funct_1(sK2,sK9(sK0,sK2)) = X2 )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_8
    | ~ spl11_12
    | ~ spl11_894
    | ~ spl11_1362 ),
    inference(subsumption_resolution,[],[f26744,f11560])).

fof(f11560,plain,
    ( r2_hidden(k1_funct_1(sK2,sK9(sK0,sK2)),sK0)
    | ~ spl11_1362 ),
    inference(avatar_component_clause,[],[f11559])).

fof(f26744,plain,
    ( ! [X2] :
        ( ~ r2_hidden(k1_funct_1(sK2,sK9(sK0,sK2)),sK0)
        | ~ r2_hidden(X2,sK0)
        | k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK9(sK0,sK2))
        | k1_funct_1(sK2,sK9(sK0,sK2)) = X2 )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_8
    | ~ spl11_12
    | ~ spl11_894 ),
    inference(forward_demodulation,[],[f26743,f166])).

fof(f166,plain,
    ( k1_relat_1(sK1) = sK0
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f165])).

fof(f26743,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK0)
        | k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK9(sK0,sK2))
        | k1_funct_1(sK2,sK9(sK0,sK2)) = X2
        | ~ r2_hidden(k1_funct_1(sK2,sK9(sK0,sK2)),k1_relat_1(sK1)) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_8
    | ~ spl11_12
    | ~ spl11_894 ),
    inference(forward_demodulation,[],[f26742,f166])).

fof(f26742,plain,
    ( ! [X2] :
        ( k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK9(sK0,sK2))
        | k1_funct_1(sK2,sK9(sK0,sK2)) = X2
        | ~ r2_hidden(X2,k1_relat_1(sK1))
        | ~ r2_hidden(k1_funct_1(sK2,sK9(sK0,sK2)),k1_relat_1(sK1)) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_8
    | ~ spl11_894 ),
    inference(subsumption_resolution,[],[f26741,f124])).

fof(f124,plain,
    ( v1_relat_1(sK1)
    | ~ spl11_0 ),
    inference(avatar_component_clause,[],[f123])).

fof(f26741,plain,
    ( ! [X2] :
        ( k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK9(sK0,sK2))
        | k1_funct_1(sK2,sK9(sK0,sK2)) = X2
        | ~ r2_hidden(X2,k1_relat_1(sK1))
        | ~ r2_hidden(k1_funct_1(sK2,sK9(sK0,sK2)),k1_relat_1(sK1))
        | ~ v1_relat_1(sK1) )
    | ~ spl11_2
    | ~ spl11_8
    | ~ spl11_894 ),
    inference(subsumption_resolution,[],[f26740,f131])).

fof(f131,plain,
    ( v1_funct_1(sK1)
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f130])).

fof(f26740,plain,
    ( ! [X2] :
        ( k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK9(sK0,sK2))
        | k1_funct_1(sK2,sK9(sK0,sK2)) = X2
        | ~ r2_hidden(X2,k1_relat_1(sK1))
        | ~ r2_hidden(k1_funct_1(sK2,sK9(sK0,sK2)),k1_relat_1(sK1))
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl11_8
    | ~ spl11_894 ),
    inference(subsumption_resolution,[],[f26727,f152])).

fof(f152,plain,
    ( v2_funct_1(sK1)
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f151])).

fof(f26727,plain,
    ( ! [X2] :
        ( k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK9(sK0,sK2))
        | k1_funct_1(sK2,sK9(sK0,sK2)) = X2
        | ~ r2_hidden(X2,k1_relat_1(sK1))
        | ~ r2_hidden(k1_funct_1(sK2,sK9(sK0,sK2)),k1_relat_1(sK1))
        | ~ v2_funct_1(sK1)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl11_894 ),
    inference(superposition,[],[f82,f8370])).

fof(f8370,plain,
    ( k1_funct_1(sK1,sK9(sK0,sK2)) = k1_funct_1(sK1,k1_funct_1(sK2,sK9(sK0,sK2)))
    | ~ spl11_894 ),
    inference(avatar_component_clause,[],[f8369])).

fof(f82,plain,(
    ! [X4,X0,X3] :
      ( k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | X3 = X4
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK3(X0) != sK4(X0)
            & k1_funct_1(X0,sK3(X0)) = k1_funct_1(X0,sK4(X0))
            & r2_hidden(sK4(X0),k1_relat_1(X0))
            & r2_hidden(sK3(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f52,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK3(X0) != sK4(X0)
        & k1_funct_1(X0,sK3(X0)) = k1_funct_1(X0,sK4(X0))
        & r2_hidden(sK4(X0),k1_relat_1(X0))
        & r2_hidden(sK3(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( X1 = X2
              | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
              | ~ r2_hidden(X2,k1_relat_1(X0))
              | ~ r2_hidden(X1,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t50_funct_1.p',d8_funct_1)).

fof(f19638,plain,
    ( spl11_1360
    | ~ spl11_16
    | ~ spl11_1336 ),
    inference(avatar_split_clause,[],[f11848,f11474,f179,f11549])).

fof(f11549,plain,
    ( spl11_1360
  <=> m1_subset_1(k1_funct_1(sK2,sK9(sK0,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1360])])).

fof(f179,plain,
    ( spl11_16
  <=> r1_tarski(k2_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).

fof(f11474,plain,
    ( spl11_1336
  <=> ! [X0] :
        ( m1_subset_1(k1_funct_1(sK2,sK9(sK0,sK2)),X0)
        | ~ r1_tarski(k2_relat_1(sK2),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1336])])).

fof(f11848,plain,
    ( m1_subset_1(k1_funct_1(sK2,sK9(sK0,sK2)),sK0)
    | ~ spl11_16
    | ~ spl11_1336 ),
    inference(resolution,[],[f11475,f180])).

fof(f180,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0)
    | ~ spl11_16 ),
    inference(avatar_component_clause,[],[f179])).

fof(f11475,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK2),X0)
        | m1_subset_1(k1_funct_1(sK2,sK9(sK0,sK2)),X0) )
    | ~ spl11_1336 ),
    inference(avatar_component_clause,[],[f11474])).

fof(f11561,plain,
    ( spl11_1362
    | spl11_45
    | ~ spl11_1360 ),
    inference(avatar_split_clause,[],[f11554,f11549,f349,f11559])).

fof(f349,plain,
    ( spl11_45
  <=> ~ v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_45])])).

fof(f11554,plain,
    ( r2_hidden(k1_funct_1(sK2,sK9(sK0,sK2)),sK0)
    | ~ spl11_45
    | ~ spl11_1360 ),
    inference(subsumption_resolution,[],[f11553,f350])).

fof(f350,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl11_45 ),
    inference(avatar_component_clause,[],[f349])).

fof(f11553,plain,
    ( v1_xboole_0(sK0)
    | r2_hidden(k1_funct_1(sK2,sK9(sK0,sK2)),sK0)
    | ~ spl11_1360 ),
    inference(resolution,[],[f11550,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t50_funct_1.p',t2_subset)).

fof(f11550,plain,
    ( m1_subset_1(k1_funct_1(sK2,sK9(sK0,sK2)),sK0)
    | ~ spl11_1360 ),
    inference(avatar_component_clause,[],[f11549])).

fof(f11543,plain,
    ( spl11_1336
    | ~ spl11_500 ),
    inference(avatar_split_clause,[],[f8331,f5107,f11474])).

fof(f5107,plain,
    ( spl11_500
  <=> ! [X0] :
        ( ~ m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(X0))
        | m1_subset_1(k1_funct_1(sK2,sK9(sK0,sK2)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_500])])).

fof(f8331,plain,
    ( ! [X0] :
        ( m1_subset_1(k1_funct_1(sK2,sK9(sK0,sK2)),X0)
        | ~ r1_tarski(k2_relat_1(sK2),X0) )
    | ~ spl11_500 ),
    inference(resolution,[],[f5108,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t50_funct_1.p',t3_subset)).

fof(f5108,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(X0))
        | m1_subset_1(k1_funct_1(sK2,sK9(sK0,sK2)),X0) )
    | ~ spl11_500 ),
    inference(avatar_component_clause,[],[f5107])).

fof(f8371,plain,
    ( spl11_894
    | ~ spl11_42
    | ~ spl11_140 ),
    inference(avatar_split_clause,[],[f957,f947,f331,f8369])).

fof(f947,plain,
    ( spl11_140
  <=> ! [X0] :
        ( k1_funct_1(sK1,X0) = k1_funct_1(sK1,k1_funct_1(sK2,X0))
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_140])])).

fof(f957,plain,
    ( k1_funct_1(sK1,sK9(sK0,sK2)) = k1_funct_1(sK1,k1_funct_1(sK2,sK9(sK0,sK2)))
    | ~ spl11_42
    | ~ spl11_140 ),
    inference(resolution,[],[f948,f332])).

fof(f948,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | k1_funct_1(sK1,X0) = k1_funct_1(sK1,k1_funct_1(sK2,X0)) )
    | ~ spl11_140 ),
    inference(avatar_component_clause,[],[f947])).

fof(f5223,plain,
    ( spl11_500
    | ~ spl11_108 ),
    inference(avatar_split_clause,[],[f4000,f661,f5107])).

fof(f661,plain,
    ( spl11_108
  <=> r2_hidden(k1_funct_1(sK2,sK9(sK0,sK2)),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_108])])).

fof(f4000,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(X0))
        | m1_subset_1(k1_funct_1(sK2,sK9(sK0,sK2)),X0) )
    | ~ spl11_108 ),
    inference(resolution,[],[f662,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t50_funct_1.p',t4_subset)).

fof(f662,plain,
    ( r2_hidden(k1_funct_1(sK2,sK9(sK0,sK2)),k2_relat_1(sK2))
    | ~ spl11_108 ),
    inference(avatar_component_clause,[],[f661])).

fof(f949,plain,
    ( spl11_140
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_20
    | ~ spl11_94 ),
    inference(avatar_split_clause,[],[f612,f565,f193,f130,f123,f947])).

fof(f193,plain,
    ( spl11_20
  <=> k5_relat_1(sK2,sK1) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).

fof(f565,plain,
    ( spl11_94
  <=> ! [X3,X2] :
        ( ~ r2_hidden(X2,sK0)
        | ~ v1_funct_1(X3)
        | ~ v1_relat_1(X3)
        | k1_funct_1(X3,k1_funct_1(sK2,X2)) = k1_funct_1(k5_relat_1(sK2,X3),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_94])])).

fof(f612,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,X0) = k1_funct_1(sK1,k1_funct_1(sK2,X0))
        | ~ r2_hidden(X0,sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_20
    | ~ spl11_94 ),
    inference(forward_demodulation,[],[f611,f194])).

fof(f194,plain,
    ( k5_relat_1(sK2,sK1) = sK1
    | ~ spl11_20 ),
    inference(avatar_component_clause,[],[f193])).

fof(f611,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | k1_funct_1(k5_relat_1(sK2,sK1),X0) = k1_funct_1(sK1,k1_funct_1(sK2,X0)) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_94 ),
    inference(subsumption_resolution,[],[f609,f124])).

fof(f609,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ v1_relat_1(sK1)
        | k1_funct_1(k5_relat_1(sK2,sK1),X0) = k1_funct_1(sK1,k1_funct_1(sK2,X0)) )
    | ~ spl11_2
    | ~ spl11_94 ),
    inference(resolution,[],[f566,f131])).

fof(f566,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_1(X3)
        | ~ r2_hidden(X2,sK0)
        | ~ v1_relat_1(X3)
        | k1_funct_1(X3,k1_funct_1(sK2,X2)) = k1_funct_1(k5_relat_1(sK2,X3),X2) )
    | ~ spl11_94 ),
    inference(avatar_component_clause,[],[f565])).

fof(f663,plain,
    ( spl11_108
    | ~ spl11_42
    | ~ spl11_56 ),
    inference(avatar_split_clause,[],[f434,f388,f331,f661])).

fof(f388,plain,
    ( spl11_56
  <=> ! [X1] :
        ( ~ r2_hidden(X1,sK0)
        | r2_hidden(k1_funct_1(sK2,X1),k2_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_56])])).

fof(f434,plain,
    ( r2_hidden(k1_funct_1(sK2,sK9(sK0,sK2)),k2_relat_1(sK2))
    | ~ spl11_42
    | ~ spl11_56 ),
    inference(resolution,[],[f389,f332])).

fof(f389,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK0)
        | r2_hidden(k1_funct_1(sK2,X1),k2_relat_1(sK2)) )
    | ~ spl11_56 ),
    inference(avatar_component_clause,[],[f388])).

fof(f567,plain,
    ( spl11_94
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_14 ),
    inference(avatar_split_clause,[],[f339,f172,f144,f137,f565])).

fof(f137,plain,
    ( spl11_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f144,plain,
    ( spl11_6
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f172,plain,
    ( spl11_14
  <=> k1_relat_1(sK2) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f339,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,sK0)
        | ~ v1_funct_1(X3)
        | ~ v1_relat_1(X3)
        | k1_funct_1(X3,k1_funct_1(sK2,X2)) = k1_funct_1(k5_relat_1(sK2,X3),X2) )
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_14 ),
    inference(forward_demodulation,[],[f338,f173])).

fof(f173,plain,
    ( k1_relat_1(sK2) = sK0
    | ~ spl11_14 ),
    inference(avatar_component_clause,[],[f172])).

fof(f338,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,k1_relat_1(sK2))
        | ~ v1_funct_1(X3)
        | ~ v1_relat_1(X3)
        | k1_funct_1(X3,k1_funct_1(sK2,X2)) = k1_funct_1(k5_relat_1(sK2,X3),X2) )
    | ~ spl11_4
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f335,f138])).

fof(f138,plain,
    ( v1_relat_1(sK2)
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f137])).

fof(f335,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,k1_relat_1(sK2))
        | ~ v1_funct_1(X3)
        | ~ v1_relat_1(X3)
        | k1_funct_1(X3,k1_funct_1(sK2,X2)) = k1_funct_1(k5_relat_1(sK2,X3),X2)
        | ~ v1_relat_1(sK2) )
    | ~ spl11_6 ),
    inference(resolution,[],[f101,f145])).

fof(f145,plain,
    ( v1_funct_1(sK2)
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f144])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
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
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t50_funct_1.p',t23_funct_1)).

fof(f420,plain,
    ( ~ spl11_65
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_14
    | spl11_19 ),
    inference(avatar_split_clause,[],[f321,f186,f172,f144,f137,f418])).

fof(f186,plain,
    ( spl11_19
  <=> k6_relat_1(sK0) != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).

fof(f321,plain,
    ( k1_funct_1(sK2,sK9(sK0,sK2)) != sK9(sK0,sK2)
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_14
    | ~ spl11_19 ),
    inference(subsumption_resolution,[],[f320,f187])).

fof(f187,plain,
    ( k6_relat_1(sK0) != sK2
    | ~ spl11_19 ),
    inference(avatar_component_clause,[],[f186])).

fof(f320,plain,
    ( k6_relat_1(sK0) = sK2
    | k1_funct_1(sK2,sK9(sK0,sK2)) != sK9(sK0,sK2)
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_14 ),
    inference(forward_demodulation,[],[f319,f173])).

fof(f319,plain,
    ( k1_funct_1(sK2,sK9(sK0,sK2)) != sK9(sK0,sK2)
    | k6_relat_1(k1_relat_1(sK2)) = sK2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_14 ),
    inference(subsumption_resolution,[],[f318,f138])).

fof(f318,plain,
    ( k1_funct_1(sK2,sK9(sK0,sK2)) != sK9(sK0,sK2)
    | k6_relat_1(k1_relat_1(sK2)) = sK2
    | ~ v1_relat_1(sK2)
    | ~ spl11_6
    | ~ spl11_14 ),
    inference(subsumption_resolution,[],[f314,f145])).

fof(f314,plain,
    ( k1_funct_1(sK2,sK9(sK0,sK2)) != sK9(sK0,sK2)
    | k6_relat_1(k1_relat_1(sK2)) = sK2
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl11_14 ),
    inference(superposition,[],[f113,f173])).

fof(f113,plain,(
    ! [X1] :
      ( k1_funct_1(X1,sK9(k1_relat_1(X1),X1)) != sK9(k1_relat_1(X1),X1)
      | k6_relat_1(k1_relat_1(X1)) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | k1_funct_1(X1,sK9(X0,X1)) != sK9(X0,X1)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( k1_funct_1(X1,sK9(X0,X1)) != sK9(X0,X1)
            & r2_hidden(sK9(X0,X1),X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f65,f66])).

fof(f66,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( k1_funct_1(X1,sK9(X0,X1)) != sK9(X0,X1)
        & r2_hidden(sK9(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
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
    inference(rectify,[],[f64])).

fof(f64,plain,(
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
    inference(flattening,[],[f63])).

fof(f63,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t50_funct_1.p',t34_funct_1)).

fof(f390,plain,
    ( spl11_56
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_14 ),
    inference(avatar_split_clause,[],[f260,f172,f144,f137,f388])).

fof(f260,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK0)
        | r2_hidden(k1_funct_1(sK2,X1),k2_relat_1(sK2)) )
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_14 ),
    inference(forward_demodulation,[],[f259,f173])).

fof(f259,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK2))
        | r2_hidden(k1_funct_1(sK2,X1),k2_relat_1(sK2)) )
    | ~ spl11_4
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f256,f138])).

fof(f256,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK2))
        | r2_hidden(k1_funct_1(sK2,X1),k2_relat_1(sK2))
        | ~ v1_relat_1(sK2) )
    | ~ spl11_6 ),
    inference(resolution,[],[f110,f145])).

fof(f110,plain,(
    ! [X6,X0] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f109])).

fof(f109,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK5(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK5(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK6(X0,X1)) = sK5(X0,X1)
                  & r2_hidden(sK6(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK5(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK7(X0,X5)) = X5
                    & r2_hidden(sK7(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f56,f59,f58,f57])).

fof(f57,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK5(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK5(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK6(X0,X1)) = X2
        & r2_hidden(sK6(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK7(X0,X5)) = X5
        & r2_hidden(sK7(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

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
    file('/export/starexec/sandbox/benchmark/funct_1__t50_funct_1.p',d5_funct_1)).

fof(f351,plain,
    ( ~ spl11_45
    | ~ spl11_42 ),
    inference(avatar_split_clause,[],[f342,f331,f349])).

fof(f342,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl11_42 ),
    inference(resolution,[],[f332,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t50_funct_1.p',t7_boole)).

fof(f333,plain,
    ( spl11_42
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_14
    | spl11_19 ),
    inference(avatar_split_clause,[],[f301,f186,f172,f144,f137,f331])).

fof(f301,plain,
    ( r2_hidden(sK9(sK0,sK2),sK0)
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_14
    | ~ spl11_19 ),
    inference(subsumption_resolution,[],[f300,f187])).

fof(f300,plain,
    ( k6_relat_1(sK0) = sK2
    | r2_hidden(sK9(sK0,sK2),sK0)
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_14 ),
    inference(forward_demodulation,[],[f299,f173])).

fof(f299,plain,
    ( r2_hidden(sK9(sK0,sK2),sK0)
    | k6_relat_1(k1_relat_1(sK2)) = sK2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_14 ),
    inference(forward_demodulation,[],[f298,f173])).

fof(f298,plain,
    ( r2_hidden(sK9(k1_relat_1(sK2),sK2),k1_relat_1(sK2))
    | k6_relat_1(k1_relat_1(sK2)) = sK2
    | ~ spl11_4
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f294,f138])).

fof(f294,plain,
    ( r2_hidden(sK9(k1_relat_1(sK2),sK2),k1_relat_1(sK2))
    | k6_relat_1(k1_relat_1(sK2)) = sK2
    | ~ v1_relat_1(sK2)
    | ~ spl11_6 ),
    inference(resolution,[],[f114,f145])).

fof(f114,plain,(
    ! [X1] :
      ( ~ v1_funct_1(X1)
      | r2_hidden(sK9(k1_relat_1(X1),X1),k1_relat_1(X1))
      | k6_relat_1(k1_relat_1(X1)) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | r2_hidden(sK9(X0,X1),X0)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f195,plain,(
    spl11_20 ),
    inference(avatar_split_clause,[],[f77,f193])).

fof(f77,plain,(
    k5_relat_1(sK2,sK1) = sK1 ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,
    ( k6_relat_1(sK0) != sK2
    & k5_relat_1(sK2,sK1) = sK1
    & v2_funct_1(sK1)
    & r1_tarski(k2_relat_1(sK2),sK0)
    & k1_relat_1(sK2) = sK0
    & k1_relat_1(sK1) = sK0
    & v1_funct_1(sK2)
    & v1_relat_1(sK2)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f49,f48])).

fof(f48,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k6_relat_1(X0) != X2
            & k5_relat_1(X2,X1) = X1
            & v2_funct_1(X1)
            & r1_tarski(k2_relat_1(X2),X0)
            & k1_relat_1(X2) = X0
            & k1_relat_1(X1) = X0
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( k6_relat_1(sK0) != X2
          & k5_relat_1(X2,sK1) = sK1
          & v2_funct_1(sK1)
          & r1_tarski(k2_relat_1(X2),sK0)
          & k1_relat_1(X2) = sK0
          & k1_relat_1(sK1) = sK0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k6_relat_1(X0) != X2
          & k5_relat_1(X2,X1) = X1
          & v2_funct_1(X1)
          & r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X0
          & k1_relat_1(X1) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( k6_relat_1(X0) != sK2
        & k5_relat_1(sK2,X1) = X1
        & v2_funct_1(X1)
        & r1_tarski(k2_relat_1(sK2),X0)
        & k1_relat_1(sK2) = X0
        & k1_relat_1(X1) = X0
        & v1_funct_1(sK2)
        & v1_relat_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k6_relat_1(X0) != X2
          & k5_relat_1(X2,X1) = X1
          & v2_funct_1(X1)
          & r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X0
          & k1_relat_1(X1) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k6_relat_1(X0) != X2
          & k5_relat_1(X2,X1) = X1
          & v2_funct_1(X1)
          & r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X0
          & k1_relat_1(X1) = X0
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
           => ( ( k5_relat_1(X2,X1) = X1
                & v2_funct_1(X1)
                & r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X0
                & k1_relat_1(X1) = X0 )
             => k6_relat_1(X0) = X2 ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( ( k5_relat_1(X2,X1) = X1
              & v2_funct_1(X1)
              & r1_tarski(k2_relat_1(X2),X0)
              & k1_relat_1(X2) = X0
              & k1_relat_1(X1) = X0 )
           => k6_relat_1(X0) = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t50_funct_1.p',t50_funct_1)).

fof(f188,plain,(
    ~ spl11_19 ),
    inference(avatar_split_clause,[],[f78,f186])).

fof(f78,plain,(
    k6_relat_1(sK0) != sK2 ),
    inference(cnf_transformation,[],[f50])).

fof(f181,plain,(
    spl11_16 ),
    inference(avatar_split_clause,[],[f75,f179])).

fof(f75,plain,(
    r1_tarski(k2_relat_1(sK2),sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f174,plain,(
    spl11_14 ),
    inference(avatar_split_clause,[],[f74,f172])).

fof(f74,plain,(
    k1_relat_1(sK2) = sK0 ),
    inference(cnf_transformation,[],[f50])).

fof(f167,plain,(
    spl11_12 ),
    inference(avatar_split_clause,[],[f73,f165])).

fof(f73,plain,(
    k1_relat_1(sK1) = sK0 ),
    inference(cnf_transformation,[],[f50])).

fof(f153,plain,(
    spl11_8 ),
    inference(avatar_split_clause,[],[f76,f151])).

fof(f76,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f146,plain,(
    spl11_6 ),
    inference(avatar_split_clause,[],[f72,f144])).

fof(f72,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f139,plain,(
    spl11_4 ),
    inference(avatar_split_clause,[],[f71,f137])).

fof(f71,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f132,plain,(
    spl11_2 ),
    inference(avatar_split_clause,[],[f70,f130])).

fof(f70,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f125,plain,(
    spl11_0 ),
    inference(avatar_split_clause,[],[f69,f123])).

fof(f69,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f50])).
%------------------------------------------------------------------------------
