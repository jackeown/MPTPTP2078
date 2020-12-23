%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t173_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:20 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 227 expanded)
%              Number of leaves         :   32 (  94 expanded)
%              Depth                    :   11
%              Number of atoms          :  380 ( 899 expanded)
%              Number of equality atoms :   21 (  85 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f249,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f77,f84,f91,f98,f105,f112,f119,f129,f159,f166,f179,f201,f208,f217,f225,f238,f245])).

fof(f245,plain,
    ( ~ spl5_0
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_18
    | ~ spl5_28 ),
    inference(avatar_contradiction_clause,[],[f244])).

fof(f244,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_18
    | ~ spl5_28 ),
    inference(subsumption_resolution,[],[f243,f130])).

fof(f130,plain,
    ( ! [X0] : ~ r2_hidden(X0,o_0_0_xboole_0)
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f104,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t173_funct_1.p',t7_boole)).

fof(f104,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl5_10
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f243,plain,
    ( r2_hidden(k1_funct_1(sK0,sK2(sK1)),o_0_0_xboole_0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_12
    | ~ spl5_18
    | ~ spl5_28 ),
    inference(forward_demodulation,[],[f239,f216])).

fof(f216,plain,
    ( k1_funct_1(sK1,sK2(sK1)) = o_0_0_xboole_0
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f215])).

fof(f215,plain,
    ( spl5_28
  <=> k1_funct_1(sK1,sK2(sK1)) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f239,plain,
    ( r2_hidden(k1_funct_1(sK0,sK2(sK1)),k1_funct_1(sK1,sK2(sK1)))
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_12
    | ~ spl5_18 ),
    inference(unit_resulting_resolution,[],[f83,f90,f69,f76,f111,f158,f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r2_hidden(X3,k1_relat_1(X1))
      | ~ v5_funct_1(X1,X0)
      | r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ( ~ r2_hidden(k1_funct_1(X1,sK3(X0,X1)),k1_funct_1(X0,sK3(X0,X1)))
                & r2_hidden(sK3(X0,X1),k1_relat_1(X1)) ) )
            & ( ! [X3] :
                  ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
          & r2_hidden(X2,k1_relat_1(X1)) )
     => ( ~ r2_hidden(k1_funct_1(X1,sK3(X0,X1)),k1_funct_1(X0,sK3(X0,X1)))
        & r2_hidden(sK3(X0,X1),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  & r2_hidden(X2,k1_relat_1(X1)) ) )
            & ( ! [X3] :
                  ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  & r2_hidden(X2,k1_relat_1(X1)) ) )
            & ( ! [X2] :
                  ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  | ~ r2_hidden(X2,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(X2,k1_relat_1(X1))
               => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t173_funct_1.p',d20_funct_1)).

fof(f158,plain,
    ( r2_hidden(sK2(sK1),k1_relat_1(sK0))
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl5_18
  <=> r2_hidden(sK2(sK1),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f111,plain,
    ( v5_funct_1(sK0,sK1)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl5_12
  <=> v5_funct_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f76,plain,
    ( v1_funct_1(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl5_2
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f69,plain,
    ( v1_relat_1(sK0)
    | ~ spl5_0 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl5_0
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f90,plain,
    ( v1_funct_1(sK1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl5_6
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f83,plain,
    ( v1_relat_1(sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl5_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f238,plain,
    ( ~ spl5_33
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f228,f223,f236])).

fof(f236,plain,
    ( spl5_33
  <=> ~ r2_hidden(k1_relat_1(sK0),sK4(k1_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f223,plain,
    ( spl5_30
  <=> r2_hidden(sK4(k1_relat_1(sK0)),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f228,plain,
    ( ~ r2_hidden(k1_relat_1(sK0),sK4(k1_relat_1(sK0)))
    | ~ spl5_30 ),
    inference(unit_resulting_resolution,[],[f224,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t173_funct_1.p',antisymmetry_r2_hidden)).

fof(f224,plain,
    ( r2_hidden(sK4(k1_relat_1(sK0)),k1_relat_1(sK0))
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f223])).

fof(f225,plain,
    ( spl5_30
    | spl5_23 ),
    inference(avatar_split_clause,[],[f180,f177,f223])).

fof(f177,plain,
    ( spl5_23
  <=> ~ v1_xboole_0(k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f180,plain,
    ( r2_hidden(sK4(k1_relat_1(sK0)),k1_relat_1(sK0))
    | ~ spl5_23 ),
    inference(unit_resulting_resolution,[],[f58,f178,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t173_funct_1.p',t2_subset)).

fof(f178,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK0))
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f177])).

fof(f58,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f11,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f11,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t173_funct_1.p',existence_m1_subset_1)).

fof(f217,plain,
    ( spl5_28
    | ~ spl5_10
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f187,f164,f103,f215])).

fof(f164,plain,
    ( spl5_20
  <=> v1_xboole_0(k1_funct_1(sK1,sK2(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f187,plain,
    ( k1_funct_1(sK1,sK2(sK1)) = o_0_0_xboole_0
    | ~ spl5_10
    | ~ spl5_20 ),
    inference(unit_resulting_resolution,[],[f165,f122])).

fof(f122,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl5_10 ),
    inference(backward_demodulation,[],[f120,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t173_funct_1.p',t6_boole)).

fof(f120,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f104,f51])).

fof(f165,plain,
    ( v1_xboole_0(k1_funct_1(sK1,sK2(sK1)))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f164])).

fof(f208,plain,
    ( ~ spl5_27
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f169,f157,f206])).

fof(f206,plain,
    ( spl5_27
  <=> ~ r2_hidden(k1_relat_1(sK0),sK2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f169,plain,
    ( ~ r2_hidden(k1_relat_1(sK0),sK2(sK1))
    | ~ spl5_18 ),
    inference(unit_resulting_resolution,[],[f158,f59])).

fof(f201,plain,
    ( spl5_24
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f167,f157,f199])).

fof(f199,plain,
    ( spl5_24
  <=> m1_subset_1(sK2(sK1),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f167,plain,
    ( m1_subset_1(sK2(sK1),k1_relat_1(sK0))
    | ~ spl5_18 ),
    inference(unit_resulting_resolution,[],[f158,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t173_funct_1.p',t1_subset)).

fof(f179,plain,
    ( ~ spl5_23
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f170,f157,f177])).

fof(f170,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK0))
    | ~ spl5_18 ),
    inference(unit_resulting_resolution,[],[f158,f63])).

fof(f166,plain,
    ( spl5_20
    | ~ spl5_4
    | ~ spl5_6
    | spl5_9 ),
    inference(avatar_split_clause,[],[f151,f96,f89,f82,f164])).

fof(f96,plain,
    ( spl5_9
  <=> ~ v2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f151,plain,
    ( v1_xboole_0(k1_funct_1(sK1,sK2(sK1)))
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_9 ),
    inference(unit_resulting_resolution,[],[f83,f90,f97,f54])).

fof(f54,plain,(
    ! [X0] :
      ( v2_relat_1(X0)
      | v1_xboole_0(k1_funct_1(X0,sK2(X0)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( ( v2_relat_1(X0)
          | ( v1_xboole_0(k1_funct_1(X0,sK2(X0)))
            & r2_hidden(sK2(X0),k1_relat_1(X0)) ) )
        & ( ! [X2] :
              ( ~ v1_xboole_0(k1_funct_1(X0,X2))
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          | ~ v2_relat_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(k1_funct_1(X0,X1))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( v1_xboole_0(k1_funct_1(X0,sK2(X0)))
        & r2_hidden(sK2(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ( ( v2_relat_1(X0)
          | ? [X1] :
              ( v1_xboole_0(k1_funct_1(X0,X1))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X2] :
              ( ~ v1_xboole_0(k1_funct_1(X0,X2))
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          | ~ v2_relat_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( ( v2_relat_1(X0)
          | ? [X1] :
              ( v1_xboole_0(k1_funct_1(X0,X1))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X1] :
              ( ~ v1_xboole_0(k1_funct_1(X0,X1))
              | ~ r2_hidden(X1,k1_relat_1(X0)) )
          | ~ v2_relat_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v2_relat_1(X0)
      <=> ! [X1] :
            ( ~ v1_xboole_0(k1_funct_1(X0,X1))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v2_relat_1(X0)
      <=> ! [X1] :
            ( ~ v1_xboole_0(k1_funct_1(X0,X1))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_relat_1(X0)
      <=> ! [X1] :
            ~ ( v1_xboole_0(k1_funct_1(X0,X1))
              & r2_hidden(X1,k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t173_funct_1.p',d15_funct_1)).

fof(f97,plain,
    ( ~ v2_relat_1(sK1)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f96])).

fof(f159,plain,
    ( spl5_18
    | ~ spl5_4
    | ~ spl5_6
    | spl5_9
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f147,f117,f96,f89,f82,f157])).

fof(f117,plain,
    ( spl5_14
  <=> k1_relat_1(sK0) = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f147,plain,
    ( r2_hidden(sK2(sK1),k1_relat_1(sK0))
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f145,f118])).

fof(f118,plain,
    ( k1_relat_1(sK0) = k1_relat_1(sK1)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f117])).

fof(f145,plain,
    ( r2_hidden(sK2(sK1),k1_relat_1(sK1))
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_9 ),
    inference(unit_resulting_resolution,[],[f83,f90,f97,f53])).

fof(f53,plain,(
    ! [X0] :
      ( v2_relat_1(X0)
      | r2_hidden(sK2(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f129,plain,
    ( spl5_16
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f120,f103,f127])).

fof(f127,plain,
    ( spl5_16
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f119,plain,(
    spl5_14 ),
    inference(avatar_split_clause,[],[f48,f117])).

fof(f48,plain,(
    k1_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ~ v2_relat_1(sK1)
    & k1_relat_1(sK0) = k1_relat_1(sK1)
    & v5_funct_1(sK0,sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f31,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_relat_1(X1)
            & k1_relat_1(X0) = k1_relat_1(X1)
            & v5_funct_1(X0,X1)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ v2_relat_1(X1)
          & k1_relat_1(sK0) = k1_relat_1(X1)
          & v5_funct_1(sK0,X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_relat_1(X1)
          & k1_relat_1(X0) = k1_relat_1(X1)
          & v5_funct_1(X0,X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ~ v2_relat_1(sK1)
        & k1_relat_1(sK1) = k1_relat_1(X0)
        & v5_funct_1(X0,sK1)
        & v1_funct_1(sK1)
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_relat_1(X1)
          & k1_relat_1(X0) = k1_relat_1(X1)
          & v5_funct_1(X0,X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_relat_1(X1)
          & k1_relat_1(X0) = k1_relat_1(X1)
          & v5_funct_1(X0,X1)
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
           => ( ( k1_relat_1(X0) = k1_relat_1(X1)
                & v5_funct_1(X0,X1) )
             => v2_relat_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k1_relat_1(X0) = k1_relat_1(X1)
              & v5_funct_1(X0,X1) )
           => v2_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t173_funct_1.p',t173_funct_1)).

fof(f112,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f47,f110])).

fof(f47,plain,(
    v5_funct_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f105,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f50,f103])).

fof(f50,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t173_funct_1.p',dt_o_0_0_xboole_0)).

fof(f98,plain,(
    ~ spl5_9 ),
    inference(avatar_split_clause,[],[f49,f96])).

fof(f49,plain,(
    ~ v2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f91,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f46,f89])).

fof(f46,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f84,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f45,f82])).

fof(f45,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f77,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f44,f75])).

fof(f44,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f70,plain,(
    spl5_0 ),
    inference(avatar_split_clause,[],[f43,f68])).

fof(f43,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
