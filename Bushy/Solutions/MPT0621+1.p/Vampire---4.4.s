%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t16_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:19 EDT 2019

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 265 expanded)
%              Number of leaves         :   28 ( 110 expanded)
%              Depth                    :    8
%              Number of atoms          :  292 ( 922 expanded)
%              Number of equality atoms :   88 ( 320 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f147,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f73,f74,f75,f81,f85,f93,f94,f107,f112,f116,f117,f127,f132,f136,f137,f142,f146])).

fof(f146,plain,(
    ~ spl4_22 ),
    inference(avatar_contradiction_clause,[],[f145])).

fof(f145,plain,
    ( $false
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f144,f42])).

fof(f42,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t16_funct_1.p',dt_o_0_0_xboole_0)).

fof(f144,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl4_22 ),
    inference(backward_demodulation,[],[f141,f41])).

fof(f41,plain,(
    ~ v1_xboole_0(np__1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ~ v1_xboole_0(np__1) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t16_funct_1.p',spc1_boole)).

fof(f141,plain,
    ( o_0_0_xboole_0 = np__1
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl4_22
  <=> o_0_0_xboole_0 = np__1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f142,plain,
    ( spl4_22
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f138,f110,f105,f140])).

fof(f105,plain,
    ( spl4_10
  <=> o_0_0_xboole_0 = k1_funct_1(sK2(sK0),sK1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f110,plain,
    ( spl4_12
  <=> k1_funct_1(sK2(sK0),sK1(sK0)) = np__1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f138,plain,
    ( o_0_0_xboole_0 = np__1
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f111,f106])).

fof(f106,plain,
    ( o_0_0_xboole_0 = k1_funct_1(sK2(sK0),sK1(sK0))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f105])).

fof(f111,plain,
    ( k1_funct_1(sK2(sK0),sK1(sK0)) = np__1
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f110])).

fof(f137,plain,
    ( ~ spl4_21
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f120,f83,f134])).

fof(f134,plain,
    ( spl4_21
  <=> ~ r2_hidden(sK0,o_1_0_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f83,plain,
    ( spl4_6
  <=> r2_hidden(o_1_0_funct_1(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f120,plain,
    ( ~ r2_hidden(sK0,o_1_0_funct_1(sK0))
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f84,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t16_funct_1.p',antisymmetry_r2_hidden)).

fof(f84,plain,
    ( r2_hidden(o_1_0_funct_1(sK0),sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f83])).

fof(f136,plain,
    ( ~ spl4_21
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f121,f83,f134])).

fof(f121,plain,
    ( ~ r2_hidden(sK0,o_1_0_funct_1(sK0))
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f84,f55])).

fof(f132,plain,
    ( spl4_18
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f128,f91,f83,f130])).

fof(f130,plain,
    ( spl4_18
  <=> k1_funct_1(sK2(sK0),o_1_0_funct_1(sK0)) = np__1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f91,plain,
    ( spl4_8
  <=> sK2(sK0) = sK3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f128,plain,
    ( k1_funct_1(sK2(sK0),o_1_0_funct_1(sK0)) = np__1
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f122,f92])).

fof(f92,plain,
    ( sK2(sK0) = sK3(sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f91])).

fof(f122,plain,
    ( k1_funct_1(sK3(sK0),o_1_0_funct_1(sK0)) = np__1
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f84,f54])).

fof(f54,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | k1_funct_1(sK3(X0),X2) = np__1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_funct_1(sK3(X0),X2) = np__1
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK3(X0)) = X0
      & v1_funct_1(sK3(X0))
      & v1_relat_1(sK3(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_funct_1(X1,X2) = np__1
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_funct_1(sK3(X0),X2) = np__1
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK3(X0)) = X0
        & v1_funct_1(sK3(X0))
        & v1_relat_1(sK3(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = np__1
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_funct_1(X1,X2) = np__1 )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t16_funct_1.p',s3_funct_1__e7_25__funct_1)).

fof(f127,plain,
    ( spl4_16
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f123,f83,f125])).

fof(f125,plain,
    ( spl4_16
  <=> o_0_0_xboole_0 = k1_funct_1(sK2(sK0),o_1_0_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f123,plain,
    ( o_0_0_xboole_0 = k1_funct_1(sK2(sK0),o_1_0_funct_1(sK0))
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f84,f62])).

fof(f62,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | o_0_0_xboole_0 = k1_funct_1(sK2(X0),X2) ) ),
    inference(definition_unfolding,[],[f50,f43])).

fof(f43,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/funct_1__t16_funct_1.p',d2_xboole_0)).

fof(f50,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = k1_funct_1(sK2(X0),X2)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(sK2(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK2(X0)) = X0
      & v1_funct_1(sK2(X0))
      & v1_relat_1(sK2(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_xboole_0 = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_xboole_0 = k1_funct_1(sK2(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK2(X0)) = X0
        & v1_funct_1(sK2(X0))
        & v1_relat_1(sK2(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t16_funct_1.p',s3_funct_1__e2_25__funct_1)).

fof(f117,plain,
    ( ~ spl4_15
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f100,f79,f114])).

fof(f114,plain,
    ( spl4_15
  <=> ~ r2_hidden(sK0,sK1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f79,plain,
    ( spl4_4
  <=> r2_hidden(sK1(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f100,plain,
    ( ~ r2_hidden(sK0,sK1(sK0))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f80,f55])).

fof(f80,plain,
    ( r2_hidden(sK1(sK0),sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f116,plain,
    ( ~ spl4_15
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f101,f79,f114])).

fof(f101,plain,
    ( ~ r2_hidden(sK0,sK1(sK0))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f80,f55])).

fof(f112,plain,
    ( spl4_12
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f108,f91,f79,f110])).

fof(f108,plain,
    ( k1_funct_1(sK2(sK0),sK1(sK0)) = np__1
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f102,f92])).

fof(f102,plain,
    ( k1_funct_1(sK3(sK0),sK1(sK0)) = np__1
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f80,f54])).

fof(f107,plain,
    ( spl4_10
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f103,f79,f105])).

fof(f103,plain,
    ( o_0_0_xboole_0 = k1_funct_1(sK2(sK0),sK1(sK0))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f80,f62])).

fof(f94,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f87,f91])).

fof(f87,plain,(
    sK2(sK0) = sK3(sK0) ),
    inference(unit_resulting_resolution,[],[f51,f52,f47,f53,f48,f49,f39])).

fof(f39,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(X2)
      | k1_relat_1(X2) != sK0
      | k1_relat_1(X1) != sK0
      | X1 = X2
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( k1_xboole_0 != sK0
    & ! [X1] :
        ( ! [X2] :
            ( X1 = X2
            | k1_relat_1(X2) != sK0
            | k1_relat_1(X1) != sK0
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f31])).

fof(f31,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | k1_relat_1(X2) != X0
                | k1_relat_1(X1) != X0
                | ~ v1_funct_1(X2)
                | ~ v1_relat_1(X2) )
            | ~ v1_funct_1(X1)
            | ~ v1_relat_1(X1) ) )
   => ( k1_xboole_0 != sK0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != sK0
              | k1_relat_1(X1) != sK0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( k1_relat_1(X2) = X0
                    & k1_relat_1(X1) = X0 )
                 => X1 = X2 ) ) )
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( ( k1_relat_1(X2) = X0
                  & k1_relat_1(X1) = X0 )
               => X1 = X2 ) ) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t16_funct_1.p',t16_funct_1)).

fof(f49,plain,(
    ! [X0] : k1_relat_1(sK2(X0)) = X0 ),
    inference(cnf_transformation,[],[f36])).

fof(f48,plain,(
    ! [X0] : v1_funct_1(sK2(X0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f53,plain,(
    ! [X0] : k1_relat_1(sK3(X0)) = X0 ),
    inference(cnf_transformation,[],[f38])).

fof(f47,plain,(
    ! [X0] : v1_relat_1(sK2(X0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f52,plain,(
    ! [X0] : v1_funct_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f51,plain,(
    ! [X0] : v1_relat_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f93,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f88,f91])).

fof(f88,plain,(
    sK2(sK0) = sK3(sK0) ),
    inference(unit_resulting_resolution,[],[f47,f48,f51,f49,f52,f53,f39])).

fof(f85,plain,
    ( spl4_6
    | spl4_3 ),
    inference(avatar_split_clause,[],[f76,f71,f83])).

fof(f71,plain,
    ( spl4_3
  <=> ~ v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f76,plain,
    ( r2_hidden(o_1_0_funct_1(sK0),sK0)
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f44,f72,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox/benchmark/funct_1__t16_funct_1.p',t2_subset)).

fof(f72,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f44,plain,(
    ! [X0] : m1_subset_1(o_1_0_funct_1(X0),X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(o_1_0_funct_1(X0),X0) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t16_funct_1.p',dt_o_1_0_funct_1)).

fof(f81,plain,
    ( spl4_4
    | spl4_3 ),
    inference(avatar_split_clause,[],[f77,f71,f79])).

fof(f77,plain,
    ( r2_hidden(sK1(sK0),sK0)
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f46,f72,f57])).

fof(f46,plain,(
    ! [X0] : m1_subset_1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] : m1_subset_1(sK1(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f11,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f11,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t16_funct_1.p',existence_m1_subset_1)).

fof(f75,plain,
    ( ~ spl4_3
    | spl4_1 ),
    inference(avatar_split_clause,[],[f67,f64,f71])).

fof(f64,plain,
    ( spl4_1
  <=> o_0_0_xboole_0 != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f67,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl4_1 ),
    inference(unit_resulting_resolution,[],[f65,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f45,f43])).

fof(f45,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t16_funct_1.p',t6_boole)).

fof(f65,plain,
    ( o_0_0_xboole_0 != sK0
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f74,plain,
    ( ~ spl4_3
    | spl4_1 ),
    inference(avatar_split_clause,[],[f68,f64,f71])).

fof(f68,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl4_1 ),
    inference(unit_resulting_resolution,[],[f42,f65,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t16_funct_1.p',t8_boole)).

fof(f73,plain,
    ( ~ spl4_3
    | spl4_1 ),
    inference(avatar_split_clause,[],[f69,f64,f71])).

fof(f69,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl4_1 ),
    inference(unit_resulting_resolution,[],[f42,f65,f58])).

fof(f66,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f60,f64])).

fof(f60,plain,(
    o_0_0_xboole_0 != sK0 ),
    inference(definition_unfolding,[],[f40,f43])).

fof(f40,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
