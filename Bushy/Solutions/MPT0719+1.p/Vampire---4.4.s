%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t174_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:20 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 163 expanded)
%              Number of leaves         :   23 (  61 expanded)
%              Depth                    :   15
%              Number of atoms          :  277 ( 486 expanded)
%              Number of equality atoms :    8 (  14 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f197,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f73,f80,f87,f94,f103,f110,f119,f126,f140,f150,f169,f189,f196])).

fof(f196,plain,
    ( ~ spl3_0
    | ~ spl3_2
    | ~ spl3_4
    | spl3_9
    | ~ spl3_10
    | ~ spl3_14
    | ~ spl3_22 ),
    inference(avatar_contradiction_clause,[],[f195])).

fof(f195,plain,
    ( $false
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_14
    | ~ spl3_22 ),
    inference(subsumption_resolution,[],[f194,f143])).

fof(f143,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f79,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t174_funct_1.p',t7_boole)).

fof(f79,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl3_4
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f194,plain,
    ( r2_hidden(sK1(sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_14
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f193,f168])).

fof(f168,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl3_22
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f193,plain,
    ( r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f192,f65])).

fof(f65,plain,
    ( v1_relat_1(sK0)
    | ~ spl3_0 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl3_0
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_0])])).

fof(f192,plain,
    ( r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(sK0)
    | ~ spl3_2
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f191,f72])).

fof(f72,plain,
    ( v1_funct_1(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl3_2
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f191,plain,
    ( r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f190,f118])).

fof(f118,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl3_14
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f190,plain,
    ( r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f186,f102])).

fof(f102,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl3_10
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f186,plain,
    ( r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl3_9 ),
    inference(resolution,[],[f52,f93])).

fof(f93,plain,
    ( ~ v5_funct_1(k1_xboole_0,sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl3_9
  <=> ~ v5_funct_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v5_funct_1(X1,X0)
      | r2_hidden(sK1(X0,X1),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ( ~ r2_hidden(k1_funct_1(X1,sK1(X0,X1)),k1_funct_1(X0,sK1(X0,X1)))
                & r2_hidden(sK1(X0,X1),k1_relat_1(X1)) ) )
            & ( ! [X3] :
                  ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
          & r2_hidden(X2,k1_relat_1(X1)) )
     => ( ~ r2_hidden(k1_funct_1(X1,sK1(X0,X1)),k1_funct_1(X0,sK1(X0,X1)))
        & r2_hidden(sK1(X0,X1),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/funct_1__t174_funct_1.p',d20_funct_1)).

fof(f189,plain,
    ( ~ spl3_0
    | ~ spl3_2
    | ~ spl3_4
    | spl3_9
    | ~ spl3_10
    | ~ spl3_14
    | ~ spl3_22 ),
    inference(avatar_contradiction_clause,[],[f188])).

fof(f188,plain,
    ( $false
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_14
    | ~ spl3_22 ),
    inference(subsumption_resolution,[],[f187,f143])).

fof(f187,plain,
    ( r2_hidden(sK1(sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_14
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f185,f168])).

fof(f185,plain,
    ( r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_14 ),
    inference(unit_resulting_resolution,[],[f65,f72,f118,f102,f93,f52])).

fof(f169,plain,
    ( spl3_22
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f153,f148,f167])).

fof(f148,plain,
    ( spl3_20
  <=> v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f153,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl3_20 ),
    inference(unit_resulting_resolution,[],[f149,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t174_funct_1.p',t6_boole)).

fof(f149,plain,
    ( v1_xboole_0(k1_relat_1(k1_xboole_0))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f148])).

fof(f150,plain,
    ( spl3_20
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f141,f78,f148])).

fof(f141,plain,
    ( v1_xboole_0(k1_relat_1(k1_xboole_0))
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f79,f50])).

fof(f50,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t174_funct_1.p',fc10_relat_1)).

fof(f140,plain,
    ( spl3_18
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f128,f85,f138])).

fof(f138,plain,
    ( spl3_18
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f85,plain,
    ( spl3_6
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f128,plain,
    ( k1_xboole_0 = o_0_0_xboole_0
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f86,f49])).

fof(f86,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f85])).

fof(f126,plain,
    ( spl3_16
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f112,f85,f124])).

fof(f124,plain,
    ( spl3_16
  <=> v1_relat_1(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f112,plain,
    ( v1_relat_1(o_0_0_xboole_0)
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f86,f48])).

fof(f48,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t174_funct_1.p',cc1_relat_1)).

fof(f119,plain,
    ( spl3_14
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f111,f78,f117])).

fof(f111,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f79,f48])).

fof(f110,plain,
    ( spl3_12
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f96,f85,f108])).

fof(f108,plain,
    ( spl3_12
  <=> v1_funct_1(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f96,plain,
    ( v1_funct_1(o_0_0_xboole_0)
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f86,f47])).

fof(f47,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t174_funct_1.p',cc1_funct_1)).

fof(f103,plain,
    ( spl3_10
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f95,f78,f101])).

fof(f95,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f79,f47])).

fof(f94,plain,(
    ~ spl3_9 ),
    inference(avatar_split_clause,[],[f44,f92])).

fof(f44,plain,(
    ~ v5_funct_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ~ v5_funct_1(k1_xboole_0,sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( ~ v5_funct_1(k1_xboole_0,X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ~ v5_funct_1(k1_xboole_0,sK0)
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( ~ v5_funct_1(k1_xboole_0,X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ~ v5_funct_1(k1_xboole_0,X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => v5_funct_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => v5_funct_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t174_funct_1.p',t174_funct_1)).

fof(f87,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f46,f85])).

fof(f46,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t174_funct_1.p',dt_o_0_0_xboole_0)).

fof(f80,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f45,f78])).

fof(f45,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t174_funct_1.p',fc1_xboole_0)).

fof(f73,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f43,f71])).

fof(f43,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f66,plain,(
    spl3_0 ),
    inference(avatar_split_clause,[],[f42,f64])).

fof(f42,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
