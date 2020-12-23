%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t56_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:25 EDT 2019

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 142 expanded)
%              Number of leaves         :   21 (  50 expanded)
%              Depth                    :   12
%              Number of atoms          :  341 ( 515 expanded)
%              Number of equality atoms :   57 (  92 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f239,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f91,f98,f105,f112,f125,f134,f142,f190,f217,f222,f237])).

fof(f237,plain,
    ( ~ spl4_0
    | ~ spl4_2
    | ~ spl4_6
    | spl4_11
    | ~ spl4_12
    | ~ spl4_18
    | ~ spl4_20 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_2
    | ~ spl4_6
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_18
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f235,f118])).

fof(f118,plain,
    ( k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0) != sK0
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl4_11
  <=> k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0) != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f235,plain,
    ( k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0) = sK0
    | ~ spl4_0
    | ~ spl4_2
    | ~ spl4_6
    | ~ spl4_12
    | ~ spl4_18
    | ~ spl4_20 ),
    inference(forward_demodulation,[],[f234,f121])).

fof(f121,plain,
    ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) = sK0
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl4_12
  <=> k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f234,plain,
    ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) = k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0)
    | ~ spl4_0
    | ~ spl4_2
    | ~ spl4_6
    | ~ spl4_18
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f230,f186])).

fof(f186,plain,
    ( v1_relat_1(k2_funct_1(sK1))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl4_20
  <=> v1_relat_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f230,plain,
    ( ~ v1_relat_1(k2_funct_1(sK1))
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) = k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0)
    | ~ spl4_0
    | ~ spl4_2
    | ~ spl4_6
    | ~ spl4_18 ),
    inference(resolution,[],[f154,f180])).

fof(f180,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl4_18
  <=> v1_funct_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f154,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k1_funct_1(X0,k1_funct_1(sK1,sK0)) = k1_funct_1(k5_relat_1(sK1,X0),sK0) )
    | ~ spl4_0
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f153,f83])).

fof(f83,plain,
    ( v1_relat_1(sK1)
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl4_0
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f153,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(sK1)
        | k1_funct_1(X0,k1_funct_1(sK1,sK0)) = k1_funct_1(k5_relat_1(sK1,X0),sK0) )
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f152,f90])).

fof(f90,plain,
    ( v1_funct_1(sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl4_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f152,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK1)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(sK1)
        | k1_funct_1(X0,k1_funct_1(sK1,sK0)) = k1_funct_1(k5_relat_1(sK1,X0),sK0) )
    | ~ spl4_6 ),
    inference(resolution,[],[f47,f104])).

fof(f104,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl4_6
  <=> r2_hidden(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X1)
      | k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox/benchmark/funct_1__t56_funct_1.p',t23_funct_1)).

fof(f222,plain,
    ( ~ spl4_0
    | ~ spl4_2
    | spl4_21 ),
    inference(avatar_contradiction_clause,[],[f221])).

fof(f221,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_2
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f220,f83])).

fof(f220,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl4_2
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f219,f90])).

fof(f219,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl4_21 ),
    inference(resolution,[],[f189,f63])).

fof(f63,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t56_funct_1.p',dt_k2_funct_1)).

fof(f189,plain,
    ( ~ v1_relat_1(k2_funct_1(sK1))
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl4_21
  <=> ~ v1_relat_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f217,plain,
    ( ~ spl4_0
    | ~ spl4_2
    | spl4_19 ),
    inference(avatar_contradiction_clause,[],[f216])).

fof(f216,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_2
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f215,f83])).

fof(f215,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl4_2
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f214,f90])).

fof(f214,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl4_19 ),
    inference(resolution,[],[f183,f64])).

fof(f64,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f183,plain,
    ( ~ v1_funct_1(k2_funct_1(sK1))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl4_19
  <=> ~ v1_funct_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f190,plain,
    ( ~ spl4_19
    | ~ spl4_21
    | ~ spl4_0
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | spl4_13 ),
    inference(avatar_split_clause,[],[f175,f123,f103,f96,f89,f82,f188,f182])).

fof(f96,plain,
    ( spl4_4
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f123,plain,
    ( spl4_13
  <=> k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f175,plain,
    ( ~ v1_relat_1(k2_funct_1(sK1))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ spl4_0
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f174,f124])).

fof(f124,plain,
    ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) != sK0
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f123])).

fof(f174,plain,
    ( ~ v1_relat_1(k2_funct_1(sK1))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) = sK0
    | ~ spl4_0
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f173,f83])).

fof(f173,plain,
    ( ~ v1_relat_1(k2_funct_1(sK1))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(sK1)
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) = sK0
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f172,f97])).

fof(f97,plain,
    ( v2_funct_1(sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f96])).

fof(f172,plain,
    ( ~ v2_funct_1(sK1)
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(sK1)
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) = sK0
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f169,f90])).

fof(f169,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(sK1)
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) = sK0
    | ~ spl4_6 ),
    inference(resolution,[],[f75,f104])).

fof(f75,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0)
      | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3 ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X1,k1_funct_1(X0,X3)) = X3
      | k2_funct_1(X0) != X1 ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | k1_funct_1(X1,X2) = X3
      | k2_funct_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_funct_1(X0) = X1
          <=> ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k1_relat_1(X1) = k2_relat_1(X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_funct_1(X0) = X1
          <=> ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k1_relat_1(X1) = k2_relat_1(X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( k2_funct_1(X0) = X1
            <=> ( ! [X2,X3] :
                    ( ( ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) )
                     => ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) ) )
                    & ( ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) )
                     => ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) ) ) )
                & k1_relat_1(X1) = k2_relat_1(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t56_funct_1.p',t54_funct_1)).

fof(f142,plain,
    ( ~ spl4_17
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f127,f103,f140])).

fof(f140,plain,
    ( spl4_17
  <=> ~ r2_hidden(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f127,plain,
    ( ~ r2_hidden(k1_relat_1(sK1),sK0)
    | ~ spl4_6 ),
    inference(resolution,[],[f67,f104])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t56_funct_1.p',antisymmetry_r2_hidden)).

fof(f134,plain,
    ( ~ spl4_15
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f126,f103,f132])).

fof(f132,plain,
    ( spl4_15
  <=> ~ v1_xboole_0(k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f126,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK1))
    | ~ spl4_6 ),
    inference(resolution,[],[f65,f104])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t56_funct_1.p',t7_boole)).

fof(f125,plain,
    ( ~ spl4_11
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f41,f123,f117])).

fof(f41,plain,
    ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) != sK0
    | k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0) != sK0 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0
        | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0 )
      & r2_hidden(X0,k1_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0
        | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0 )
      & r2_hidden(X0,k1_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( r2_hidden(X0,k1_relat_1(X1))
            & v2_funct_1(X1) )
         => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
            & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t56_funct_1.p',t56_funct_1)).

fof(f112,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f52,f110])).

fof(f110,plain,
    ( spl4_8
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f52,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/funct_1__t56_funct_1.p',d2_xboole_0)).

fof(f105,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f45,f103])).

fof(f45,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f98,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f44,f96])).

fof(f44,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f91,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f43,f89])).

fof(f43,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f84,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f42,f82])).

fof(f42,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
