%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t18_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n030.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:21 EDT 2019

% Result     : Theorem 0.83s
% Output     : Refutation 0.83s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 207 expanded)
%              Number of leaves         :   23 (  64 expanded)
%              Depth                    :   15
%              Number of atoms          :  367 ( 921 expanded)
%              Number of equality atoms :   99 ( 316 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2132,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f117,f1919,f2022,f2024,f2128])).

fof(f2128,plain,(
    ~ spl8_24 ),
    inference(avatar_contradiction_clause,[],[f2127])).

fof(f2127,plain,
    ( $false
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f2126,f95])).

fof(f95,plain,(
    ! [X0,X1] : v1_relat_1(sK7(X0,X1)) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK7(X0,X1),X3) = o_1_0_funct_1(X0)
          | ~ r2_hidden(X3,X1) )
      & k1_relat_1(sK7(X0,X1)) = X1
      & v1_funct_1(sK7(X0,X1))
      & v1_relat_1(sK7(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f46,f65])).

fof(f65,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X2,X3) = o_1_0_funct_1(X0)
              | ~ r2_hidden(X3,X1) )
          & k1_relat_1(X2) = X1
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ! [X3] :
            ( k1_funct_1(sK7(X0,X1),X3) = o_1_0_funct_1(X0)
            | ~ r2_hidden(X3,X1) )
        & k1_relat_1(sK7(X0,X1)) = X1
        & v1_funct_1(sK7(X0,X1))
        & v1_relat_1(sK7(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = o_1_0_funct_1(X0)
          | ~ r2_hidden(X3,X1) )
      & k1_relat_1(X2) = X1
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => k1_funct_1(X2,X3) = o_1_0_funct_1(X0) )
      & k1_relat_1(X2) = X1
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t18_funct_1.p',s3_funct_1__e1_27_1__funct_1)).

fof(f2126,plain,
    ( ~ v1_relat_1(sK7(sK0,sK1))
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f2125,f96])).

fof(f96,plain,(
    ! [X0,X1] : v1_funct_1(sK7(X0,X1)) ),
    inference(cnf_transformation,[],[f66])).

fof(f2125,plain,
    ( ~ v1_funct_1(sK7(sK0,sK1))
    | ~ v1_relat_1(sK7(sK0,sK1))
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f2119,f97])).

fof(f97,plain,(
    ! [X0,X1] : k1_relat_1(sK7(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f66])).

fof(f2119,plain,
    ( k1_relat_1(sK7(sK0,sK1)) != sK1
    | ~ v1_funct_1(sK7(sK0,sK1))
    | ~ v1_relat_1(sK7(sK0,sK1))
    | ~ spl8_24 ),
    inference(resolution,[],[f2116,f68])).

fof(f68,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_relat_1(X2),sK0)
      | k1_relat_1(X2) != sK1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_relat_1(X2),sK0)
        | k1_relat_1(X2) != sK1
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f50])).

fof(f50,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( ~ r1_tarski(k2_relat_1(X2),X0)
            | k1_relat_1(X2) != X1
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 != X0 ) )
   => ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),sK0)
          | k1_relat_1(X2) != sK1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = sK1
        | k1_xboole_0 != sK0 ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t18_funct_1.p',t18_funct_1)).

fof(f2116,plain,
    ( r1_tarski(k2_relat_1(sK7(sK0,sK1)),sK0)
    | ~ spl8_24 ),
    inference(resolution,[],[f1918,f72])).

fof(f72,plain,(
    ! [X0] : m1_subset_1(o_1_0_funct_1(X0),X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(o_1_0_funct_1(X0),X0) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t18_funct_1.p',dt_o_1_0_funct_1)).

fof(f1918,plain,
    ( ! [X22] :
        ( ~ m1_subset_1(o_1_0_funct_1(X22),sK0)
        | r1_tarski(k2_relat_1(sK7(X22,sK1)),sK0) )
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f1917])).

fof(f1917,plain,
    ( spl8_24
  <=> ! [X22] :
        ( ~ m1_subset_1(o_1_0_funct_1(X22),sK0)
        | r1_tarski(k2_relat_1(sK7(X22,sK1)),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f2024,plain,(
    ~ spl8_2 ),
    inference(avatar_contradiction_clause,[],[f2023])).

fof(f2023,plain,
    ( $false
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f116,f136])).

fof(f136,plain,(
    k1_xboole_0 != sK1 ),
    inference(subsumption_resolution,[],[f134,f70])).

fof(f70,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t18_funct_1.p',fc1_xboole_0)).

fof(f134,plain,
    ( k1_xboole_0 != sK1
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[],[f129,f131])).

fof(f131,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f122,f70])).

fof(f122,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = k1_relat_1(X0) ) ),
    inference(resolution,[],[f77,f75])).

fof(f75,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t18_funct_1.p',t6_boole)).

fof(f77,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t18_funct_1.p',fc10_relat_1)).

fof(f129,plain,(
    ! [X1] :
      ( k1_relat_1(X1) != sK1
      | ~ v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f128,f74])).

fof(f74,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t18_funct_1.p',cc1_funct_1)).

fof(f128,plain,(
    ! [X1] :
      ( k1_relat_1(X1) != sK1
      | ~ v1_funct_1(X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f127,f73])).

fof(f73,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t18_funct_1.p',cc1_relat_1)).

fof(f127,plain,(
    ! [X1] :
      ( k1_relat_1(X1) != sK1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f125,f71])).

fof(f71,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t18_funct_1.p',t2_xboole_1)).

fof(f125,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_xboole_0,sK0)
      | k1_relat_1(X1) != sK1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(superposition,[],[f68,f121])).

fof(f121,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f76,f75])).

fof(f76,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t18_funct_1.p',fc11_relat_1)).

fof(f116,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl8_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f2022,plain,
    ( spl8_1
    | ~ spl8_22 ),
    inference(avatar_contradiction_clause,[],[f2021])).

fof(f2021,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_22 ),
    inference(subsumption_resolution,[],[f1920,f110])).

fof(f110,plain,
    ( k1_xboole_0 != sK0
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl8_1
  <=> k1_xboole_0 != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f1920,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_22 ),
    inference(resolution,[],[f1915,f75])).

fof(f1915,plain,
    ( v1_xboole_0(sK0)
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f1914])).

fof(f1914,plain,
    ( spl8_22
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f1919,plain,
    ( spl8_22
    | spl8_24 ),
    inference(avatar_split_clause,[],[f1891,f1917,f1914])).

fof(f1891,plain,(
    ! [X22] :
      ( ~ m1_subset_1(o_1_0_funct_1(X22),sK0)
      | v1_xboole_0(sK0)
      | r1_tarski(k2_relat_1(sK7(X22,sK1)),sK0) ) ),
    inference(superposition,[],[f184,f1832])).

fof(f1832,plain,(
    ! [X15] : o_1_0_funct_1(X15) = sK6(k2_relat_1(sK7(X15,sK1)),sK0) ),
    inference(resolution,[],[f1821,f163])).

fof(f163,plain,(
    ! [X0] : r2_hidden(sK6(k2_relat_1(sK7(X0,sK1)),sK0),k2_relat_1(sK7(X0,sK1))) ),
    inference(equality_resolution,[],[f162])).

fof(f162,plain,(
    ! [X2,X1] :
      ( sK1 != X2
      | r2_hidden(sK6(k2_relat_1(sK7(X1,X2)),sK0),k2_relat_1(sK7(X1,X2))) ) ),
    inference(forward_demodulation,[],[f161,f97])).

fof(f161,plain,(
    ! [X2,X1] :
      ( k1_relat_1(sK7(X1,X2)) != sK1
      | r2_hidden(sK6(k2_relat_1(sK7(X1,X2)),sK0),k2_relat_1(sK7(X1,X2))) ) ),
    inference(subsumption_resolution,[],[f160,f95])).

fof(f160,plain,(
    ! [X2,X1] :
      ( k1_relat_1(sK7(X1,X2)) != sK1
      | r2_hidden(sK6(k2_relat_1(sK7(X1,X2)),sK0),k2_relat_1(sK7(X1,X2)))
      | ~ v1_relat_1(sK7(X1,X2)) ) ),
    inference(resolution,[],[f158,f96])).

fof(f158,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k1_relat_1(X0) != sK1
      | r2_hidden(sK6(k2_relat_1(X0),sK0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f89,f68])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK6(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f61,f62])).

fof(f62,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t18_funct_1.p',d3_tarski)).

fof(f1821,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X5,k2_relat_1(sK7(X3,X4)))
      | o_1_0_funct_1(X3) = X5 ) ),
    inference(subsumption_resolution,[],[f1817,f582])).

fof(f582,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(sK4(sK7(X3,X4),X2),X4)
      | ~ r2_hidden(X2,k2_relat_1(sK7(X3,X4))) ) ),
    inference(forward_demodulation,[],[f581,f97])).

fof(f581,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X2,k2_relat_1(sK7(X3,X4)))
      | r2_hidden(sK4(sK7(X3,X4),X2),k1_relat_1(sK7(X3,X4))) ) ),
    inference(subsumption_resolution,[],[f579,f95])).

fof(f579,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X2,k2_relat_1(sK7(X3,X4)))
      | r2_hidden(sK4(sK7(X3,X4),X2),k1_relat_1(sK7(X3,X4)))
      | ~ v1_relat_1(sK7(X3,X4)) ) ),
    inference(resolution,[],[f104,f96])).

fof(f104,plain,(
    ! [X0,X5] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | r2_hidden(sK4(X0,X5),k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK4(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK2(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK2(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK3(X0,X1)) = sK2(X0,X1)
                  & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK2(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK4(X0,X5)) = X5
                    & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f53,f56,f55,f54])).

fof(f54,plain,(
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
              ( k1_funct_1(X0,X3) != sK2(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK2(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1)) = X2
        & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X5)) = X5
        & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
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
    inference(rectify,[],[f52])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox/benchmark/funct_1__t18_funct_1.p',d5_funct_1)).

fof(f1817,plain,(
    ! [X4,X5,X3] :
      ( o_1_0_funct_1(X3) = X5
      | ~ r2_hidden(X5,k2_relat_1(sK7(X3,X4)))
      | ~ r2_hidden(sK4(sK7(X3,X4),X5),X4) ) ),
    inference(superposition,[],[f685,f98])).

fof(f98,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(sK7(X0,X1),X3) = o_1_0_funct_1(X0)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f685,plain,(
    ! [X4,X2,X3] :
      ( k1_funct_1(sK7(X3,X4),sK4(sK7(X3,X4),X2)) = X2
      | ~ r2_hidden(X2,k2_relat_1(sK7(X3,X4))) ) ),
    inference(subsumption_resolution,[],[f683,f95])).

fof(f683,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X2,k2_relat_1(sK7(X3,X4)))
      | k1_funct_1(sK7(X3,X4),sK4(sK7(X3,X4),X2)) = X2
      | ~ v1_relat_1(sK7(X3,X4)) ) ),
    inference(resolution,[],[f103,f96])).

fof(f103,plain,(
    ! [X0,X5] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | k1_funct_1(X0,sK4(X0,X5)) = X5
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK4(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f184,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK6(X0,X1),X1)
      | v1_xboole_0(X1)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f90,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t18_funct_1.p',t2_subset)).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f117,plain,
    ( ~ spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f67,f115,f109])).

fof(f67,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f51])).
%------------------------------------------------------------------------------
