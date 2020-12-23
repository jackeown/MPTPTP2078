%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t70_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:27 EDT 2019

% Result     : Theorem 2.36s
% Output     : Refutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 224 expanded)
%              Number of leaves         :   33 (  75 expanded)
%              Depth                    :   17
%              Number of atoms          :  433 ( 666 expanded)
%              Number of equality atoms :   59 ( 110 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23949,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f96,f103,f122,f143,f265,f283,f347,f364,f1283,f1621,f5923,f5929,f13732,f14643,f23948])).

fof(f23948,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | spl6_9
    | ~ spl6_22 ),
    inference(avatar_contradiction_clause,[],[f23947])).

fof(f23947,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_9
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f23941,f142])).

fof(f142,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl6_9
  <=> k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f23941,plain,
    ( k1_funct_1(sK2,sK0) = k1_funct_1(k7_relat_1(sK2,sK1),sK0)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_22 ),
    inference(resolution,[],[f16601,f121])).

fof(f121,plain,
    ( r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl6_4
  <=> r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f16601,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(X3,k1_relat_1(k7_relat_1(sK2,X4)))
        | k1_funct_1(sK2,X3) = k1_funct_1(k7_relat_1(sK2,X4),X3) )
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_22 ),
    inference(condensation,[],[f16600])).

fof(f16600,plain,
    ( ! [X4,X5,X3] :
        ( ~ r2_hidden(X3,k1_relat_1(k7_relat_1(sK2,X5)))
        | ~ r2_hidden(X3,k1_relat_1(k7_relat_1(sK2,X4)))
        | k1_funct_1(sK2,X3) = k1_funct_1(k7_relat_1(sK2,X4),X3) )
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_22 ),
    inference(forward_demodulation,[],[f16595,f104])).

fof(f104,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK2,X0)) = k3_xboole_0(k1_relat_1(sK2),X0)
    | ~ spl6_0 ),
    inference(resolution,[],[f95,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t70_funct_1.p',t90_relat_1)).

fof(f95,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_0 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl6_0
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_0])])).

fof(f16595,plain,
    ( ! [X4,X5,X3] :
        ( ~ r2_hidden(X3,k1_relat_1(k7_relat_1(sK2,X4)))
        | k1_funct_1(sK2,X3) = k1_funct_1(k7_relat_1(sK2,X4),X3)
        | ~ r2_hidden(X3,k3_xboole_0(k1_relat_1(sK2),X5)) )
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_22 ),
    inference(resolution,[],[f15132,f88])).

fof(f88,plain,(
    ! [X0,X3,X1] :
      ( sP5(X3,X1,X0)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( sP5(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t70_funct_1.p',d4_xboole_0)).

fof(f15132,plain,
    ( ! [X4,X2,X3] :
        ( ~ sP5(X2,X4,k1_relat_1(sK2))
        | ~ r2_hidden(X2,k1_relat_1(k7_relat_1(sK2,X3)))
        | k1_funct_1(sK2,X2) = k1_funct_1(k7_relat_1(sK2,X3),X2) )
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_22 ),
    inference(resolution,[],[f14716,f78])).

fof(f78,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ sP5(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f14716,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | k1_funct_1(sK2,X0) = k1_funct_1(k7_relat_1(sK2,X1),X0)
        | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,X1))) )
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_22 ),
    inference(resolution,[],[f13782,f368])).

fof(f368,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,k1_funct_1(k7_relat_1(sK2,X1),X0)),k7_relat_1(sK2,X1))
        | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,X1))) )
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f367,f95])).

fof(f367,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,X1)))
        | r2_hidden(k4_tarski(X0,k1_funct_1(k7_relat_1(sK2,X1),X0)),k7_relat_1(sK2,X1))
        | ~ v1_relat_1(sK2) )
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(resolution,[],[f128,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t70_funct_1.p',dt_k7_relat_1)).

fof(f128,plain,
    ( ! [X12,X11] :
        ( ~ v1_relat_1(k7_relat_1(sK2,X11))
        | ~ r2_hidden(X12,k1_relat_1(k7_relat_1(sK2,X11)))
        | r2_hidden(k4_tarski(X12,k1_funct_1(k7_relat_1(sK2,X11),X12)),k7_relat_1(sK2,X11)) )
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(resolution,[],[f111,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t70_funct_1.p',d4_funct_1)).

fof(f111,plain,
    ( ! [X1] : v1_funct_1(k7_relat_1(sK2,X1))
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f106,f95])).

fof(f106,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(sK2)
        | v1_funct_1(k7_relat_1(sK2,X1)) )
    | ~ spl6_2 ),
    inference(resolution,[],[f102,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t70_funct_1.p',fc8_funct_1)).

fof(f102,plain,
    ( v1_funct_1(sK2)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl6_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f13782,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),k7_relat_1(sK2,X2))
        | ~ r2_hidden(X0,k1_relat_1(sK2))
        | k1_funct_1(sK2,X0) = X1 )
    | ~ spl6_0
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f13780,f95])).

fof(f13780,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | ~ r2_hidden(k4_tarski(X0,X1),k7_relat_1(sK2,X2))
        | k1_funct_1(sK2,X0) = X1
        | ~ v1_relat_1(sK2) )
    | ~ spl6_22 ),
    inference(resolution,[],[f13770,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t70_funct_1.p',t88_relat_1)).

fof(f13770,plain,
    ( ! [X4,X2,X3] :
        ( ~ r1_tarski(X4,sK2)
        | ~ r2_hidden(X2,k1_relat_1(sK2))
        | ~ r2_hidden(k4_tarski(X2,X3),X4)
        | k1_funct_1(sK2,X2) = X3 )
    | ~ spl6_22 ),
    inference(resolution,[],[f13763,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t70_funct_1.p',t3_subset)).

fof(f13763,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(sK2))
        | k1_funct_1(sK2,X0) = X1
        | ~ r2_hidden(X0,k1_relat_1(sK2))
        | ~ r2_hidden(k4_tarski(X0,X1),X2) )
    | ~ spl6_22 ),
    inference(resolution,[],[f264,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t70_funct_1.p',t4_subset)).

fof(f264,plain,
    ( ! [X8,X7] :
        ( ~ m1_subset_1(k4_tarski(X7,X8),sK2)
        | ~ r2_hidden(X7,k1_relat_1(sK2))
        | k1_funct_1(sK2,X7) = X8 )
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f263])).

fof(f263,plain,
    ( spl6_22
  <=> ! [X7,X8] :
        ( ~ r2_hidden(X7,k1_relat_1(sK2))
        | ~ m1_subset_1(k4_tarski(X7,X8),sK2)
        | k1_funct_1(sK2,X7) = X8 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f14643,plain,
    ( ~ spl6_38
    | ~ spl6_112 ),
    inference(avatar_contradiction_clause,[],[f14642])).

fof(f14642,plain,
    ( $false
    | ~ spl6_38
    | ~ spl6_112 ),
    inference(subsumption_resolution,[],[f2119,f12858])).

fof(f12858,plain,
    ( ! [X2] : ~ r2_hidden(X2,k1_xboole_0)
    | ~ spl6_38 ),
    inference(resolution,[],[f405,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t70_funct_1.p',t7_boole)).

fof(f405,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f404])).

fof(f404,plain,
    ( spl6_38
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f2119,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl6_112 ),
    inference(avatar_component_clause,[],[f2118])).

fof(f2118,plain,
    ( spl6_112
  <=> r2_hidden(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_112])])).

fof(f13732,plain,
    ( ~ spl6_0
    | ~ spl6_24
    | ~ spl6_90
    | spl6_113
    | ~ spl6_176 ),
    inference(avatar_contradiction_clause,[],[f13731])).

fof(f13731,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_24
    | ~ spl6_90
    | ~ spl6_113
    | ~ spl6_176 ),
    inference(subsumption_resolution,[],[f13691,f2122])).

fof(f2122,plain,
    ( ~ r2_hidden(sK0,k1_xboole_0)
    | ~ spl6_113 ),
    inference(avatar_component_clause,[],[f2121])).

fof(f2121,plain,
    ( spl6_113
  <=> ~ r2_hidden(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_113])])).

fof(f13691,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl6_0
    | ~ spl6_24
    | ~ spl6_90
    | ~ spl6_176 ),
    inference(superposition,[],[f1620,f13664])).

fof(f13664,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | ~ spl6_0
    | ~ spl6_24
    | ~ spl6_176 ),
    inference(forward_demodulation,[],[f13663,f55])).

fof(f55,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t70_funct_1.p',t2_boole)).

fof(f13663,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(k1_xboole_0,X0)) = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl6_0
    | ~ spl6_24
    | ~ spl6_176 ),
    inference(forward_demodulation,[],[f11533,f4682])).

fof(f4682,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ spl6_176 ),
    inference(avatar_component_clause,[],[f4681])).

fof(f4681,plain,
    ( spl6_176
  <=> k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_176])])).

fof(f11533,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(k1_xboole_0,X0)) = k3_xboole_0(X0,k1_relat_1(k1_xboole_0))
    | ~ spl6_0
    | ~ spl6_24 ),
    inference(superposition,[],[f149,f282])).

fof(f282,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f281])).

fof(f281,plain,
    ( spl6_24
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f149,plain,
    ( ! [X1] : k1_relat_1(k7_relat_1(sK2,X1)) = k3_xboole_0(X1,k1_relat_1(sK2))
    | ~ spl6_0 ),
    inference(superposition,[],[f104,f63])).

fof(f63,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t70_funct_1.p',commutativity_k3_xboole_0)).

fof(f1620,plain,
    ( r2_hidden(sK0,k1_relat_1(k7_relat_1(k1_xboole_0,sK1)))
    | ~ spl6_90 ),
    inference(avatar_component_clause,[],[f1619])).

fof(f1619,plain,
    ( spl6_90
  <=> r2_hidden(sK0,k1_relat_1(k7_relat_1(k1_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_90])])).

fof(f5929,plain,
    ( ~ spl6_88
    | spl6_177 ),
    inference(avatar_contradiction_clause,[],[f5928])).

fof(f5928,plain,
    ( $false
    | ~ spl6_88
    | ~ spl6_177 ),
    inference(subsumption_resolution,[],[f5927,f4685])).

fof(f4685,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | ~ spl6_177 ),
    inference(avatar_component_clause,[],[f4684])).

fof(f4684,plain,
    ( spl6_177
  <=> k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_177])])).

fof(f5927,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ spl6_88 ),
    inference(resolution,[],[f1596,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t70_funct_1.p',t6_boole)).

fof(f1596,plain,
    ( v1_xboole_0(k1_relat_1(k1_xboole_0))
    | ~ spl6_88 ),
    inference(avatar_component_clause,[],[f1595])).

fof(f1595,plain,
    ( spl6_88
  <=> v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_88])])).

fof(f5923,plain,
    ( ~ spl6_30
    | ~ spl6_32
    | ~ spl6_38
    | spl6_89 ),
    inference(avatar_contradiction_clause,[],[f5920])).

fof(f5920,plain,
    ( $false
    | ~ spl6_30
    | ~ spl6_32
    | ~ spl6_38
    | ~ spl6_89 ),
    inference(resolution,[],[f5808,f61])).

fof(f61,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t70_funct_1.p',existence_m1_subset_1)).

fof(f5808,plain,
    ( ! [X4] : ~ m1_subset_1(X4,k1_relat_1(k1_xboole_0))
    | ~ spl6_30
    | ~ spl6_32
    | ~ spl6_38
    | ~ spl6_89 ),
    inference(subsumption_resolution,[],[f5806,f1599])).

fof(f1599,plain,
    ( ~ v1_xboole_0(k1_relat_1(k1_xboole_0))
    | ~ spl6_89 ),
    inference(avatar_component_clause,[],[f1598])).

fof(f1598,plain,
    ( spl6_89
  <=> ~ v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_89])])).

fof(f5806,plain,
    ( ! [X4] :
        ( v1_xboole_0(k1_relat_1(k1_xboole_0))
        | ~ m1_subset_1(X4,k1_relat_1(k1_xboole_0)) )
    | ~ spl6_30
    | ~ spl6_32
    | ~ spl6_38 ),
    inference(resolution,[],[f5803,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t70_funct_1.p',t2_subset)).

fof(f5803,plain,
    ( ! [X6] : ~ r2_hidden(X6,k1_relat_1(k1_xboole_0))
    | ~ spl6_30
    | ~ spl6_32
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f4598,f4600])).

fof(f4600,plain,
    ( ! [X2] : ~ r2_hidden(X2,k1_xboole_0)
    | ~ spl6_38 ),
    inference(resolution,[],[f405,f75])).

fof(f4598,plain,
    ( ! [X6] :
        ( ~ r2_hidden(X6,k1_relat_1(k1_xboole_0))
        | r2_hidden(k4_tarski(X6,k1_funct_1(k1_xboole_0,X6)),k1_xboole_0) )
    | ~ spl6_30
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f4593,f346])).

fof(f346,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f345])).

fof(f345,plain,
    ( spl6_30
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f4593,plain,
    ( ! [X6] :
        ( ~ v1_relat_1(k1_xboole_0)
        | ~ r2_hidden(X6,k1_relat_1(k1_xboole_0))
        | r2_hidden(k4_tarski(X6,k1_funct_1(k1_xboole_0,X6)),k1_xboole_0) )
    | ~ spl6_32 ),
    inference(resolution,[],[f363,f85])).

fof(f363,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f362])).

fof(f362,plain,
    ( spl6_32
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f1621,plain,
    ( spl6_90
    | ~ spl6_4
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f1301,f281,f120,f1619])).

fof(f1301,plain,
    ( r2_hidden(sK0,k1_relat_1(k7_relat_1(k1_xboole_0,sK1)))
    | ~ spl6_4
    | ~ spl6_24 ),
    inference(superposition,[],[f121,f282])).

fof(f1283,plain,
    ( k1_xboole_0 != sK2
    | v1_xboole_0(k1_xboole_0)
    | ~ v1_xboole_0(sK2) ),
    introduced(theory_axiom,[])).

fof(f364,plain,
    ( spl6_32
    | ~ spl6_2
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f297,f281,f101,f362])).

fof(f297,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl6_2
    | ~ spl6_24 ),
    inference(superposition,[],[f102,f282])).

fof(f347,plain,
    ( spl6_30
    | ~ spl6_0
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f296,f281,f94,f345])).

fof(f296,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl6_0
    | ~ spl6_24 ),
    inference(superposition,[],[f95,f282])).

fof(f283,plain,
    ( spl6_24
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f269,f260,f281])).

fof(f260,plain,
    ( spl6_20
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f269,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_20 ),
    inference(resolution,[],[f261,f56])).

fof(f261,plain,
    ( v1_xboole_0(sK2)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f260])).

fof(f265,plain,
    ( spl6_20
    | spl6_22
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f168,f101,f94,f263,f260])).

fof(f168,plain,
    ( ! [X8,X7] :
        ( ~ r2_hidden(X7,k1_relat_1(sK2))
        | k1_funct_1(sK2,X7) = X8
        | v1_xboole_0(sK2)
        | ~ m1_subset_1(k4_tarski(X7,X8),sK2) )
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(resolution,[],[f114,f67])).

fof(f114,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(k4_tarski(X4,X5),sK2)
        | ~ r2_hidden(X4,k1_relat_1(sK2))
        | k1_funct_1(sK2,X4) = X5 )
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f109,f95])).

fof(f109,plain,
    ( ! [X4,X5] :
        ( ~ v1_relat_1(sK2)
        | ~ r2_hidden(X4,k1_relat_1(sK2))
        | ~ r2_hidden(k4_tarski(X4,X5),sK2)
        | k1_funct_1(sK2,X4) = X5 )
    | ~ spl6_2 ),
    inference(resolution,[],[f102,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f143,plain,(
    ~ spl6_9 ),
    inference(avatar_split_clause,[],[f53,f141])).

fof(f53,plain,(
    k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0)
      & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0)
      & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
         => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
       => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t70_funct_1.p',t70_funct_1)).

fof(f122,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f52,f120])).

fof(f52,plain,(
    r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f32])).

fof(f103,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f51,f101])).

fof(f51,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f96,plain,(
    spl6_0 ),
    inference(avatar_split_clause,[],[f50,f94])).

fof(f50,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
