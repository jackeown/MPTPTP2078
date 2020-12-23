%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t122_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:14 EDT 2019

% Result     : Theorem 1.83s
% Output     : Refutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 303 expanded)
%              Number of leaves         :   38 ( 125 expanded)
%              Depth                    :   13
%              Number of atoms          :  505 ( 985 expanded)
%              Number of equality atoms :  118 ( 250 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1931,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f107,f114,f121,f138,f160,f172,f190,f204,f240,f273,f285,f312,f344,f351,f358,f387,f394,f479,f905,f1388,f1774,f1879,f1901,f1930])).

fof(f1930,plain,
    ( ~ spl5_0
    | ~ spl5_2
    | spl5_5
    | ~ spl5_128 ),
    inference(avatar_contradiction_clause,[],[f1929])).

fof(f1929,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_128 ),
    inference(subsumption_resolution,[],[f1928,f106])).

fof(f106,plain,
    ( v1_relat_1(sK0)
    | ~ spl5_0 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl5_0
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f1928,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_128 ),
    inference(subsumption_resolution,[],[f1927,f113])).

fof(f113,plain,
    ( v1_funct_1(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl5_2
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f1927,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl5_5
    | ~ spl5_128 ),
    inference(subsumption_resolution,[],[f1925,f120])).

fof(f120,plain,
    ( ~ v2_funct_1(sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl5_5
  <=> ~ v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f1925,plain,
    ( v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl5_128 ),
    inference(trivial_inequality_removal,[],[f1924])).

fof(f1924,plain,
    ( sK1(sK0) != sK1(sK0)
    | v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl5_128 ),
    inference(superposition,[],[f81,f1872])).

fof(f1872,plain,
    ( sK1(sK0) = sK2(sK0)
    | ~ spl5_128 ),
    inference(avatar_component_clause,[],[f1871])).

fof(f1871,plain,
    ( spl5_128
  <=> sK1(sK0) = sK2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_128])])).

fof(f81,plain,(
    ! [X0] :
      ( sK1(X0) != sK2(X0)
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK1(X0) != sK2(X0)
            & k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK2(X0))
            & r2_hidden(sK2(X0),k1_relat_1(X0))
            & r2_hidden(sK1(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f60,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK1(X0) != sK2(X0)
        & k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK2(X0))
        & r2_hidden(sK2(X0),k1_relat_1(X0))
        & r2_hidden(sK1(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
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
    inference(rectify,[],[f59])).

fof(f59,plain,(
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
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t122_funct_1.p',d8_funct_1)).

fof(f1901,plain,
    ( ~ spl5_20
    | spl5_53
    | ~ spl5_130 ),
    inference(avatar_contradiction_clause,[],[f1900])).

fof(f1900,plain,
    ( $false
    | ~ spl5_20
    | ~ spl5_53
    | ~ spl5_130 ),
    inference(subsumption_resolution,[],[f1885,f393])).

fof(f393,plain,
    ( k11_relat_1(sK0,sK1(sK0)) != k1_xboole_0
    | ~ spl5_53 ),
    inference(avatar_component_clause,[],[f392])).

fof(f392,plain,
    ( spl5_53
  <=> k11_relat_1(sK0,sK1(sK0)) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).

fof(f1885,plain,
    ( k11_relat_1(sK0,sK1(sK0)) = k1_xboole_0
    | ~ spl5_20
    | ~ spl5_130 ),
    inference(superposition,[],[f189,f1878])).

fof(f1878,plain,
    ( k9_relat_1(sK0,k1_tarski(sK1(sK0))) = k1_xboole_0
    | ~ spl5_130 ),
    inference(avatar_component_clause,[],[f1877])).

fof(f1877,plain,
    ( spl5_130
  <=> k9_relat_1(sK0,k1_tarski(sK1(sK0))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_130])])).

fof(f189,plain,
    ( ! [X0] : k9_relat_1(sK0,k1_tarski(X0)) = k11_relat_1(sK0,X0)
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl5_20
  <=> ! [X0] : k9_relat_1(sK0,k1_tarski(X0)) = k11_relat_1(sK0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f1879,plain,
    ( spl5_128
    | spl5_130
    | ~ spl5_114 ),
    inference(avatar_split_clause,[],[f1808,f1770,f1877,f1871])).

fof(f1770,plain,
    ( spl5_114
  <=> ! [X1] :
        ( k9_relat_1(sK0,k3_xboole_0(k1_tarski(sK1(sK0)),k1_tarski(X1))) = k1_xboole_0
        | sK2(sK0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_114])])).

fof(f1808,plain,
    ( k9_relat_1(sK0,k1_tarski(sK1(sK0))) = k1_xboole_0
    | sK1(sK0) = sK2(sK0)
    | ~ spl5_114 ),
    inference(superposition,[],[f1771,f83])).

fof(f83,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/funct_1__t122_funct_1.p',idempotence_k3_xboole_0)).

fof(f1771,plain,
    ( ! [X1] :
        ( k9_relat_1(sK0,k3_xboole_0(k1_tarski(sK1(sK0)),k1_tarski(X1))) = k1_xboole_0
        | sK2(sK0) = X1 )
    | ~ spl5_114 ),
    inference(avatar_component_clause,[],[f1770])).

fof(f1774,plain,
    ( spl5_114
    | ~ spl5_18
    | ~ spl5_104 ),
    inference(avatar_split_clause,[],[f1036,f817,f170,f1770])).

fof(f170,plain,
    ( spl5_18
  <=> k9_relat_1(sK0,k1_xboole_0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f817,plain,
    ( spl5_104
  <=> ! [X0] : k9_relat_1(sK0,k3_xboole_0(k1_tarski(sK1(sK0)),X0)) = k9_relat_1(sK0,k3_xboole_0(k1_tarski(sK2(sK0)),X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_104])])).

fof(f1036,plain,
    ( ! [X0] :
        ( k9_relat_1(sK0,k3_xboole_0(k1_tarski(sK1(sK0)),k1_tarski(X0))) = k1_xboole_0
        | sK2(sK0) = X0 )
    | ~ spl5_18
    | ~ spl5_104 ),
    inference(forward_demodulation,[],[f1010,f171])).

fof(f171,plain,
    ( k9_relat_1(sK0,k1_xboole_0) = k1_xboole_0
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f170])).

fof(f1010,plain,
    ( ! [X0] :
        ( k9_relat_1(sK0,k1_xboole_0) = k9_relat_1(sK0,k3_xboole_0(k1_tarski(sK1(sK0)),k1_tarski(X0)))
        | sK2(sK0) = X0 )
    | ~ spl5_104 ),
    inference(superposition,[],[f818,f181])).

fof(f181,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_xboole_0
      | X0 = X1 ) ),
    inference(resolution,[],[f95,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t122_funct_1.p',t17_zfmisc_1)).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t122_funct_1.p',d7_xboole_0)).

fof(f818,plain,
    ( ! [X0] : k9_relat_1(sK0,k3_xboole_0(k1_tarski(sK1(sK0)),X0)) = k9_relat_1(sK0,k3_xboole_0(k1_tarski(sK2(sK0)),X0))
    | ~ spl5_104 ),
    inference(avatar_component_clause,[],[f817])).

fof(f1388,plain,(
    ~ spl5_10 ),
    inference(avatar_contradiction_clause,[],[f1371])).

fof(f1371,plain,
    ( $false
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f72,f137])).

fof(f137,plain,
    ( ! [X1] : v1_xboole_0(X1)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl5_10
  <=> ! [X1] : v1_xboole_0(X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f72,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t122_funct_1.p',fc2_xboole_0)).

fof(f905,plain,
    ( spl5_104
    | ~ spl5_50
    | ~ spl5_68 ),
    inference(avatar_split_clause,[],[f584,f477,f385,f817])).

fof(f385,plain,
    ( spl5_50
  <=> k11_relat_1(sK0,sK1(sK0)) = k11_relat_1(sK0,sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).

fof(f477,plain,
    ( spl5_68
  <=> ! [X1,X2] : k3_xboole_0(k9_relat_1(sK0,X2),k11_relat_1(sK0,X1)) = k9_relat_1(sK0,k3_xboole_0(k1_tarski(X1),X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).

fof(f584,plain,
    ( ! [X0] : k9_relat_1(sK0,k3_xboole_0(k1_tarski(sK1(sK0)),X0)) = k9_relat_1(sK0,k3_xboole_0(k1_tarski(sK2(sK0)),X0))
    | ~ spl5_50
    | ~ spl5_68 ),
    inference(forward_demodulation,[],[f571,f478])).

fof(f478,plain,
    ( ! [X2,X1] : k3_xboole_0(k9_relat_1(sK0,X2),k11_relat_1(sK0,X1)) = k9_relat_1(sK0,k3_xboole_0(k1_tarski(X1),X2))
    | ~ spl5_68 ),
    inference(avatar_component_clause,[],[f477])).

fof(f571,plain,
    ( ! [X0] : k3_xboole_0(k9_relat_1(sK0,X0),k11_relat_1(sK0,sK1(sK0))) = k9_relat_1(sK0,k3_xboole_0(k1_tarski(sK2(sK0)),X0))
    | ~ spl5_50
    | ~ spl5_68 ),
    inference(superposition,[],[f478,f386])).

fof(f386,plain,
    ( k11_relat_1(sK0,sK1(sK0)) = k11_relat_1(sK0,sK2(sK0))
    | ~ spl5_50 ),
    inference(avatar_component_clause,[],[f385])).

fof(f479,plain,
    ( spl5_68
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f316,f188,f477])).

fof(f316,plain,
    ( ! [X2,X1] : k3_xboole_0(k9_relat_1(sK0,X2),k11_relat_1(sK0,X1)) = k9_relat_1(sK0,k3_xboole_0(k1_tarski(X1),X2))
    | ~ spl5_20 ),
    inference(superposition,[],[f222,f189])).

fof(f222,plain,(
    ! [X4,X3] : k3_xboole_0(k9_relat_1(sK0,X4),k9_relat_1(sK0,X3)) = k9_relat_1(sK0,k3_xboole_0(X3,X4)) ),
    inference(superposition,[],[f69,f84])).

fof(f84,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t122_funct_1.p',commutativity_k3_xboole_0)).

fof(f69,plain,(
    ! [X2,X1] : k3_xboole_0(k9_relat_1(sK0,X1),k9_relat_1(sK0,X2)) = k9_relat_1(sK0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,
    ( ~ v2_funct_1(sK0)
    & ! [X1,X2] : k3_xboole_0(k9_relat_1(sK0,X1),k9_relat_1(sK0,X2)) = k9_relat_1(sK0,k3_xboole_0(X1,X2))
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f57])).

fof(f57,plain,
    ( ? [X0] :
        ( ~ v2_funct_1(X0)
        & ! [X1,X2] : k3_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k3_xboole_0(X1,X2))
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ~ v2_funct_1(sK0)
      & ! [X2,X1] : k3_xboole_0(k9_relat_1(sK0,X1),k9_relat_1(sK0,X2)) = k9_relat_1(sK0,k3_xboole_0(X1,X2))
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ? [X0] :
      ( ~ v2_funct_1(X0)
      & ! [X1,X2] : k3_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k3_xboole_0(X1,X2))
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ~ v2_funct_1(X0)
      & ! [X1,X2] : k3_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k3_xboole_0(X1,X2))
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( ! [X1,X2] : k3_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k3_xboole_0(X1,X2))
         => v2_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ! [X1,X2] : k3_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k3_xboole_0(X1,X2))
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t122_funct_1.p',t122_funct_1)).

fof(f394,plain,
    ( ~ spl5_53
    | ~ spl5_40
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f371,f349,f342,f392])).

fof(f342,plain,
    ( spl5_40
  <=> ! [X0] : k1_tarski(X0) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f349,plain,
    ( spl5_42
  <=> k11_relat_1(sK0,sK1(sK0)) = k1_tarski(k1_funct_1(sK0,sK1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f371,plain,
    ( k11_relat_1(sK0,sK1(sK0)) != k1_xboole_0
    | ~ spl5_40
    | ~ spl5_42 ),
    inference(superposition,[],[f343,f350])).

fof(f350,plain,
    ( k11_relat_1(sK0,sK1(sK0)) = k1_tarski(k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_42 ),
    inference(avatar_component_clause,[],[f349])).

fof(f343,plain,
    ( ! [X0] : k1_tarski(X0) != k1_xboole_0
    | ~ spl5_40 ),
    inference(avatar_component_clause,[],[f342])).

fof(f387,plain,
    ( spl5_50
    | ~ spl5_42
    | ~ spl5_44 ),
    inference(avatar_split_clause,[],[f379,f356,f349,f385])).

fof(f356,plain,
    ( spl5_44
  <=> k11_relat_1(sK0,sK2(sK0)) = k1_tarski(k1_funct_1(sK0,sK1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f379,plain,
    ( k11_relat_1(sK0,sK1(sK0)) = k11_relat_1(sK0,sK2(sK0))
    | ~ spl5_42
    | ~ spl5_44 ),
    inference(forward_demodulation,[],[f357,f350])).

fof(f357,plain,
    ( k11_relat_1(sK0,sK2(sK0)) = k1_tarski(k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_44 ),
    inference(avatar_component_clause,[],[f356])).

fof(f358,plain,
    ( spl5_44
    | ~ spl5_26
    | ~ spl5_32
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f300,f283,f271,f238,f356])).

fof(f238,plain,
    ( spl5_26
  <=> r2_hidden(sK2(sK0),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f271,plain,
    ( spl5_32
  <=> k1_funct_1(sK0,sK1(sK0)) = k1_funct_1(sK0,sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f283,plain,
    ( spl5_34
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK0))
        | k11_relat_1(sK0,X0) = k1_tarski(k1_funct_1(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f300,plain,
    ( k11_relat_1(sK0,sK2(sK0)) = k1_tarski(k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_26
    | ~ spl5_32
    | ~ spl5_34 ),
    inference(forward_demodulation,[],[f298,f272])).

fof(f272,plain,
    ( k1_funct_1(sK0,sK1(sK0)) = k1_funct_1(sK0,sK2(sK0))
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f271])).

fof(f298,plain,
    ( k11_relat_1(sK0,sK2(sK0)) = k1_tarski(k1_funct_1(sK0,sK2(sK0)))
    | ~ spl5_26
    | ~ spl5_34 ),
    inference(resolution,[],[f284,f239])).

fof(f239,plain,
    ( r2_hidden(sK2(sK0),k1_relat_1(sK0))
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f238])).

fof(f284,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK0))
        | k11_relat_1(sK0,X0) = k1_tarski(k1_funct_1(sK0,X0)) )
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f283])).

fof(f351,plain,
    ( spl5_42
    | ~ spl5_22
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f297,f283,f202,f349])).

fof(f202,plain,
    ( spl5_22
  <=> r2_hidden(sK1(sK0),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f297,plain,
    ( k11_relat_1(sK0,sK1(sK0)) = k1_tarski(k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_22
    | ~ spl5_34 ),
    inference(resolution,[],[f284,f203])).

fof(f203,plain,
    ( r2_hidden(sK1(sK0),k1_relat_1(sK0))
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f202])).

fof(f344,plain,
    ( spl5_40
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f330,f310,f342])).

fof(f310,plain,
    ( spl5_36
  <=> ! [X0] :
        ( k1_xboole_0 != X0
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f330,plain,
    ( ! [X0] : k1_tarski(X0) != k1_xboole_0
    | ~ spl5_36 ),
    inference(resolution,[],[f311,f72])).

fof(f311,plain,
    ( ! [X0] :
        ( v1_xboole_0(X0)
        | k1_xboole_0 != X0 )
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f310])).

fof(f312,plain,
    ( spl5_36
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f308,f158,f310])).

fof(f158,plain,
    ( spl5_16
  <=> ! [X0] :
        ( ~ r1_subset_1(X0,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f308,plain,
    ( ! [X0] :
        ( k1_xboole_0 != X0
        | v1_xboole_0(X0) )
    | ~ spl5_16 ),
    inference(forward_demodulation,[],[f307,f83])).

fof(f307,plain,
    ( ! [X0] :
        ( v1_xboole_0(X0)
        | k3_xboole_0(X0,X0) != k1_xboole_0 )
    | ~ spl5_16 ),
    inference(duplicate_literal_removal,[],[f302])).

fof(f302,plain,
    ( ! [X0] :
        ( v1_xboole_0(X0)
        | v1_xboole_0(X0)
        | k3_xboole_0(X0,X0) != k1_xboole_0
        | v1_xboole_0(X0) )
    | ~ spl5_16 ),
    inference(resolution,[],[f192,f159])).

fof(f159,plain,
    ( ! [X0] :
        ( ~ r1_subset_1(X0,X0)
        | v1_xboole_0(X0) )
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f158])).

fof(f192,plain,(
    ! [X2,X3] :
      ( r1_subset_1(X2,X3)
      | v1_xboole_0(X3)
      | v1_xboole_0(X2)
      | k3_xboole_0(X2,X3) != k1_xboole_0 ) ),
    inference(resolution,[],[f93,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f66])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t122_funct_1.p',redefinition_r1_subset_1)).

fof(f285,plain,
    ( spl5_34
    | ~ spl5_0
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f242,f112,f105,f283])).

fof(f242,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK0))
        | k11_relat_1(sK0,X0) = k1_tarski(k1_funct_1(sK0,X0)) )
    | ~ spl5_0
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f241,f106])).

fof(f241,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK0))
        | k11_relat_1(sK0,X0) = k1_tarski(k1_funct_1(sK0,X0))
        | ~ v1_relat_1(sK0) )
    | ~ spl5_2 ),
    inference(resolution,[],[f94,f113])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t122_funct_1.p',t117_funct_1)).

fof(f273,plain,
    ( spl5_32
    | ~ spl5_0
    | ~ spl5_2
    | spl5_5 ),
    inference(avatar_split_clause,[],[f233,f119,f112,f105,f271])).

fof(f233,plain,
    ( k1_funct_1(sK0,sK1(sK0)) = k1_funct_1(sK0,sK2(sK0))
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f232,f106])).

fof(f232,plain,
    ( k1_funct_1(sK0,sK1(sK0)) = k1_funct_1(sK0,sK2(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f231,f113])).

fof(f231,plain,
    ( k1_funct_1(sK0,sK1(sK0)) = k1_funct_1(sK0,sK2(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl5_5 ),
    inference(resolution,[],[f80,f120])).

fof(f80,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK2(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f240,plain,
    ( spl5_26
    | ~ spl5_0
    | ~ spl5_2
    | spl5_5 ),
    inference(avatar_split_clause,[],[f207,f119,f112,f105,f238])).

fof(f207,plain,
    ( r2_hidden(sK2(sK0),k1_relat_1(sK0))
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f206,f106])).

fof(f206,plain,
    ( r2_hidden(sK2(sK0),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f205,f120])).

fof(f205,plain,
    ( r2_hidden(sK2(sK0),k1_relat_1(sK0))
    | v2_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl5_2 ),
    inference(resolution,[],[f79,f113])).

fof(f79,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(sK2(X0),k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f204,plain,
    ( spl5_22
    | ~ spl5_0
    | ~ spl5_2
    | spl5_5 ),
    inference(avatar_split_clause,[],[f197,f119,f112,f105,f202])).

fof(f197,plain,
    ( r2_hidden(sK1(sK0),k1_relat_1(sK0))
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f196,f106])).

fof(f196,plain,
    ( r2_hidden(sK1(sK0),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f195,f120])).

fof(f195,plain,
    ( r2_hidden(sK1(sK0),k1_relat_1(sK0))
    | v2_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl5_2 ),
    inference(resolution,[],[f78,f113])).

fof(f78,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(sK1(X0),k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f190,plain,
    ( spl5_20
    | ~ spl5_0 ),
    inference(avatar_split_clause,[],[f184,f105,f188])).

fof(f184,plain,
    ( ! [X0] : k9_relat_1(sK0,k1_tarski(X0)) = k11_relat_1(sK0,X0)
    | ~ spl5_0 ),
    inference(resolution,[],[f75,f106])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_tarski(X1)) = k11_relat_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] : k9_relat_1(X0,k1_tarski(X1)) = k11_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k9_relat_1(X0,k1_tarski(X1)) = k11_relat_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t122_funct_1.p',d16_relat_1)).

fof(f172,plain,
    ( spl5_18
    | ~ spl5_0 ),
    inference(avatar_split_clause,[],[f161,f105,f170])).

fof(f161,plain,
    ( k9_relat_1(sK0,k1_xboole_0) = k1_xboole_0
    | ~ spl5_0 ),
    inference(resolution,[],[f74,f106])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_xboole_0) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t122_funct_1.p',t149_relat_1)).

fof(f160,plain,
    ( spl5_16
    | spl5_9 ),
    inference(avatar_split_clause,[],[f156,f133,f158])).

fof(f133,plain,
    ( spl5_9
  <=> ~ sP4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f156,plain,
    ( ! [X0] :
        ( ~ r1_subset_1(X0,X0)
        | v1_xboole_0(X0) )
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f99,f134])).

fof(f134,plain,
    ( ~ sP4
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f133])).

fof(f99,plain,(
    ! [X0] :
      ( ~ r1_subset_1(X0,X0)
      | v1_xboole_0(X0)
      | sP4 ) ),
    inference(cnf_transformation,[],[f99_D])).

fof(f99_D,plain,
    ( ! [X0] :
        ( ~ r1_subset_1(X0,X0)
        | v1_xboole_0(X0) )
  <=> ~ sP4 ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).

fof(f138,plain,
    ( ~ spl5_9
    | spl5_10 ),
    inference(avatar_split_clause,[],[f100,f136,f133])).

fof(f100,plain,(
    ! [X1] :
      ( v1_xboole_0(X1)
      | ~ sP4 ) ),
    inference(general_splitting,[],[f90,f99_D])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ r1_subset_1(X0,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_subset_1(X0,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_subset_1(X0,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ~ r1_subset_1(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t122_funct_1.p',irreflexivity_r1_subset_1)).

fof(f121,plain,(
    ~ spl5_5 ),
    inference(avatar_split_clause,[],[f70,f119])).

fof(f70,plain,(
    ~ v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f114,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f68,f112])).

fof(f68,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f107,plain,(
    spl5_0 ),
    inference(avatar_split_clause,[],[f67,f105])).

fof(f67,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f58])).
%------------------------------------------------------------------------------
