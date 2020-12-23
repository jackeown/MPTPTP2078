%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t147_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:16 EDT 2019

% Result     : Theorem 7.00s
% Output     : Refutation 7.00s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 283 expanded)
%              Number of leaves         :   12 (  68 expanded)
%              Depth                    :   14
%              Number of atoms          :  246 ( 938 expanded)
%              Number of equality atoms :   35 ( 176 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20150,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f172,f342,f727,f2256,f6466,f20148])).

fof(f20148,plain,(
    ~ spl11_84 ),
    inference(avatar_contradiction_clause,[],[f20140])).

fof(f20140,plain,
    ( $false
    | ~ spl11_84 ),
    inference(unit_resulting_resolution,[],[f90,f156,f20119,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t147_funct_1.p',d3_tarski)).

fof(f20119,plain,
    ( ~ r2_hidden(sK6(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))),sK0)
    | ~ spl11_84 ),
    inference(forward_demodulation,[],[f20112,f932])).

fof(f932,plain,(
    k1_funct_1(sK1,sK8(sK1,sK6(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))))) = sK6(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))) ),
    inference(unit_resulting_resolution,[],[f49,f48,f394,f101])).

fof(f101,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_funct_1(X0,sK8(X0,X2)) = X2
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK8(X0,X2)) = X2
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/funct_1__t147_funct_1.p',d5_funct_1)).

fof(f394,plain,(
    r2_hidden(sK6(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f50,f156,f73])).

fof(f50,plain,(
    r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(X0,k2_relat_1(X1))
         => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t147_funct_1.p',t147_funct_1)).

fof(f48,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f49,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f20112,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK8(sK1,sK6(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))))),sK0)
    | ~ spl11_84 ),
    inference(unit_resulting_resolution,[],[f49,f48,f931,f6523,f96])).

fof(f96,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(k1_funct_1(X0,X3),X1)
      | r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(k1_funct_1(X0,X3),X1)
      | r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t147_funct_1.p',d13_funct_1)).

fof(f6523,plain,
    ( ~ r2_hidden(sK8(sK1,sK6(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))),k10_relat_1(sK1,sK0))
    | ~ spl11_84 ),
    inference(unit_resulting_resolution,[],[f394,f157,f6465])).

fof(f6465,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(sK8(sK1,X3),X4)
        | r2_hidden(X3,k9_relat_1(sK1,X4))
        | ~ r2_hidden(X3,k2_relat_1(sK1)) )
    | ~ spl11_84 ),
    inference(avatar_component_clause,[],[f6464])).

fof(f6464,plain,
    ( spl11_84
  <=> ! [X3,X4] :
        ( ~ r2_hidden(X3,k2_relat_1(sK1))
        | r2_hidden(X3,k9_relat_1(sK1,X4))
        | ~ r2_hidden(sK8(sK1,X3),X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_84])])).

fof(f157,plain,(
    ~ r2_hidden(sK6(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k9_relat_1(sK1,k10_relat_1(sK1,sK0))) ),
    inference(unit_resulting_resolution,[],[f124,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f124,plain,(
    ~ r1_tarski(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))) ),
    inference(unit_resulting_resolution,[],[f51,f103,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t147_funct_1.p',d10_xboole_0)).

fof(f103,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) ),
    inference(unit_resulting_resolution,[],[f48,f49,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t147_funct_1.p',t145_funct_1)).

fof(f51,plain,(
    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != sK0 ),
    inference(cnf_transformation,[],[f29])).

fof(f931,plain,(
    r2_hidden(sK8(sK1,sK6(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))),k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f49,f48,f394,f102])).

fof(f102,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK8(X0,X2),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK8(X0,X2),k1_relat_1(X0))
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f156,plain,(
    r2_hidden(sK6(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))),sK0) ),
    inference(unit_resulting_resolution,[],[f124,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f90,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f6466,plain,
    ( ~ spl11_7
    | ~ spl11_31
    | spl11_84
    | ~ spl11_54 ),
    inference(avatar_split_clause,[],[f2292,f2254,f6464,f694,f166])).

fof(f166,plain,
    ( spl11_7
  <=> ~ v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f694,plain,
    ( spl11_31
  <=> ~ v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_31])])).

fof(f2254,plain,
    ( spl11_54
  <=> ! [X9,X8] :
        ( r2_hidden(X8,k9_relat_1(sK1,X9))
        | ~ r2_hidden(X8,k2_relat_1(sK1))
        | ~ r2_hidden(sK8(sK1,X8),X9)
        | ~ r2_hidden(sK8(sK1,X8),k1_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_54])])).

fof(f2292,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(X3,k2_relat_1(sK1))
        | ~ r2_hidden(sK8(sK1,X3),X4)
        | r2_hidden(X3,k9_relat_1(sK1,X4))
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl11_54 ),
    inference(duplicate_literal_removal,[],[f2289])).

fof(f2289,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(X3,k2_relat_1(sK1))
        | ~ r2_hidden(sK8(sK1,X3),X4)
        | r2_hidden(X3,k9_relat_1(sK1,X4))
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(X3,k2_relat_1(sK1)) )
    | ~ spl11_54 ),
    inference(resolution,[],[f2255,f102])).

fof(f2255,plain,
    ( ! [X8,X9] :
        ( ~ r2_hidden(sK8(sK1,X8),k1_relat_1(sK1))
        | ~ r2_hidden(X8,k2_relat_1(sK1))
        | ~ r2_hidden(sK8(sK1,X8),X9)
        | r2_hidden(X8,k9_relat_1(sK1,X9)) )
    | ~ spl11_54 ),
    inference(avatar_component_clause,[],[f2254])).

fof(f2256,plain,
    ( ~ spl11_7
    | ~ spl11_31
    | spl11_54
    | ~ spl11_16 ),
    inference(avatar_split_clause,[],[f378,f340,f2254,f694,f166])).

fof(f340,plain,
    ( spl11_16
  <=> ! [X20] :
        ( k1_funct_1(sK1,sK8(sK1,X20)) = X20
        | ~ r2_hidden(X20,k2_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).

fof(f378,plain,
    ( ! [X8,X9] :
        ( r2_hidden(X8,k9_relat_1(sK1,X9))
        | ~ v1_funct_1(sK1)
        | ~ r2_hidden(sK8(sK1,X8),k1_relat_1(sK1))
        | ~ r2_hidden(sK8(sK1,X8),X9)
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(X8,k2_relat_1(sK1)) )
    | ~ spl11_16 ),
    inference(superposition,[],[f92,f341])).

fof(f341,plain,
    ( ! [X20] :
        ( k1_funct_1(sK1,sK8(sK1,X20)) = X20
        | ~ r2_hidden(X20,k2_relat_1(sK1)) )
    | ~ spl11_16 ),
    inference(avatar_component_clause,[],[f340])).

fof(f92,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X4),k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,X1)
      | r2_hidden(k1_funct_1(X0,X4),X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,X1)
      | k1_funct_1(X0,X4) != X3
      | r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t147_funct_1.p',d12_funct_1)).

fof(f727,plain,(
    spl11_31 ),
    inference(avatar_contradiction_clause,[],[f724])).

fof(f724,plain,
    ( $false
    | ~ spl11_31 ),
    inference(unit_resulting_resolution,[],[f49,f695])).

fof(f695,plain,
    ( ~ v1_funct_1(sK1)
    | ~ spl11_31 ),
    inference(avatar_component_clause,[],[f694])).

fof(f342,plain,
    ( spl11_16
    | ~ spl11_7 ),
    inference(avatar_split_clause,[],[f115,f166,f340])).

fof(f115,plain,(
    ! [X20] :
      ( ~ v1_relat_1(sK1)
      | k1_funct_1(sK1,sK8(sK1,X20)) = X20
      | ~ r2_hidden(X20,k2_relat_1(sK1)) ) ),
    inference(resolution,[],[f49,f101])).

fof(f172,plain,(
    spl11_7 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | ~ spl11_7 ),
    inference(unit_resulting_resolution,[],[f48,f167])).

fof(f167,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f166])).
%------------------------------------------------------------------------------
