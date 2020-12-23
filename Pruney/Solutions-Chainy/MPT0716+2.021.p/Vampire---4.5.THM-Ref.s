%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 272 expanded)
%              Number of leaves         :   28 (  95 expanded)
%              Depth                    :   13
%              Number of atoms          :  399 ( 956 expanded)
%              Number of equality atoms :   35 (  62 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1953,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f62,f66,f95,f106,f114,f116,f147,f295,f354,f359,f513,f544,f549,f551,f581,f1786,f1818,f1952])).

fof(f1952,plain,
    ( ~ spl3_44
    | ~ spl3_57
    | ~ spl3_136 ),
    inference(avatar_contradiction_clause,[],[f1950])).

fof(f1950,plain,
    ( $false
    | ~ spl3_44
    | ~ spl3_57
    | ~ spl3_136 ),
    inference(resolution,[],[f1799,f502])).

fof(f502,plain,
    ( r1_tarski(sK2,sK2)
    | ~ spl3_44 ),
    inference(avatar_component_clause,[],[f501])).

fof(f501,plain,
    ( spl3_44
  <=> r1_tarski(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f1799,plain,
    ( ~ r1_tarski(sK2,sK2)
    | ~ spl3_57
    | ~ spl3_136 ),
    inference(superposition,[],[f580,f1785])).

fof(f1785,plain,
    ( sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1))
    | ~ spl3_136 ),
    inference(avatar_component_clause,[],[f1784])).

fof(f1784,plain,
    ( spl3_136
  <=> sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_136])])).

fof(f580,plain,
    ( ! [X0] : ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(k7_relat_1(sK0,X0),sK1)))
    | ~ spl3_57 ),
    inference(avatar_component_clause,[],[f579])).

fof(f579,plain,
    ( spl3_57
  <=> ! [X0] : ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(k7_relat_1(sK0,X0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).

fof(f1818,plain,
    ( ~ spl3_10
    | ~ spl3_7
    | spl3_44
    | ~ spl3_4
    | ~ spl3_136 ),
    inference(avatar_split_clause,[],[f1817,f1784,f81,f501,f91,f123])).

fof(f123,plain,
    ( spl3_10
  <=> v1_relat_1(k7_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f91,plain,
    ( spl3_7
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f81,plain,
    ( spl3_4
  <=> sK2 = k1_relat_1(k7_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f1817,plain,
    ( r1_tarski(sK2,sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ spl3_4
    | ~ spl3_136 ),
    inference(forward_demodulation,[],[f1803,f82])).

fof(f82,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK0,sK2))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f1803,plain,
    ( r1_tarski(sK2,k1_relat_1(k7_relat_1(sK0,sK2)))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ spl3_136 ),
    inference(superposition,[],[f40,f1785])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

fof(f1786,plain,
    ( ~ spl3_10
    | ~ spl3_7
    | spl3_136
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f1782,f81,f56,f1784,f91,f123])).

fof(f56,plain,
    ( spl3_2
  <=> r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f1782,plain,
    ( sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f1776,f82])).

fof(f1776,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | k1_relat_1(k7_relat_1(sK0,sK2)) = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1))
    | ~ spl3_2 ),
    inference(resolution,[],[f138,f57])).

fof(f57,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f138,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k9_relat_1(sK0,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k7_relat_1(sK0,X0))
      | k1_relat_1(k5_relat_1(k7_relat_1(sK0,X0),X1)) = k1_relat_1(k7_relat_1(sK0,X0)) ) ),
    inference(superposition,[],[f41,f71])).

fof(f71,plain,(
    ! [X6] : k2_relat_1(k7_relat_1(sK0,X6)) = k9_relat_1(sK0,X6) ),
    inference(resolution,[],[f45,f38])).

fof(f38,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <~> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <~> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
              <=> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <=> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

fof(f581,plain,
    ( ~ spl3_9
    | spl3_57
    | spl3_1 ),
    inference(avatar_split_clause,[],[f577,f53,f579,f112])).

fof(f112,plain,
    ( spl3_9
  <=> v1_relat_1(k5_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f53,plain,
    ( spl3_1
  <=> r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f577,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(k7_relat_1(sK0,X0),sK1)))
        | ~ v1_relat_1(k5_relat_1(sK0,sK1)) )
    | spl3_1 ),
    inference(forward_demodulation,[],[f574,f205])).

fof(f205,plain,(
    ! [X6] : k7_relat_1(k5_relat_1(sK0,sK1),X6) = k5_relat_1(k7_relat_1(sK0,X6),sK1) ),
    inference(resolution,[],[f99,f38])).

fof(f99,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X10)
      | k7_relat_1(k5_relat_1(X10,sK1),X11) = k5_relat_1(k7_relat_1(X10,X11),sK1) ) ),
    inference(resolution,[],[f47,f36])).

fof(f36,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).

fof(f574,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2,k1_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),X0)))
        | ~ v1_relat_1(k5_relat_1(sK0,sK1)) )
    | spl3_1 ),
    inference(resolution,[],[f573,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).

fof(f573,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(k5_relat_1(sK0,sK1)))
        | ~ r1_tarski(sK2,X0) )
    | spl3_1 ),
    inference(resolution,[],[f63,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f63,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f551,plain,(
    spl3_54 ),
    inference(avatar_contradiction_clause,[],[f550])).

fof(f550,plain,
    ( $false
    | spl3_54 ),
    inference(resolution,[],[f548,f39])).

fof(f39,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f548,plain,
    ( ~ v1_funct_1(sK0)
    | spl3_54 ),
    inference(avatar_component_clause,[],[f547])).

fof(f547,plain,
    ( spl3_54
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).

fof(f549,plain,
    ( ~ spl3_5
    | ~ spl3_54
    | spl3_45 ),
    inference(avatar_split_clause,[],[f545,f508,f547,f84])).

fof(f84,plain,
    ( spl3_5
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f508,plain,
    ( spl3_45
  <=> v1_funct_1(k7_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f545,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl3_45 ),
    inference(resolution,[],[f509,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

fof(f509,plain,
    ( ~ v1_funct_1(k7_relat_1(sK0,sK2))
    | spl3_45 ),
    inference(avatar_component_clause,[],[f508])).

fof(f544,plain,(
    spl3_46 ),
    inference(avatar_contradiction_clause,[],[f543])).

fof(f543,plain,
    ( $false
    | spl3_46 ),
    inference(resolution,[],[f512,f37])).

fof(f37,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f512,plain,
    ( ~ v1_funct_1(sK1)
    | spl3_46 ),
    inference(avatar_component_clause,[],[f511])).

fof(f511,plain,
    ( spl3_46
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f513,plain,
    ( ~ spl3_7
    | ~ spl3_45
    | ~ spl3_10
    | ~ spl3_46
    | spl3_2
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f506,f109,f81,f56,f511,f123,f508,f91])).

fof(f109,plain,
    ( spl3_8
  <=> sK2 = k1_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f506,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ v1_funct_1(k7_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK1)
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f505,f71])).

fof(f505,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ v1_funct_1(k7_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK1)
    | r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(trivial_inequality_removal,[],[f504])).

fof(f504,plain,
    ( sK2 != sK2
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ v1_funct_1(k7_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK1)
    | r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f492,f82])).

fof(f492,plain,
    ( sK2 != k1_relat_1(k7_relat_1(sK0,sK2))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ v1_funct_1(k7_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK1)
    | r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))
    | ~ spl3_8 ),
    inference(superposition,[],[f42,f472])).

fof(f472,plain,
    ( sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1))
    | ~ spl3_8 ),
    inference(backward_demodulation,[],[f110,f205])).

fof(f110,plain,
    ( sK2 = k1_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),sK2))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f109])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0))
           => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).

fof(f359,plain,
    ( spl3_4
    | ~ spl3_5
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f356,f60,f84,f81])).

fof(f60,plain,
    ( spl3_3
  <=> r1_tarski(sK2,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f356,plain,
    ( ~ v1_relat_1(sK0)
    | sK2 = k1_relat_1(k7_relat_1(sK0,sK2))
    | ~ spl3_3 ),
    inference(resolution,[],[f61,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f61,plain,
    ( r1_tarski(sK2,k1_relat_1(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f354,plain,
    ( ~ spl3_1
    | ~ spl3_16 ),
    inference(avatar_contradiction_clause,[],[f353])).

fof(f353,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_16 ),
    inference(resolution,[],[f340,f36])).

fof(f340,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl3_1
    | ~ spl3_16 ),
    inference(resolution,[],[f158,f54])).

fof(f54,plain,
    ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f158,plain,
    ( ! [X1] :
        ( ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,X1)))
        | ~ v1_relat_1(X1) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl3_16
  <=> ! [X1] :
        ( ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,X1)))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f295,plain,
    ( ~ spl3_5
    | spl3_16
    | spl3_3 ),
    inference(avatar_split_clause,[],[f292,f60,f157,f84])).

fof(f292,plain,
    ( ! [X1] :
        ( ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,X1)))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(sK0) )
    | spl3_3 ),
    inference(resolution,[],[f290,f40])).

fof(f290,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK0))
        | ~ r1_tarski(sK2,X0) )
    | spl3_3 ),
    inference(resolution,[],[f65,f51])).

fof(f65,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK0))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f147,plain,(
    spl3_10 ),
    inference(avatar_contradiction_clause,[],[f146])).

fof(f146,plain,
    ( $false
    | spl3_10 ),
    inference(resolution,[],[f145,f38])).

fof(f145,plain,
    ( ~ v1_relat_1(sK0)
    | spl3_10 ),
    inference(resolution,[],[f124,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f124,plain,
    ( ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f123])).

fof(f116,plain,
    ( ~ spl3_5
    | ~ spl3_7
    | spl3_9 ),
    inference(avatar_split_clause,[],[f115,f112,f91,f84])).

fof(f115,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | spl3_9 ),
    inference(resolution,[],[f113,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f113,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f112])).

fof(f114,plain,
    ( spl3_8
    | ~ spl3_9
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f107,f53,f112,f109])).

fof(f107,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | sK2 = k1_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),sK2))
    | ~ spl3_1 ),
    inference(resolution,[],[f54,f46])).

fof(f106,plain,(
    spl3_7 ),
    inference(avatar_contradiction_clause,[],[f105])).

fof(f105,plain,
    ( $false
    | spl3_7 ),
    inference(resolution,[],[f92,f36])).

fof(f92,plain,
    ( ~ v1_relat_1(sK1)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f91])).

fof(f95,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f94])).

fof(f94,plain,
    ( $false
    | spl3_5 ),
    inference(resolution,[],[f85,f38])).

fof(f85,plain,
    ( ~ v1_relat_1(sK0)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f84])).

fof(f66,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f33,f60,f56,f53])).

fof(f33,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK0))
    | ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f15])).

fof(f62,plain,
    ( spl3_1
    | spl3_3 ),
    inference(avatar_split_clause,[],[f34,f60,f53])).

fof(f34,plain,
    ( r1_tarski(sK2,k1_relat_1(sK0))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f15])).

fof(f58,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f35,f56,f53])).

fof(f35,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:38:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (12432)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.47  % (12452)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.20/0.47  % (12443)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.20/0.48  % (12440)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.49  % (12430)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.50  % (12431)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.50  % (12448)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.20/0.50  % (12438)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.20/0.50  % (12429)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.51  % (12428)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.51  % (12442)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.20/0.51  % (12449)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.51  % (12447)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.20/0.51  % (12446)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.20/0.52  % (12433)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.52  % (12436)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.20/0.52  % (12434)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.52  % (12439)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.52  % (12444)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.20/0.52  % (12437)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.53  % (12451)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.20/0.54  % (12440)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % (12450)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.55  % (12441)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f1953,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(avatar_sat_refutation,[],[f58,f62,f66,f95,f106,f114,f116,f147,f295,f354,f359,f513,f544,f549,f551,f581,f1786,f1818,f1952])).
% 0.20/0.55  fof(f1952,plain,(
% 0.20/0.55    ~spl3_44 | ~spl3_57 | ~spl3_136),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f1950])).
% 0.20/0.55  fof(f1950,plain,(
% 0.20/0.55    $false | (~spl3_44 | ~spl3_57 | ~spl3_136)),
% 0.20/0.55    inference(resolution,[],[f1799,f502])).
% 0.20/0.55  fof(f502,plain,(
% 0.20/0.55    r1_tarski(sK2,sK2) | ~spl3_44),
% 0.20/0.55    inference(avatar_component_clause,[],[f501])).
% 0.20/0.55  fof(f501,plain,(
% 0.20/0.55    spl3_44 <=> r1_tarski(sK2,sK2)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 0.20/0.55  fof(f1799,plain,(
% 0.20/0.55    ~r1_tarski(sK2,sK2) | (~spl3_57 | ~spl3_136)),
% 0.20/0.55    inference(superposition,[],[f580,f1785])).
% 0.20/0.55  fof(f1785,plain,(
% 0.20/0.55    sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) | ~spl3_136),
% 0.20/0.55    inference(avatar_component_clause,[],[f1784])).
% 0.20/0.55  fof(f1784,plain,(
% 0.20/0.55    spl3_136 <=> sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_136])])).
% 0.20/0.55  fof(f580,plain,(
% 0.20/0.55    ( ! [X0] : (~r1_tarski(sK2,k1_relat_1(k5_relat_1(k7_relat_1(sK0,X0),sK1)))) ) | ~spl3_57),
% 0.20/0.55    inference(avatar_component_clause,[],[f579])).
% 0.20/0.55  fof(f579,plain,(
% 0.20/0.55    spl3_57 <=> ! [X0] : ~r1_tarski(sK2,k1_relat_1(k5_relat_1(k7_relat_1(sK0,X0),sK1)))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).
% 0.20/0.55  fof(f1818,plain,(
% 0.20/0.55    ~spl3_10 | ~spl3_7 | spl3_44 | ~spl3_4 | ~spl3_136),
% 0.20/0.55    inference(avatar_split_clause,[],[f1817,f1784,f81,f501,f91,f123])).
% 0.20/0.55  fof(f123,plain,(
% 0.20/0.55    spl3_10 <=> v1_relat_1(k7_relat_1(sK0,sK2))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.55  fof(f91,plain,(
% 0.20/0.55    spl3_7 <=> v1_relat_1(sK1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.55  fof(f81,plain,(
% 0.20/0.55    spl3_4 <=> sK2 = k1_relat_1(k7_relat_1(sK0,sK2))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.55  fof(f1817,plain,(
% 0.20/0.55    r1_tarski(sK2,sK2) | ~v1_relat_1(sK1) | ~v1_relat_1(k7_relat_1(sK0,sK2)) | (~spl3_4 | ~spl3_136)),
% 0.20/0.55    inference(forward_demodulation,[],[f1803,f82])).
% 0.20/0.55  fof(f82,plain,(
% 0.20/0.55    sK2 = k1_relat_1(k7_relat_1(sK0,sK2)) | ~spl3_4),
% 0.20/0.55    inference(avatar_component_clause,[],[f81])).
% 0.20/0.55  fof(f1803,plain,(
% 0.20/0.55    r1_tarski(sK2,k1_relat_1(k7_relat_1(sK0,sK2))) | ~v1_relat_1(sK1) | ~v1_relat_1(k7_relat_1(sK0,sK2)) | ~spl3_136),
% 0.20/0.55    inference(superposition,[],[f40,f1785])).
% 0.20/0.55  fof(f40,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f16])).
% 0.20/0.55  fof(f16,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f6])).
% 0.20/0.55  fof(f6,axiom,(
% 0.20/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).
% 0.20/0.55  fof(f1786,plain,(
% 0.20/0.55    ~spl3_10 | ~spl3_7 | spl3_136 | ~spl3_2 | ~spl3_4),
% 0.20/0.55    inference(avatar_split_clause,[],[f1782,f81,f56,f1784,f91,f123])).
% 0.20/0.55  fof(f56,plain,(
% 0.20/0.55    spl3_2 <=> r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.55  fof(f1782,plain,(
% 0.20/0.55    sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) | ~v1_relat_1(sK1) | ~v1_relat_1(k7_relat_1(sK0,sK2)) | (~spl3_2 | ~spl3_4)),
% 0.20/0.55    inference(forward_demodulation,[],[f1776,f82])).
% 0.20/0.55  fof(f1776,plain,(
% 0.20/0.55    ~v1_relat_1(sK1) | ~v1_relat_1(k7_relat_1(sK0,sK2)) | k1_relat_1(k7_relat_1(sK0,sK2)) = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) | ~spl3_2),
% 0.20/0.55    inference(resolution,[],[f138,f57])).
% 0.20/0.55  fof(f57,plain,(
% 0.20/0.55    r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~spl3_2),
% 0.20/0.55    inference(avatar_component_clause,[],[f56])).
% 0.20/0.55  fof(f138,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r1_tarski(k9_relat_1(sK0,X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(k7_relat_1(sK0,X0)) | k1_relat_1(k5_relat_1(k7_relat_1(sK0,X0),X1)) = k1_relat_1(k7_relat_1(sK0,X0))) )),
% 0.20/0.55    inference(superposition,[],[f41,f71])).
% 0.20/0.55  fof(f71,plain,(
% 0.20/0.55    ( ! [X6] : (k2_relat_1(k7_relat_1(sK0,X6)) = k9_relat_1(sK0,X6)) )),
% 0.20/0.55    inference(resolution,[],[f45,f38])).
% 0.20/0.55  fof(f38,plain,(
% 0.20/0.55    v1_relat_1(sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f15])).
% 0.20/0.55  fof(f15,plain,(
% 0.20/0.55    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.20/0.55    inference(flattening,[],[f14])).
% 0.20/0.55  fof(f14,plain,(
% 0.20/0.55    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f13])).
% 0.20/0.55  fof(f13,negated_conjecture,(
% 0.20/0.55    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 0.20/0.55    inference(negated_conjecture,[],[f12])).
% 0.20/0.55  fof(f12,conjecture,(
% 0.20/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_1)).
% 0.20/0.55  fof(f45,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f23])).
% 0.20/0.55  fof(f23,plain,(
% 0.20/0.55    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.55    inference(ennf_transformation,[],[f5])).
% 0.20/0.55  fof(f5,axiom,(
% 0.20/0.55    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.20/0.55  fof(f41,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f18])).
% 0.20/0.55  fof(f18,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.55    inference(flattening,[],[f17])).
% 0.20/0.55  fof(f17,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : ((k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f7])).
% 0.20/0.55  fof(f7,axiom,(
% 0.20/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).
% 0.20/0.55  fof(f581,plain,(
% 0.20/0.55    ~spl3_9 | spl3_57 | spl3_1),
% 0.20/0.55    inference(avatar_split_clause,[],[f577,f53,f579,f112])).
% 0.20/0.55  fof(f112,plain,(
% 0.20/0.55    spl3_9 <=> v1_relat_1(k5_relat_1(sK0,sK1))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.55  fof(f53,plain,(
% 0.20/0.55    spl3_1 <=> r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.55  fof(f577,plain,(
% 0.20/0.55    ( ! [X0] : (~r1_tarski(sK2,k1_relat_1(k5_relat_1(k7_relat_1(sK0,X0),sK1))) | ~v1_relat_1(k5_relat_1(sK0,sK1))) ) | spl3_1),
% 0.20/0.55    inference(forward_demodulation,[],[f574,f205])).
% 0.20/0.55  fof(f205,plain,(
% 0.20/0.55    ( ! [X6] : (k7_relat_1(k5_relat_1(sK0,sK1),X6) = k5_relat_1(k7_relat_1(sK0,X6),sK1)) )),
% 0.20/0.55    inference(resolution,[],[f99,f38])).
% 0.20/0.55  fof(f99,plain,(
% 0.20/0.55    ( ! [X10,X11] : (~v1_relat_1(X10) | k7_relat_1(k5_relat_1(X10,sK1),X11) = k5_relat_1(k7_relat_1(X10,X11),sK1)) )),
% 0.20/0.55    inference(resolution,[],[f47,f36])).
% 0.20/0.55  fof(f36,plain,(
% 0.20/0.55    v1_relat_1(sK1)),
% 0.20/0.55    inference(cnf_transformation,[],[f15])).
% 0.20/0.55  fof(f47,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_relat_1(X1) | k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f26])).
% 0.20/0.55  fof(f26,plain,(
% 0.20/0.55    ! [X0,X1] : (! [X2] : (k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.55    inference(ennf_transformation,[],[f4])).
% 0.20/0.55  fof(f4,axiom,(
% 0.20/0.55    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).
% 0.20/0.55  fof(f574,plain,(
% 0.20/0.55    ( ! [X0] : (~r1_tarski(sK2,k1_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),X0))) | ~v1_relat_1(k5_relat_1(sK0,sK1))) ) | spl3_1),
% 0.20/0.55    inference(resolution,[],[f573,f44])).
% 0.20/0.55  fof(f44,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f22])).
% 0.20/0.55  fof(f22,plain,(
% 0.20/0.55    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.55    inference(ennf_transformation,[],[f8])).
% 0.20/0.55  fof(f8,axiom,(
% 0.20/0.55    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).
% 0.20/0.55  fof(f573,plain,(
% 0.20/0.55    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(k5_relat_1(sK0,sK1))) | ~r1_tarski(sK2,X0)) ) | spl3_1),
% 0.20/0.55    inference(resolution,[],[f63,f51])).
% 0.20/0.55  fof(f51,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f32])).
% 0.20/0.55  fof(f32,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.55    inference(flattening,[],[f31])).
% 0.20/0.55  fof(f31,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.55    inference(ennf_transformation,[],[f1])).
% 0.20/0.55  fof(f1,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.55  fof(f63,plain,(
% 0.20/0.55    ~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) | spl3_1),
% 0.20/0.55    inference(avatar_component_clause,[],[f53])).
% 0.20/0.55  fof(f551,plain,(
% 0.20/0.55    spl3_54),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f550])).
% 0.20/0.55  fof(f550,plain,(
% 0.20/0.55    $false | spl3_54),
% 0.20/0.55    inference(resolution,[],[f548,f39])).
% 0.20/0.55  fof(f39,plain,(
% 0.20/0.55    v1_funct_1(sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f15])).
% 0.20/0.55  fof(f548,plain,(
% 0.20/0.55    ~v1_funct_1(sK0) | spl3_54),
% 0.20/0.55    inference(avatar_component_clause,[],[f547])).
% 0.20/0.55  fof(f547,plain,(
% 0.20/0.55    spl3_54 <=> v1_funct_1(sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).
% 0.20/0.55  fof(f549,plain,(
% 0.20/0.55    ~spl3_5 | ~spl3_54 | spl3_45),
% 0.20/0.55    inference(avatar_split_clause,[],[f545,f508,f547,f84])).
% 0.20/0.55  fof(f84,plain,(
% 0.20/0.55    spl3_5 <=> v1_relat_1(sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.55  fof(f508,plain,(
% 0.20/0.55    spl3_45 <=> v1_funct_1(k7_relat_1(sK0,sK2))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 0.20/0.55  fof(f545,plain,(
% 0.20/0.55    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl3_45),
% 0.20/0.55    inference(resolution,[],[f509,f49])).
% 0.20/0.55  fof(f49,plain,(
% 0.20/0.55    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f28])).
% 0.20/0.55  fof(f28,plain,(
% 0.20/0.55    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.55    inference(flattening,[],[f27])).
% 0.20/0.55  fof(f27,plain,(
% 0.20/0.55    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f10])).
% 0.20/0.55  fof(f10,axiom,(
% 0.20/0.55    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).
% 0.20/0.55  fof(f509,plain,(
% 0.20/0.55    ~v1_funct_1(k7_relat_1(sK0,sK2)) | spl3_45),
% 0.20/0.55    inference(avatar_component_clause,[],[f508])).
% 0.20/0.55  fof(f544,plain,(
% 0.20/0.55    spl3_46),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f543])).
% 0.20/0.55  fof(f543,plain,(
% 0.20/0.55    $false | spl3_46),
% 0.20/0.55    inference(resolution,[],[f512,f37])).
% 0.20/0.55  fof(f37,plain,(
% 0.20/0.55    v1_funct_1(sK1)),
% 0.20/0.55    inference(cnf_transformation,[],[f15])).
% 0.20/0.55  fof(f512,plain,(
% 0.20/0.55    ~v1_funct_1(sK1) | spl3_46),
% 0.20/0.55    inference(avatar_component_clause,[],[f511])).
% 0.20/0.55  fof(f511,plain,(
% 0.20/0.55    spl3_46 <=> v1_funct_1(sK1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 0.20/0.55  fof(f513,plain,(
% 0.20/0.55    ~spl3_7 | ~spl3_45 | ~spl3_10 | ~spl3_46 | spl3_2 | ~spl3_4 | ~spl3_8),
% 0.20/0.55    inference(avatar_split_clause,[],[f506,f109,f81,f56,f511,f123,f508,f91])).
% 0.20/0.55  fof(f109,plain,(
% 0.20/0.55    spl3_8 <=> sK2 = k1_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),sK2))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.55  fof(f506,plain,(
% 0.20/0.55    r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(k7_relat_1(sK0,sK2)) | ~v1_funct_1(k7_relat_1(sK0,sK2)) | ~v1_relat_1(sK1) | (~spl3_4 | ~spl3_8)),
% 0.20/0.55    inference(forward_demodulation,[],[f505,f71])).
% 0.20/0.55  fof(f505,plain,(
% 0.20/0.55    ~v1_funct_1(sK1) | ~v1_relat_1(k7_relat_1(sK0,sK2)) | ~v1_funct_1(k7_relat_1(sK0,sK2)) | ~v1_relat_1(sK1) | r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) | (~spl3_4 | ~spl3_8)),
% 0.20/0.55    inference(trivial_inequality_removal,[],[f504])).
% 0.20/0.55  fof(f504,plain,(
% 0.20/0.55    sK2 != sK2 | ~v1_funct_1(sK1) | ~v1_relat_1(k7_relat_1(sK0,sK2)) | ~v1_funct_1(k7_relat_1(sK0,sK2)) | ~v1_relat_1(sK1) | r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) | (~spl3_4 | ~spl3_8)),
% 0.20/0.55    inference(forward_demodulation,[],[f492,f82])).
% 0.20/0.55  fof(f492,plain,(
% 0.20/0.55    sK2 != k1_relat_1(k7_relat_1(sK0,sK2)) | ~v1_funct_1(sK1) | ~v1_relat_1(k7_relat_1(sK0,sK2)) | ~v1_funct_1(k7_relat_1(sK0,sK2)) | ~v1_relat_1(sK1) | r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) | ~spl3_8),
% 0.20/0.55    inference(superposition,[],[f42,f472])).
% 0.20/0.55  fof(f472,plain,(
% 0.20/0.55    sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) | ~spl3_8),
% 0.20/0.55    inference(backward_demodulation,[],[f110,f205])).
% 0.20/0.55  fof(f110,plain,(
% 0.20/0.55    sK2 = k1_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),sK2)) | ~spl3_8),
% 0.20/0.55    inference(avatar_component_clause,[],[f109])).
% 0.20/0.55  fof(f42,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | r1_tarski(k2_relat_1(X1),k1_relat_1(X0))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f20])).
% 0.20/0.55  fof(f20,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.55    inference(flattening,[],[f19])).
% 0.20/0.55  fof(f19,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f11])).
% 0.20/0.55  fof(f11,axiom,(
% 0.20/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0)) => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).
% 0.20/0.55  fof(f359,plain,(
% 0.20/0.55    spl3_4 | ~spl3_5 | ~spl3_3),
% 0.20/0.55    inference(avatar_split_clause,[],[f356,f60,f84,f81])).
% 0.20/0.55  fof(f60,plain,(
% 0.20/0.55    spl3_3 <=> r1_tarski(sK2,k1_relat_1(sK0))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.55  fof(f356,plain,(
% 0.20/0.55    ~v1_relat_1(sK0) | sK2 = k1_relat_1(k7_relat_1(sK0,sK2)) | ~spl3_3),
% 0.20/0.55    inference(resolution,[],[f61,f46])).
% 0.20/0.55  fof(f46,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f25])).
% 0.20/0.55  fof(f25,plain,(
% 0.20/0.55    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.55    inference(flattening,[],[f24])).
% 0.20/0.55  fof(f24,plain,(
% 0.20/0.55    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.20/0.55    inference(ennf_transformation,[],[f9])).
% 0.20/0.55  fof(f9,axiom,(
% 0.20/0.55    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 0.20/0.55  fof(f61,plain,(
% 0.20/0.55    r1_tarski(sK2,k1_relat_1(sK0)) | ~spl3_3),
% 0.20/0.55    inference(avatar_component_clause,[],[f60])).
% 0.20/0.55  fof(f354,plain,(
% 0.20/0.55    ~spl3_1 | ~spl3_16),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f353])).
% 0.20/0.55  fof(f353,plain,(
% 0.20/0.55    $false | (~spl3_1 | ~spl3_16)),
% 0.20/0.55    inference(resolution,[],[f340,f36])).
% 0.20/0.55  fof(f340,plain,(
% 0.20/0.55    ~v1_relat_1(sK1) | (~spl3_1 | ~spl3_16)),
% 0.20/0.55    inference(resolution,[],[f158,f54])).
% 0.20/0.55  fof(f54,plain,(
% 0.20/0.55    r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) | ~spl3_1),
% 0.20/0.55    inference(avatar_component_clause,[],[f53])).
% 0.20/0.55  fof(f158,plain,(
% 0.20/0.55    ( ! [X1] : (~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,X1))) | ~v1_relat_1(X1)) ) | ~spl3_16),
% 0.20/0.55    inference(avatar_component_clause,[],[f157])).
% 0.20/0.55  fof(f157,plain,(
% 0.20/0.55    spl3_16 <=> ! [X1] : (~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,X1))) | ~v1_relat_1(X1))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.55  fof(f295,plain,(
% 0.20/0.55    ~spl3_5 | spl3_16 | spl3_3),
% 0.20/0.55    inference(avatar_split_clause,[],[f292,f60,f157,f84])).
% 0.20/0.55  fof(f292,plain,(
% 0.20/0.55    ( ! [X1] : (~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,X1))) | ~v1_relat_1(X1) | ~v1_relat_1(sK0)) ) | spl3_3),
% 0.20/0.55    inference(resolution,[],[f290,f40])).
% 0.20/0.55  fof(f290,plain,(
% 0.20/0.55    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK0)) | ~r1_tarski(sK2,X0)) ) | spl3_3),
% 0.20/0.55    inference(resolution,[],[f65,f51])).
% 0.20/0.55  fof(f65,plain,(
% 0.20/0.55    ~r1_tarski(sK2,k1_relat_1(sK0)) | spl3_3),
% 0.20/0.55    inference(avatar_component_clause,[],[f60])).
% 0.20/0.55  fof(f147,plain,(
% 0.20/0.55    spl3_10),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f146])).
% 0.20/0.55  fof(f146,plain,(
% 0.20/0.55    $false | spl3_10),
% 0.20/0.55    inference(resolution,[],[f145,f38])).
% 0.20/0.55  fof(f145,plain,(
% 0.20/0.55    ~v1_relat_1(sK0) | spl3_10),
% 0.20/0.55    inference(resolution,[],[f124,f43])).
% 0.20/0.55  fof(f43,plain,(
% 0.20/0.55    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f21])).
% 0.20/0.55  fof(f21,plain,(
% 0.20/0.55    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f3])).
% 0.20/0.55  fof(f3,axiom,(
% 0.20/0.55    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.20/0.55  fof(f124,plain,(
% 0.20/0.55    ~v1_relat_1(k7_relat_1(sK0,sK2)) | spl3_10),
% 0.20/0.55    inference(avatar_component_clause,[],[f123])).
% 0.20/0.55  fof(f116,plain,(
% 0.20/0.55    ~spl3_5 | ~spl3_7 | spl3_9),
% 0.20/0.55    inference(avatar_split_clause,[],[f115,f112,f91,f84])).
% 0.20/0.55  fof(f115,plain,(
% 0.20/0.55    ~v1_relat_1(sK1) | ~v1_relat_1(sK0) | spl3_9),
% 0.20/0.55    inference(resolution,[],[f113,f50])).
% 0.20/0.55  fof(f50,plain,(
% 0.20/0.55    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f30])).
% 0.20/0.55  fof(f30,plain,(
% 0.20/0.55    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.55    inference(flattening,[],[f29])).
% 0.20/0.55  fof(f29,plain,(
% 0.20/0.55    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f2])).
% 0.20/0.55  fof(f2,axiom,(
% 0.20/0.55    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.20/0.55  fof(f113,plain,(
% 0.20/0.55    ~v1_relat_1(k5_relat_1(sK0,sK1)) | spl3_9),
% 0.20/0.55    inference(avatar_component_clause,[],[f112])).
% 0.20/0.55  fof(f114,plain,(
% 0.20/0.55    spl3_8 | ~spl3_9 | ~spl3_1),
% 0.20/0.55    inference(avatar_split_clause,[],[f107,f53,f112,f109])).
% 0.20/0.55  fof(f107,plain,(
% 0.20/0.55    ~v1_relat_1(k5_relat_1(sK0,sK1)) | sK2 = k1_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),sK2)) | ~spl3_1),
% 0.20/0.55    inference(resolution,[],[f54,f46])).
% 0.20/0.55  fof(f106,plain,(
% 0.20/0.55    spl3_7),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f105])).
% 0.20/0.55  fof(f105,plain,(
% 0.20/0.55    $false | spl3_7),
% 0.20/0.55    inference(resolution,[],[f92,f36])).
% 0.20/0.55  fof(f92,plain,(
% 0.20/0.55    ~v1_relat_1(sK1) | spl3_7),
% 0.20/0.55    inference(avatar_component_clause,[],[f91])).
% 0.20/0.55  fof(f95,plain,(
% 0.20/0.55    spl3_5),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f94])).
% 0.20/0.55  fof(f94,plain,(
% 0.20/0.55    $false | spl3_5),
% 0.20/0.55    inference(resolution,[],[f85,f38])).
% 0.20/0.55  fof(f85,plain,(
% 0.20/0.55    ~v1_relat_1(sK0) | spl3_5),
% 0.20/0.55    inference(avatar_component_clause,[],[f84])).
% 0.20/0.55  fof(f66,plain,(
% 0.20/0.55    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 0.20/0.55    inference(avatar_split_clause,[],[f33,f60,f56,f53])).
% 0.20/0.55  fof(f33,plain,(
% 0.20/0.55    ~r1_tarski(sK2,k1_relat_1(sK0)) | ~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 0.20/0.55    inference(cnf_transformation,[],[f15])).
% 0.20/0.55  fof(f62,plain,(
% 0.20/0.55    spl3_1 | spl3_3),
% 0.20/0.55    inference(avatar_split_clause,[],[f34,f60,f53])).
% 0.20/0.55  fof(f34,plain,(
% 0.20/0.55    r1_tarski(sK2,k1_relat_1(sK0)) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 0.20/0.55    inference(cnf_transformation,[],[f15])).
% 0.20/0.55  fof(f58,plain,(
% 0.20/0.55    spl3_1 | spl3_2),
% 0.20/0.55    inference(avatar_split_clause,[],[f35,f56,f53])).
% 0.20/0.55  fof(f35,plain,(
% 0.20/0.55    r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 0.20/0.55    inference(cnf_transformation,[],[f15])).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (12440)------------------------------
% 0.20/0.55  % (12440)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (12440)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (12440)Memory used [KB]: 12025
% 0.20/0.55  % (12440)Time elapsed: 0.119 s
% 0.20/0.55  % (12440)------------------------------
% 0.20/0.55  % (12440)------------------------------
% 0.20/0.55  % (12424)Success in time 0.197 s
%------------------------------------------------------------------------------
