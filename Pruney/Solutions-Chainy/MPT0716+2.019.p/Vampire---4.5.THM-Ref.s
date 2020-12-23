%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:51 EST 2020

% Result     : Theorem 2.14s
% Output     : Refutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 240 expanded)
%              Number of leaves         :   27 (  83 expanded)
%              Depth                    :   13
%              Number of atoms          :  360 ( 846 expanded)
%              Number of equality atoms :   39 (  60 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1495,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f64,f68,f101,f112,f121,f123,f152,f190,f193,f388,f420,f443,f451,f453,f1356,f1493])).

fof(f1493,plain,
    ( spl3_1
    | ~ spl3_34
    | ~ spl3_96 ),
    inference(avatar_contradiction_clause,[],[f1490])).

fof(f1490,plain,
    ( $false
    | spl3_1
    | ~ spl3_34
    | ~ spl3_96 ),
    inference(resolution,[],[f1388,f65])).

fof(f65,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl3_1
  <=> r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f1388,plain,
    ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl3_34
    | ~ spl3_96 ),
    inference(superposition,[],[f387,f1355])).

fof(f1355,plain,
    ( sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1))
    | ~ spl3_96 ),
    inference(avatar_component_clause,[],[f1354])).

fof(f1354,plain,
    ( spl3_96
  <=> sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_96])])).

fof(f387,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k5_relat_1(k7_relat_1(sK0,X0),sK1)),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f386])).

fof(f386,plain,
    ( spl3_34
  <=> ! [X0] : r1_tarski(k1_relat_1(k5_relat_1(k7_relat_1(sK0,X0),sK1)),k1_relat_1(k5_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f1356,plain,
    ( ~ spl3_10
    | ~ spl3_7
    | spl3_96
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f1352,f87,f58,f1354,f97,f129])).

fof(f129,plain,
    ( spl3_10
  <=> v1_relat_1(k7_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f97,plain,
    ( spl3_7
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f58,plain,
    ( spl3_2
  <=> r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f87,plain,
    ( spl3_4
  <=> sK2 = k1_relat_1(k7_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f1352,plain,
    ( sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f1342,f88])).

fof(f88,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK0,sK2))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f1342,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | k1_relat_1(k7_relat_1(sK0,sK2)) = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1))
    | ~ spl3_2 ),
    inference(resolution,[],[f143,f59])).

fof(f59,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f143,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k9_relat_1(sK0,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k7_relat_1(sK0,X0))
      | k1_relat_1(k5_relat_1(k7_relat_1(sK0,X0),X1)) = k1_relat_1(k7_relat_1(sK0,X0)) ) ),
    inference(superposition,[],[f42,f77])).

fof(f77,plain,(
    ! [X6] : k2_relat_1(k7_relat_1(sK0,X6)) = k9_relat_1(sK0,X6) ),
    inference(resolution,[],[f46,f39])).

fof(f39,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

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
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

fof(f453,plain,(
    spl3_46 ),
    inference(avatar_contradiction_clause,[],[f452])).

fof(f452,plain,
    ( $false
    | spl3_46 ),
    inference(resolution,[],[f450,f40])).

fof(f40,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f450,plain,
    ( ~ v1_funct_1(sK0)
    | spl3_46 ),
    inference(avatar_component_clause,[],[f449])).

fof(f449,plain,
    ( spl3_46
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f451,plain,
    ( ~ spl3_5
    | ~ spl3_46
    | spl3_39 ),
    inference(avatar_split_clause,[],[f447,f415,f449,f90])).

fof(f90,plain,
    ( spl3_5
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f415,plain,
    ( spl3_39
  <=> v1_funct_1(k7_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f447,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl3_39 ),
    inference(resolution,[],[f416,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

fof(f416,plain,
    ( ~ v1_funct_1(k7_relat_1(sK0,sK2))
    | spl3_39 ),
    inference(avatar_component_clause,[],[f415])).

fof(f443,plain,(
    spl3_40 ),
    inference(avatar_contradiction_clause,[],[f442])).

fof(f442,plain,
    ( $false
    | spl3_40 ),
    inference(resolution,[],[f419,f38])).

fof(f38,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f419,plain,
    ( ~ v1_funct_1(sK1)
    | spl3_40 ),
    inference(avatar_component_clause,[],[f418])).

fof(f418,plain,
    ( spl3_40
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f420,plain,
    ( ~ spl3_7
    | ~ spl3_39
    | ~ spl3_10
    | ~ spl3_40
    | spl3_2
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f413,f116,f87,f58,f418,f129,f415,f97])).

fof(f116,plain,
    ( spl3_8
  <=> sK2 = k1_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f413,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ v1_funct_1(k7_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK1)
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f412,f77])).

fof(f412,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ v1_funct_1(k7_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK1)
    | r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(trivial_inequality_removal,[],[f411])).

fof(f411,plain,
    ( sK2 != sK2
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ v1_funct_1(k7_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK1)
    | r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f401,f88])).

fof(f401,plain,
    ( sK2 != k1_relat_1(k7_relat_1(sK0,sK2))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ v1_funct_1(k7_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK1)
    | r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))
    | ~ spl3_8 ),
    inference(superposition,[],[f43,f381])).

fof(f381,plain,
    ( sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1))
    | ~ spl3_8 ),
    inference(backward_demodulation,[],[f117,f187])).

fof(f187,plain,(
    ! [X6] : k7_relat_1(k5_relat_1(sK0,sK1),X6) = k5_relat_1(k7_relat_1(sK0,X6),sK1) ),
    inference(resolution,[],[f105,f39])).

fof(f105,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X10)
      | k7_relat_1(k5_relat_1(X10,sK1),X11) = k5_relat_1(k7_relat_1(X10,X11),sK1) ) ),
    inference(resolution,[],[f48,f37])).

fof(f37,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).

fof(f117,plain,
    ( sK2 = k1_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),sK2))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f116])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0))
           => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_1)).

fof(f388,plain,
    ( ~ spl3_9
    | spl3_34 ),
    inference(avatar_split_clause,[],[f382,f386,f119])).

fof(f119,plain,
    ( spl3_9
  <=> v1_relat_1(k5_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f382,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k7_relat_1(sK0,X0),sK1)),k1_relat_1(k5_relat_1(sK0,sK1)))
      | ~ v1_relat_1(k5_relat_1(sK0,sK1)) ) ),
    inference(superposition,[],[f45,f187])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).

fof(f193,plain,
    ( spl3_4
    | ~ spl3_5
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f191,f62,f90,f87])).

fof(f62,plain,
    ( spl3_3
  <=> r1_tarski(sK2,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f191,plain,
    ( ~ v1_relat_1(sK0)
    | sK2 = k1_relat_1(k7_relat_1(sK0,sK2))
    | ~ spl3_3 ),
    inference(resolution,[],[f63,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f63,plain,
    ( r1_tarski(sK2,k1_relat_1(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f190,plain,
    ( ~ spl3_5
    | ~ spl3_7
    | spl3_3
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f189,f55,f62,f97,f90])).

fof(f189,plain,
    ( r1_tarski(sK2,k1_relat_1(sK0))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl3_1 ),
    inference(resolution,[],[f177,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

fof(f177,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),X0)
        | r1_tarski(sK2,X0) )
    | ~ spl3_1 ),
    inference(superposition,[],[f53,f114])).

fof(f114,plain,
    ( k1_relat_1(k5_relat_1(sK0,sK1)) = k2_xboole_0(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl3_1 ),
    inference(resolution,[],[f56,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f56,plain,
    ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f152,plain,(
    spl3_10 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | spl3_10 ),
    inference(resolution,[],[f150,f39])).

fof(f150,plain,
    ( ~ v1_relat_1(sK0)
    | spl3_10 ),
    inference(resolution,[],[f130,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f130,plain,
    ( ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f129])).

fof(f123,plain,
    ( ~ spl3_5
    | ~ spl3_7
    | spl3_9 ),
    inference(avatar_split_clause,[],[f122,f119,f97,f90])).

fof(f122,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | spl3_9 ),
    inference(resolution,[],[f120,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f120,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f119])).

fof(f121,plain,
    ( spl3_8
    | ~ spl3_9
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f113,f55,f119,f116])).

fof(f113,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | sK2 = k1_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),sK2))
    | ~ spl3_1 ),
    inference(resolution,[],[f56,f47])).

fof(f112,plain,(
    spl3_7 ),
    inference(avatar_contradiction_clause,[],[f111])).

fof(f111,plain,
    ( $false
    | spl3_7 ),
    inference(resolution,[],[f98,f37])).

fof(f98,plain,
    ( ~ v1_relat_1(sK1)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f97])).

fof(f101,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f100])).

fof(f100,plain,
    ( $false
    | spl3_5 ),
    inference(resolution,[],[f91,f39])).

fof(f91,plain,
    ( ~ v1_relat_1(sK0)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f90])).

fof(f68,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f34,f62,f58,f55])).

fof(f34,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK0))
    | ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f64,plain,
    ( spl3_1
    | spl3_3 ),
    inference(avatar_split_clause,[],[f35,f62,f55])).

fof(f35,plain,
    ( r1_tarski(sK2,k1_relat_1(sK0))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f60,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f36,f58,f55])).

fof(f36,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n001.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:13:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (7206)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.48  % (7198)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.50  % (7205)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.50  % (7196)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.51  % (7215)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.51  % (7207)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.51  % (7197)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.51  % (7195)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.51  % (7193)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.51  % (7211)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.51  % (7215)Refutation not found, incomplete strategy% (7215)------------------------------
% 0.21/0.51  % (7215)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (7199)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (7215)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (7215)Memory used [KB]: 10618
% 0.21/0.52  % (7215)Time elapsed: 0.062 s
% 0.21/0.52  % (7215)------------------------------
% 0.21/0.52  % (7215)------------------------------
% 0.21/0.52  % (7209)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.52  % (7203)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.52  % (7202)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.52  % (7195)Refutation not found, incomplete strategy% (7195)------------------------------
% 0.21/0.52  % (7195)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (7195)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (7195)Memory used [KB]: 10618
% 0.21/0.52  % (7195)Time elapsed: 0.100 s
% 0.21/0.52  % (7195)------------------------------
% 0.21/0.52  % (7195)------------------------------
% 0.21/0.52  % (7194)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.52  % (7201)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.52  % (7200)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.52  % (7214)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.53  % (7208)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.53  % (7213)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.54  % (7192)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.54  % (7210)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.56  % (7212)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.57  % (7204)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 2.14/0.66  % (7204)Refutation found. Thanks to Tanya!
% 2.14/0.66  % SZS status Theorem for theBenchmark
% 2.14/0.66  % SZS output start Proof for theBenchmark
% 2.14/0.66  fof(f1495,plain,(
% 2.14/0.66    $false),
% 2.14/0.66    inference(avatar_sat_refutation,[],[f60,f64,f68,f101,f112,f121,f123,f152,f190,f193,f388,f420,f443,f451,f453,f1356,f1493])).
% 2.14/0.66  fof(f1493,plain,(
% 2.14/0.66    spl3_1 | ~spl3_34 | ~spl3_96),
% 2.14/0.66    inference(avatar_contradiction_clause,[],[f1490])).
% 2.14/0.66  fof(f1490,plain,(
% 2.14/0.66    $false | (spl3_1 | ~spl3_34 | ~spl3_96)),
% 2.14/0.66    inference(resolution,[],[f1388,f65])).
% 2.14/0.66  fof(f65,plain,(
% 2.14/0.66    ~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) | spl3_1),
% 2.14/0.66    inference(avatar_component_clause,[],[f55])).
% 2.14/0.66  fof(f55,plain,(
% 2.14/0.66    spl3_1 <=> r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 2.14/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 2.14/0.66  fof(f1388,plain,(
% 2.14/0.66    r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) | (~spl3_34 | ~spl3_96)),
% 2.14/0.66    inference(superposition,[],[f387,f1355])).
% 2.14/0.66  fof(f1355,plain,(
% 2.14/0.66    sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) | ~spl3_96),
% 2.14/0.66    inference(avatar_component_clause,[],[f1354])).
% 2.14/0.66  fof(f1354,plain,(
% 2.14/0.66    spl3_96 <=> sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1))),
% 2.14/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_96])])).
% 2.14/0.66  fof(f387,plain,(
% 2.14/0.66    ( ! [X0] : (r1_tarski(k1_relat_1(k5_relat_1(k7_relat_1(sK0,X0),sK1)),k1_relat_1(k5_relat_1(sK0,sK1)))) ) | ~spl3_34),
% 2.14/0.66    inference(avatar_component_clause,[],[f386])).
% 2.14/0.66  fof(f386,plain,(
% 2.14/0.66    spl3_34 <=> ! [X0] : r1_tarski(k1_relat_1(k5_relat_1(k7_relat_1(sK0,X0),sK1)),k1_relat_1(k5_relat_1(sK0,sK1)))),
% 2.14/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 2.14/0.66  fof(f1356,plain,(
% 2.14/0.66    ~spl3_10 | ~spl3_7 | spl3_96 | ~spl3_2 | ~spl3_4),
% 2.14/0.66    inference(avatar_split_clause,[],[f1352,f87,f58,f1354,f97,f129])).
% 2.14/0.66  fof(f129,plain,(
% 2.14/0.66    spl3_10 <=> v1_relat_1(k7_relat_1(sK0,sK2))),
% 2.14/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 2.14/0.66  fof(f97,plain,(
% 2.14/0.66    spl3_7 <=> v1_relat_1(sK1)),
% 2.14/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 2.14/0.66  fof(f58,plain,(
% 2.14/0.66    spl3_2 <=> r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))),
% 2.14/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 2.14/0.66  fof(f87,plain,(
% 2.14/0.66    spl3_4 <=> sK2 = k1_relat_1(k7_relat_1(sK0,sK2))),
% 2.14/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 2.14/0.66  fof(f1352,plain,(
% 2.14/0.66    sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) | ~v1_relat_1(sK1) | ~v1_relat_1(k7_relat_1(sK0,sK2)) | (~spl3_2 | ~spl3_4)),
% 2.14/0.66    inference(forward_demodulation,[],[f1342,f88])).
% 2.14/0.66  fof(f88,plain,(
% 2.14/0.66    sK2 = k1_relat_1(k7_relat_1(sK0,sK2)) | ~spl3_4),
% 2.14/0.66    inference(avatar_component_clause,[],[f87])).
% 2.14/0.66  fof(f1342,plain,(
% 2.14/0.66    ~v1_relat_1(sK1) | ~v1_relat_1(k7_relat_1(sK0,sK2)) | k1_relat_1(k7_relat_1(sK0,sK2)) = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) | ~spl3_2),
% 2.14/0.66    inference(resolution,[],[f143,f59])).
% 2.14/0.66  fof(f59,plain,(
% 2.14/0.66    r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~spl3_2),
% 2.14/0.66    inference(avatar_component_clause,[],[f58])).
% 2.14/0.66  fof(f143,plain,(
% 2.14/0.66    ( ! [X0,X1] : (~r1_tarski(k9_relat_1(sK0,X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(k7_relat_1(sK0,X0)) | k1_relat_1(k5_relat_1(k7_relat_1(sK0,X0),X1)) = k1_relat_1(k7_relat_1(sK0,X0))) )),
% 2.14/0.66    inference(superposition,[],[f42,f77])).
% 2.14/0.66  fof(f77,plain,(
% 2.14/0.66    ( ! [X6] : (k2_relat_1(k7_relat_1(sK0,X6)) = k9_relat_1(sK0,X6)) )),
% 2.14/0.66    inference(resolution,[],[f46,f39])).
% 2.14/0.66  fof(f39,plain,(
% 2.14/0.66    v1_relat_1(sK0)),
% 2.14/0.66    inference(cnf_transformation,[],[f16])).
% 2.14/0.66  fof(f16,plain,(
% 2.14/0.66    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 2.14/0.66    inference(flattening,[],[f15])).
% 2.14/0.66  fof(f15,plain,(
% 2.14/0.66    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 2.14/0.66    inference(ennf_transformation,[],[f14])).
% 2.14/0.66  fof(f14,negated_conjecture,(
% 2.14/0.66    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 2.14/0.66    inference(negated_conjecture,[],[f13])).
% 2.14/0.66  fof(f13,conjecture,(
% 2.14/0.66    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 2.14/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_1)).
% 2.14/0.66  fof(f46,plain,(
% 2.14/0.66    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 2.14/0.66    inference(cnf_transformation,[],[f24])).
% 2.14/0.66  fof(f24,plain,(
% 2.14/0.66    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.14/0.66    inference(ennf_transformation,[],[f6])).
% 2.14/0.66  fof(f6,axiom,(
% 2.14/0.66    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.14/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 2.14/0.66  fof(f42,plain,(
% 2.14/0.66    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)) )),
% 2.14/0.66    inference(cnf_transformation,[],[f19])).
% 2.14/0.66  fof(f19,plain,(
% 2.14/0.66    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.14/0.66    inference(flattening,[],[f18])).
% 2.14/0.66  fof(f18,plain,(
% 2.14/0.66    ! [X0] : (! [X1] : ((k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.14/0.66    inference(ennf_transformation,[],[f8])).
% 2.14/0.66  fof(f8,axiom,(
% 2.14/0.66    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0))))),
% 2.14/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).
% 2.14/0.66  fof(f453,plain,(
% 2.14/0.66    spl3_46),
% 2.14/0.66    inference(avatar_contradiction_clause,[],[f452])).
% 2.14/0.66  fof(f452,plain,(
% 2.14/0.66    $false | spl3_46),
% 2.14/0.66    inference(resolution,[],[f450,f40])).
% 2.14/0.66  fof(f40,plain,(
% 2.14/0.66    v1_funct_1(sK0)),
% 2.14/0.66    inference(cnf_transformation,[],[f16])).
% 2.14/0.66  fof(f450,plain,(
% 2.14/0.66    ~v1_funct_1(sK0) | spl3_46),
% 2.14/0.66    inference(avatar_component_clause,[],[f449])).
% 2.14/0.66  fof(f449,plain,(
% 2.14/0.66    spl3_46 <=> v1_funct_1(sK0)),
% 2.14/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 2.14/0.66  fof(f451,plain,(
% 2.14/0.66    ~spl3_5 | ~spl3_46 | spl3_39),
% 2.14/0.66    inference(avatar_split_clause,[],[f447,f415,f449,f90])).
% 2.14/0.66  fof(f90,plain,(
% 2.14/0.66    spl3_5 <=> v1_relat_1(sK0)),
% 2.14/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 2.14/0.66  fof(f415,plain,(
% 2.14/0.66    spl3_39 <=> v1_funct_1(k7_relat_1(sK0,sK2))),
% 2.14/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 2.14/0.66  fof(f447,plain,(
% 2.14/0.66    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl3_39),
% 2.14/0.66    inference(resolution,[],[f416,f51])).
% 2.14/0.66  fof(f51,plain,(
% 2.14/0.66    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.14/0.66    inference(cnf_transformation,[],[f30])).
% 2.14/0.66  fof(f30,plain,(
% 2.14/0.66    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.14/0.66    inference(flattening,[],[f29])).
% 2.14/0.66  fof(f29,plain,(
% 2.14/0.66    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.14/0.66    inference(ennf_transformation,[],[f11])).
% 2.14/0.66  fof(f11,axiom,(
% 2.14/0.66    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 2.14/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).
% 2.14/0.66  fof(f416,plain,(
% 2.14/0.66    ~v1_funct_1(k7_relat_1(sK0,sK2)) | spl3_39),
% 2.14/0.66    inference(avatar_component_clause,[],[f415])).
% 2.14/0.66  fof(f443,plain,(
% 2.14/0.66    spl3_40),
% 2.14/0.66    inference(avatar_contradiction_clause,[],[f442])).
% 2.14/0.66  fof(f442,plain,(
% 2.14/0.66    $false | spl3_40),
% 2.14/0.66    inference(resolution,[],[f419,f38])).
% 2.14/0.66  fof(f38,plain,(
% 2.14/0.66    v1_funct_1(sK1)),
% 2.14/0.66    inference(cnf_transformation,[],[f16])).
% 2.14/0.66  fof(f419,plain,(
% 2.14/0.66    ~v1_funct_1(sK1) | spl3_40),
% 2.14/0.66    inference(avatar_component_clause,[],[f418])).
% 2.14/0.66  fof(f418,plain,(
% 2.14/0.66    spl3_40 <=> v1_funct_1(sK1)),
% 2.14/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 2.14/0.66  fof(f420,plain,(
% 2.14/0.66    ~spl3_7 | ~spl3_39 | ~spl3_10 | ~spl3_40 | spl3_2 | ~spl3_4 | ~spl3_8),
% 2.14/0.66    inference(avatar_split_clause,[],[f413,f116,f87,f58,f418,f129,f415,f97])).
% 2.14/0.66  fof(f116,plain,(
% 2.14/0.66    spl3_8 <=> sK2 = k1_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),sK2))),
% 2.14/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 2.14/0.66  fof(f413,plain,(
% 2.14/0.66    r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(k7_relat_1(sK0,sK2)) | ~v1_funct_1(k7_relat_1(sK0,sK2)) | ~v1_relat_1(sK1) | (~spl3_4 | ~spl3_8)),
% 2.14/0.66    inference(forward_demodulation,[],[f412,f77])).
% 2.14/0.66  fof(f412,plain,(
% 2.14/0.66    ~v1_funct_1(sK1) | ~v1_relat_1(k7_relat_1(sK0,sK2)) | ~v1_funct_1(k7_relat_1(sK0,sK2)) | ~v1_relat_1(sK1) | r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) | (~spl3_4 | ~spl3_8)),
% 2.14/0.66    inference(trivial_inequality_removal,[],[f411])).
% 2.14/0.66  fof(f411,plain,(
% 2.14/0.66    sK2 != sK2 | ~v1_funct_1(sK1) | ~v1_relat_1(k7_relat_1(sK0,sK2)) | ~v1_funct_1(k7_relat_1(sK0,sK2)) | ~v1_relat_1(sK1) | r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) | (~spl3_4 | ~spl3_8)),
% 2.14/0.66    inference(forward_demodulation,[],[f401,f88])).
% 2.14/0.66  fof(f401,plain,(
% 2.14/0.66    sK2 != k1_relat_1(k7_relat_1(sK0,sK2)) | ~v1_funct_1(sK1) | ~v1_relat_1(k7_relat_1(sK0,sK2)) | ~v1_funct_1(k7_relat_1(sK0,sK2)) | ~v1_relat_1(sK1) | r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) | ~spl3_8),
% 2.14/0.66    inference(superposition,[],[f43,f381])).
% 2.14/0.66  fof(f381,plain,(
% 2.14/0.66    sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) | ~spl3_8),
% 2.14/0.66    inference(backward_demodulation,[],[f117,f187])).
% 2.14/0.66  fof(f187,plain,(
% 2.14/0.66    ( ! [X6] : (k7_relat_1(k5_relat_1(sK0,sK1),X6) = k5_relat_1(k7_relat_1(sK0,X6),sK1)) )),
% 2.14/0.66    inference(resolution,[],[f105,f39])).
% 2.14/0.66  fof(f105,plain,(
% 2.14/0.66    ( ! [X10,X11] : (~v1_relat_1(X10) | k7_relat_1(k5_relat_1(X10,sK1),X11) = k5_relat_1(k7_relat_1(X10,X11),sK1)) )),
% 2.14/0.66    inference(resolution,[],[f48,f37])).
% 2.14/0.66  fof(f37,plain,(
% 2.14/0.66    v1_relat_1(sK1)),
% 2.14/0.66    inference(cnf_transformation,[],[f16])).
% 2.14/0.66  fof(f48,plain,(
% 2.14/0.66    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_relat_1(X1) | k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)) )),
% 2.14/0.66    inference(cnf_transformation,[],[f27])).
% 2.14/0.66  fof(f27,plain,(
% 2.14/0.66    ! [X0,X1] : (! [X2] : (k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 2.14/0.66    inference(ennf_transformation,[],[f5])).
% 2.14/0.66  fof(f5,axiom,(
% 2.14/0.66    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)))),
% 2.14/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).
% 2.14/0.66  fof(f117,plain,(
% 2.14/0.66    sK2 = k1_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),sK2)) | ~spl3_8),
% 2.14/0.66    inference(avatar_component_clause,[],[f116])).
% 2.14/0.66  fof(f43,plain,(
% 2.14/0.66    ( ! [X0,X1] : (k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | r1_tarski(k2_relat_1(X1),k1_relat_1(X0))) )),
% 2.14/0.66    inference(cnf_transformation,[],[f21])).
% 2.14/0.66  fof(f21,plain,(
% 2.14/0.66    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.14/0.66    inference(flattening,[],[f20])).
% 2.14/0.66  fof(f20,plain,(
% 2.14/0.66    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.14/0.66    inference(ennf_transformation,[],[f12])).
% 2.14/0.66  fof(f12,axiom,(
% 2.14/0.66    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0)) => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))))),
% 2.14/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_1)).
% 2.14/0.66  fof(f388,plain,(
% 2.14/0.66    ~spl3_9 | spl3_34),
% 2.14/0.66    inference(avatar_split_clause,[],[f382,f386,f119])).
% 2.14/0.66  fof(f119,plain,(
% 2.14/0.66    spl3_9 <=> v1_relat_1(k5_relat_1(sK0,sK1))),
% 2.14/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 2.14/0.66  fof(f382,plain,(
% 2.14/0.66    ( ! [X0] : (r1_tarski(k1_relat_1(k5_relat_1(k7_relat_1(sK0,X0),sK1)),k1_relat_1(k5_relat_1(sK0,sK1))) | ~v1_relat_1(k5_relat_1(sK0,sK1))) )),
% 2.14/0.66    inference(superposition,[],[f45,f187])).
% 2.14/0.66  fof(f45,plain,(
% 2.14/0.66    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.14/0.66    inference(cnf_transformation,[],[f23])).
% 2.14/0.66  fof(f23,plain,(
% 2.14/0.66    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.14/0.66    inference(ennf_transformation,[],[f9])).
% 2.14/0.66  fof(f9,axiom,(
% 2.14/0.66    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)))),
% 2.14/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).
% 2.14/0.66  fof(f193,plain,(
% 2.14/0.66    spl3_4 | ~spl3_5 | ~spl3_3),
% 2.14/0.66    inference(avatar_split_clause,[],[f191,f62,f90,f87])).
% 2.14/0.66  fof(f62,plain,(
% 2.14/0.66    spl3_3 <=> r1_tarski(sK2,k1_relat_1(sK0))),
% 2.14/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 2.14/0.66  fof(f191,plain,(
% 2.14/0.66    ~v1_relat_1(sK0) | sK2 = k1_relat_1(k7_relat_1(sK0,sK2)) | ~spl3_3),
% 2.14/0.66    inference(resolution,[],[f63,f47])).
% 2.14/0.66  fof(f47,plain,(
% 2.14/0.66    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = X0) )),
% 2.14/0.66    inference(cnf_transformation,[],[f26])).
% 2.14/0.66  fof(f26,plain,(
% 2.14/0.66    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.14/0.66    inference(flattening,[],[f25])).
% 2.14/0.66  fof(f25,plain,(
% 2.14/0.66    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.14/0.66    inference(ennf_transformation,[],[f10])).
% 2.14/0.66  fof(f10,axiom,(
% 2.14/0.66    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 2.14/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 2.14/0.66  fof(f63,plain,(
% 2.14/0.66    r1_tarski(sK2,k1_relat_1(sK0)) | ~spl3_3),
% 2.14/0.66    inference(avatar_component_clause,[],[f62])).
% 2.14/0.66  fof(f190,plain,(
% 2.14/0.66    ~spl3_5 | ~spl3_7 | spl3_3 | ~spl3_1),
% 2.14/0.66    inference(avatar_split_clause,[],[f189,f55,f62,f97,f90])).
% 2.14/0.66  fof(f189,plain,(
% 2.14/0.66    r1_tarski(sK2,k1_relat_1(sK0)) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0) | ~spl3_1),
% 2.14/0.66    inference(resolution,[],[f177,f41])).
% 2.14/0.66  fof(f41,plain,(
% 2.14/0.66    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.14/0.66    inference(cnf_transformation,[],[f17])).
% 2.14/0.66  fof(f17,plain,(
% 2.14/0.66    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.14/0.66    inference(ennf_transformation,[],[f7])).
% 2.14/0.66  fof(f7,axiom,(
% 2.14/0.66    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 2.14/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).
% 2.14/0.66  fof(f177,plain,(
% 2.14/0.66    ( ! [X0] : (~r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),X0) | r1_tarski(sK2,X0)) ) | ~spl3_1),
% 2.14/0.66    inference(superposition,[],[f53,f114])).
% 2.14/0.66  fof(f114,plain,(
% 2.14/0.66    k1_relat_1(k5_relat_1(sK0,sK1)) = k2_xboole_0(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) | ~spl3_1),
% 2.14/0.66    inference(resolution,[],[f56,f49])).
% 2.14/0.66  fof(f49,plain,(
% 2.14/0.66    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.14/0.66    inference(cnf_transformation,[],[f28])).
% 2.14/0.66  fof(f28,plain,(
% 2.14/0.66    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.14/0.66    inference(ennf_transformation,[],[f2])).
% 2.14/0.66  fof(f2,axiom,(
% 2.14/0.66    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.14/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.14/0.66  fof(f56,plain,(
% 2.14/0.66    r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) | ~spl3_1),
% 2.14/0.66    inference(avatar_component_clause,[],[f55])).
% 2.14/0.66  fof(f53,plain,(
% 2.14/0.66    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 2.14/0.66    inference(cnf_transformation,[],[f33])).
% 2.14/0.66  fof(f33,plain,(
% 2.14/0.66    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 2.14/0.66    inference(ennf_transformation,[],[f1])).
% 2.14/0.66  fof(f1,axiom,(
% 2.14/0.66    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 2.14/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 2.14/0.66  fof(f152,plain,(
% 2.14/0.66    spl3_10),
% 2.14/0.66    inference(avatar_contradiction_clause,[],[f151])).
% 2.14/0.66  fof(f151,plain,(
% 2.14/0.66    $false | spl3_10),
% 2.14/0.66    inference(resolution,[],[f150,f39])).
% 2.14/0.66  fof(f150,plain,(
% 2.14/0.66    ~v1_relat_1(sK0) | spl3_10),
% 2.14/0.66    inference(resolution,[],[f130,f44])).
% 2.14/0.66  fof(f44,plain,(
% 2.14/0.66    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.14/0.66    inference(cnf_transformation,[],[f22])).
% 2.14/0.66  fof(f22,plain,(
% 2.14/0.66    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 2.14/0.66    inference(ennf_transformation,[],[f4])).
% 2.14/0.66  fof(f4,axiom,(
% 2.14/0.66    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 2.14/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 2.14/0.66  fof(f130,plain,(
% 2.14/0.66    ~v1_relat_1(k7_relat_1(sK0,sK2)) | spl3_10),
% 2.14/0.66    inference(avatar_component_clause,[],[f129])).
% 2.14/0.66  fof(f123,plain,(
% 2.14/0.66    ~spl3_5 | ~spl3_7 | spl3_9),
% 2.14/0.66    inference(avatar_split_clause,[],[f122,f119,f97,f90])).
% 2.14/0.66  fof(f122,plain,(
% 2.14/0.66    ~v1_relat_1(sK1) | ~v1_relat_1(sK0) | spl3_9),
% 2.14/0.66    inference(resolution,[],[f120,f52])).
% 2.14/0.66  fof(f52,plain,(
% 2.14/0.66    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.14/0.66    inference(cnf_transformation,[],[f32])).
% 2.14/0.66  fof(f32,plain,(
% 2.14/0.66    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 2.14/0.66    inference(flattening,[],[f31])).
% 2.14/0.66  fof(f31,plain,(
% 2.14/0.66    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 2.14/0.66    inference(ennf_transformation,[],[f3])).
% 2.14/0.66  fof(f3,axiom,(
% 2.14/0.66    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 2.14/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 2.14/0.66  fof(f120,plain,(
% 2.14/0.66    ~v1_relat_1(k5_relat_1(sK0,sK1)) | spl3_9),
% 2.14/0.66    inference(avatar_component_clause,[],[f119])).
% 2.14/0.66  fof(f121,plain,(
% 2.14/0.66    spl3_8 | ~spl3_9 | ~spl3_1),
% 2.14/0.66    inference(avatar_split_clause,[],[f113,f55,f119,f116])).
% 2.14/0.66  fof(f113,plain,(
% 2.14/0.66    ~v1_relat_1(k5_relat_1(sK0,sK1)) | sK2 = k1_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),sK2)) | ~spl3_1),
% 2.14/0.66    inference(resolution,[],[f56,f47])).
% 2.14/0.66  fof(f112,plain,(
% 2.14/0.66    spl3_7),
% 2.14/0.66    inference(avatar_contradiction_clause,[],[f111])).
% 2.14/0.66  fof(f111,plain,(
% 2.14/0.66    $false | spl3_7),
% 2.14/0.66    inference(resolution,[],[f98,f37])).
% 2.14/0.66  fof(f98,plain,(
% 2.14/0.66    ~v1_relat_1(sK1) | spl3_7),
% 2.14/0.66    inference(avatar_component_clause,[],[f97])).
% 2.14/0.66  fof(f101,plain,(
% 2.14/0.66    spl3_5),
% 2.14/0.66    inference(avatar_contradiction_clause,[],[f100])).
% 2.14/0.66  fof(f100,plain,(
% 2.14/0.66    $false | spl3_5),
% 2.14/0.66    inference(resolution,[],[f91,f39])).
% 2.14/0.66  fof(f91,plain,(
% 2.14/0.66    ~v1_relat_1(sK0) | spl3_5),
% 2.14/0.66    inference(avatar_component_clause,[],[f90])).
% 2.14/0.66  fof(f68,plain,(
% 2.14/0.66    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 2.14/0.66    inference(avatar_split_clause,[],[f34,f62,f58,f55])).
% 2.14/0.66  fof(f34,plain,(
% 2.14/0.66    ~r1_tarski(sK2,k1_relat_1(sK0)) | ~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 2.14/0.66    inference(cnf_transformation,[],[f16])).
% 2.14/0.66  fof(f64,plain,(
% 2.14/0.66    spl3_1 | spl3_3),
% 2.14/0.66    inference(avatar_split_clause,[],[f35,f62,f55])).
% 2.14/0.66  fof(f35,plain,(
% 2.14/0.66    r1_tarski(sK2,k1_relat_1(sK0)) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 2.14/0.66    inference(cnf_transformation,[],[f16])).
% 2.14/0.66  fof(f60,plain,(
% 2.14/0.66    spl3_1 | spl3_2),
% 2.14/0.66    inference(avatar_split_clause,[],[f36,f58,f55])).
% 2.14/0.66  fof(f36,plain,(
% 2.14/0.66    r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 2.14/0.66    inference(cnf_transformation,[],[f16])).
% 2.14/0.66  % SZS output end Proof for theBenchmark
% 2.14/0.66  % (7204)------------------------------
% 2.14/0.66  % (7204)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.14/0.66  % (7204)Termination reason: Refutation
% 2.14/0.66  
% 2.14/0.66  % (7204)Memory used [KB]: 11897
% 2.14/0.66  % (7204)Time elapsed: 0.209 s
% 2.14/0.66  % (7204)------------------------------
% 2.14/0.66  % (7204)------------------------------
% 2.14/0.67  % (7191)Success in time 0.304 s
%------------------------------------------------------------------------------
