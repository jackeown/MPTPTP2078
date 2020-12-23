%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:55 EST 2020

% Result     : Theorem 4.19s
% Output     : Refutation 4.19s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 164 expanded)
%              Number of leaves         :   20 (  52 expanded)
%              Depth                    :   16
%              Number of atoms          :  234 ( 412 expanded)
%              Number of equality atoms :   26 (  44 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6372,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f53,f65,f69,f83,f87,f3418,f3626,f6352])).

fof(f6352,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | spl4_6
    | ~ spl4_39
    | ~ spl4_40 ),
    inference(avatar_contradiction_clause,[],[f6351])).

fof(f6351,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | spl4_6
    | ~ spl4_39
    | ~ spl4_40 ),
    inference(subsumption_resolution,[],[f6350,f86])).

fof(f86,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl4_6
  <=> r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f6350,plain,
    ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_39
    | ~ spl4_40 ),
    inference(forward_demodulation,[],[f6349,f3444])).

fof(f3444,plain,
    ( ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1
    | ~ spl4_3
    | ~ spl4_39 ),
    inference(superposition,[],[f204,f3417])).

fof(f3417,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK3)
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f3416])).

fof(f3416,plain,
    ( spl4_39
  <=> k1_xboole_0 = k4_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f204,plain,
    ( ! [X1] : k2_xboole_0(k4_xboole_0(sK2,sK3),X1) = X1
    | ~ spl4_3 ),
    inference(resolution,[],[f148,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f148,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(sK2,sK3),X0)
    | ~ spl4_3 ),
    inference(resolution,[],[f101,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f101,plain,
    ( ! [X0] : r1_tarski(sK2,k2_xboole_0(sK3,X0))
    | ~ spl4_3 ),
    inference(superposition,[],[f72,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f72,plain,
    ( ! [X0] : r1_tarski(sK2,k2_xboole_0(X0,sK3))
    | ~ spl4_3 ),
    inference(resolution,[],[f64,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f64,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl4_3
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f6349,plain,
    ( r1_tarski(k9_relat_1(sK2,sK0),k2_xboole_0(k1_xboole_0,k9_relat_1(sK3,sK1)))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_40 ),
    inference(forward_demodulation,[],[f6348,f82])).

fof(f82,plain,
    ( k1_xboole_0 = k9_relat_1(sK3,k1_xboole_0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl4_5
  <=> k1_xboole_0 = k9_relat_1(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f6348,plain,
    ( r1_tarski(k9_relat_1(sK2,sK0),k2_xboole_0(k9_relat_1(sK3,k1_xboole_0),k9_relat_1(sK3,sK1)))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_40 ),
    inference(forward_demodulation,[],[f6331,f40])).

fof(f6331,plain,
    ( r1_tarski(k9_relat_1(sK2,sK0),k2_xboole_0(k9_relat_1(sK3,sK1),k9_relat_1(sK3,k1_xboole_0)))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_40 ),
    inference(superposition,[],[f2083,f3421])).

fof(f3421,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f3420])).

fof(f3420,plain,
    ( spl4_40
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f2083,plain,
    ( ! [X2,X1] : r1_tarski(k9_relat_1(sK2,X1),k2_xboole_0(k9_relat_1(sK3,X2),k9_relat_1(sK3,k4_xboole_0(X1,X2))))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(superposition,[],[f278,f385])).

fof(f385,plain,
    ( ! [X2,X3] : k2_xboole_0(k9_relat_1(sK3,X3),k9_relat_1(sK3,k4_xboole_0(X2,X3))) = k2_xboole_0(k9_relat_1(sK3,X2),k2_xboole_0(k9_relat_1(sK3,X3),k9_relat_1(sK3,k4_xboole_0(X2,X3))))
    | ~ spl4_1 ),
    inference(resolution,[],[f166,f37])).

fof(f166,plain,
    ( ! [X0,X1] : r1_tarski(k9_relat_1(sK3,X0),k2_xboole_0(k9_relat_1(sK3,X1),k9_relat_1(sK3,k4_xboole_0(X0,X1))))
    | ~ spl4_1 ),
    inference(resolution,[],[f57,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f57,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(k9_relat_1(sK3,X0),k9_relat_1(sK3,X1)),k9_relat_1(sK3,k4_xboole_0(X0,X1)))
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f56,f39])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f56,plain,
    ( ! [X0,X1] : r1_tarski(k6_subset_1(k9_relat_1(sK3,X0),k9_relat_1(sK3,X1)),k9_relat_1(sK3,k4_xboole_0(X0,X1)))
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f55,f39])).

fof(f55,plain,
    ( ! [X0,X1] : r1_tarski(k6_subset_1(k9_relat_1(sK3,X0),k9_relat_1(sK3,X1)),k9_relat_1(sK3,k6_subset_1(X0,X1)))
    | ~ spl4_1 ),
    inference(resolution,[],[f48,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_relat_1)).

fof(f48,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl4_1
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f278,plain,
    ( ! [X0,X1] : r1_tarski(k9_relat_1(sK2,X1),k2_xboole_0(k9_relat_1(sK3,X1),X0))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(superposition,[],[f143,f40])).

fof(f143,plain,
    ( ! [X2,X3] : r1_tarski(k9_relat_1(sK2,X2),k2_xboole_0(X3,k9_relat_1(sK3,X2)))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(resolution,[],[f75,f33])).

fof(f75,plain,
    ( ! [X1] : r1_tarski(k9_relat_1(sK2,X1),k9_relat_1(sK3,X1))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f74,f52])).

fof(f52,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl4_2
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f74,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(sK2)
        | r1_tarski(k9_relat_1(sK2,X1),k9_relat_1(sK3,X1)) )
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f73,f48])).

fof(f73,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(sK3)
        | ~ v1_relat_1(sK2)
        | r1_tarski(k9_relat_1(sK2,X1),k9_relat_1(sK3,X1)) )
    | ~ spl4_3 ),
    inference(resolution,[],[f64,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_relat_1)).

fof(f3626,plain,
    ( spl4_40
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f3424,f67,f3420])).

fof(f67,plain,
    ( spl4_4
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f3424,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl4_4 ),
    inference(resolution,[],[f221,f41])).

fof(f41,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f221,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,k4_xboole_0(sK0,sK1))
        | k4_xboole_0(sK0,sK1) = X2 )
    | ~ spl4_4 ),
    inference(resolution,[],[f185,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f185,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(sK0,sK1),X0)
    | ~ spl4_4 ),
    inference(resolution,[],[f113,f43])).

fof(f113,plain,
    ( ! [X0] : r1_tarski(sK0,k2_xboole_0(sK1,X0))
    | ~ spl4_4 ),
    inference(superposition,[],[f78,f40])).

fof(f78,plain,
    ( ! [X0] : r1_tarski(sK0,k2_xboole_0(X0,sK1))
    | ~ spl4_4 ),
    inference(resolution,[],[f68,f33])).

fof(f68,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f3418,plain,
    ( spl4_39
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f3383,f63,f3416])).

fof(f3383,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK3)
    | ~ spl4_3 ),
    inference(resolution,[],[f205,f41])).

fof(f205,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,k4_xboole_0(sK2,sK3))
        | k4_xboole_0(sK2,sK3) = X2 )
    | ~ spl4_3 ),
    inference(resolution,[],[f148,f36])).

fof(f87,plain,(
    ~ spl4_6 ),
    inference(avatar_split_clause,[],[f28,f85])).

fof(f28,plain,(
    ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(X0,X1)
                & r1_tarski(X2,X3) )
             => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_relat_1)).

fof(f83,plain,
    ( spl4_5
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f54,f47,f81])).

fof(f54,plain,
    ( k1_xboole_0 = k9_relat_1(sK3,k1_xboole_0)
    | ~ spl4_1 ),
    inference(resolution,[],[f48,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_relat_1)).

fof(f69,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f27,f67])).

fof(f27,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f65,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f26,f63])).

fof(f26,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f53,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f29,f51])).

fof(f29,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f49,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f25,f47])).

fof(f25,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:19:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (26985)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (26993)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % (27002)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.53  % (26994)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (26988)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (26993)Refutation not found, incomplete strategy% (26993)------------------------------
% 0.21/0.53  % (26993)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (26983)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (26993)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (26993)Memory used [KB]: 10746
% 0.21/0.53  % (26993)Time elapsed: 0.116 s
% 0.21/0.53  % (26993)------------------------------
% 0.21/0.53  % (26993)------------------------------
% 0.21/0.53  % (26983)Refutation not found, incomplete strategy% (26983)------------------------------
% 0.21/0.53  % (26983)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (26983)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (26983)Memory used [KB]: 1663
% 0.21/0.53  % (26983)Time elapsed: 0.114 s
% 0.21/0.53  % (26983)------------------------------
% 0.21/0.53  % (26983)------------------------------
% 0.21/0.54  % (26987)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (27015)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (26984)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (27015)Refutation not found, incomplete strategy% (27015)------------------------------
% 0.21/0.54  % (27015)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (27015)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (27015)Memory used [KB]: 1663
% 0.21/0.54  % (27015)Time elapsed: 0.002 s
% 0.21/0.54  % (27015)------------------------------
% 0.21/0.54  % (27015)------------------------------
% 0.21/0.54  % (26982)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (27014)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (27012)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (26997)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.54  % (27010)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (27006)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (27014)Refutation not found, incomplete strategy% (27014)------------------------------
% 0.21/0.54  % (27014)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (26998)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (27003)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (27013)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (26999)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.55  % (27000)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (27001)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (27005)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (26989)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (27014)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (27014)Memory used [KB]: 10746
% 0.21/0.55  % (27014)Time elapsed: 0.119 s
% 0.21/0.55  % (27014)------------------------------
% 0.21/0.55  % (27014)------------------------------
% 0.21/0.55  % (26992)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (26990)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.55  % (26991)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.55  % (27004)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (27008)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.55  % (26995)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.55  % (27009)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (26995)Refutation not found, incomplete strategy% (26995)------------------------------
% 0.21/0.55  % (26995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (26995)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (26995)Memory used [KB]: 10618
% 0.21/0.55  % (26995)Time elapsed: 0.141 s
% 0.21/0.55  % (26995)------------------------------
% 0.21/0.55  % (26995)------------------------------
% 0.21/0.56  % (27000)Refutation not found, incomplete strategy% (27000)------------------------------
% 0.21/0.56  % (27000)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (27000)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (27000)Memory used [KB]: 10618
% 0.21/0.56  % (27000)Time elapsed: 0.147 s
% 0.21/0.56  % (27000)------------------------------
% 0.21/0.56  % (27000)------------------------------
% 2.08/0.64  % (26985)Refutation not found, incomplete strategy% (26985)------------------------------
% 2.08/0.64  % (26985)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.08/0.64  % (26985)Termination reason: Refutation not found, incomplete strategy
% 2.08/0.64  
% 2.08/0.64  % (26985)Memory used [KB]: 6140
% 2.08/0.64  % (26985)Time elapsed: 0.211 s
% 2.08/0.64  % (26985)------------------------------
% 2.08/0.64  % (26985)------------------------------
% 2.08/0.66  % (27034)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.08/0.67  % (27035)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.08/0.68  % (26982)Refutation not found, incomplete strategy% (26982)------------------------------
% 2.08/0.68  % (26982)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.08/0.68  % (26982)Termination reason: Refutation not found, incomplete strategy
% 2.08/0.68  
% 2.08/0.68  % (26982)Memory used [KB]: 1663
% 2.08/0.68  % (26982)Time elapsed: 0.255 s
% 2.08/0.68  % (26982)------------------------------
% 2.08/0.68  % (26982)------------------------------
% 2.08/0.68  % (27037)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.08/0.68  % (27036)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.08/0.68  % (27036)Refutation not found, incomplete strategy% (27036)------------------------------
% 2.08/0.68  % (27036)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.08/0.68  % (27036)Termination reason: Refutation not found, incomplete strategy
% 2.08/0.68  
% 2.08/0.68  % (27036)Memory used [KB]: 6140
% 2.08/0.68  % (27036)Time elapsed: 0.109 s
% 2.08/0.68  % (27036)------------------------------
% 2.08/0.68  % (27036)------------------------------
% 2.08/0.69  % (27038)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.08/0.70  % (27039)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.65/0.71  % (26999)Refutation not found, incomplete strategy% (26999)------------------------------
% 2.65/0.71  % (26999)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.65/0.71  % (26999)Termination reason: Refutation not found, incomplete strategy
% 2.65/0.71  
% 2.65/0.71  % (26999)Memory used [KB]: 6140
% 2.65/0.71  % (26999)Time elapsed: 0.290 s
% 2.65/0.71  % (26999)------------------------------
% 2.65/0.71  % (26999)------------------------------
% 3.15/0.78  % (27045)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 3.15/0.81  % (27047)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 3.15/0.82  % (27048)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 3.15/0.83  % (27009)Time limit reached!
% 3.15/0.83  % (27009)------------------------------
% 3.15/0.83  % (27009)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.15/0.83  % (27009)Termination reason: Time limit
% 3.15/0.83  
% 3.15/0.83  % (27009)Memory used [KB]: 13432
% 3.15/0.83  % (27009)Time elapsed: 0.418 s
% 3.15/0.83  % (27009)------------------------------
% 3.15/0.83  % (27009)------------------------------
% 3.15/0.84  % (26984)Time limit reached!
% 3.15/0.84  % (26984)------------------------------
% 3.15/0.84  % (26984)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.15/0.84  % (26984)Termination reason: Time limit
% 3.15/0.84  
% 3.15/0.84  % (26984)Memory used [KB]: 7164
% 3.15/0.84  % (26984)Time elapsed: 0.416 s
% 3.15/0.84  % (26984)------------------------------
% 3.15/0.84  % (26984)------------------------------
% 3.15/0.85  % (27054)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 4.19/0.93  % (27012)Refutation found. Thanks to Tanya!
% 4.19/0.93  % SZS status Theorem for theBenchmark
% 4.19/0.93  % SZS output start Proof for theBenchmark
% 4.19/0.93  fof(f6372,plain,(
% 4.19/0.93    $false),
% 4.19/0.93    inference(avatar_sat_refutation,[],[f49,f53,f65,f69,f83,f87,f3418,f3626,f6352])).
% 4.19/0.93  fof(f6352,plain,(
% 4.19/0.93    ~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5 | spl4_6 | ~spl4_39 | ~spl4_40),
% 4.19/0.93    inference(avatar_contradiction_clause,[],[f6351])).
% 4.19/0.93  fof(f6351,plain,(
% 4.19/0.93    $false | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5 | spl4_6 | ~spl4_39 | ~spl4_40)),
% 4.19/0.93    inference(subsumption_resolution,[],[f6350,f86])).
% 4.19/0.93  fof(f86,plain,(
% 4.19/0.93    ~r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1)) | spl4_6),
% 4.19/0.93    inference(avatar_component_clause,[],[f85])).
% 4.19/0.93  fof(f85,plain,(
% 4.19/0.93    spl4_6 <=> r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1))),
% 4.19/0.93    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 4.19/0.93  fof(f6350,plain,(
% 4.19/0.93    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1)) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_39 | ~spl4_40)),
% 4.19/0.93    inference(forward_demodulation,[],[f6349,f3444])).
% 4.19/0.93  fof(f3444,plain,(
% 4.19/0.93    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) ) | (~spl4_3 | ~spl4_39)),
% 4.19/0.93    inference(superposition,[],[f204,f3417])).
% 4.19/0.93  fof(f3417,plain,(
% 4.19/0.93    k1_xboole_0 = k4_xboole_0(sK2,sK3) | ~spl4_39),
% 4.19/0.93    inference(avatar_component_clause,[],[f3416])).
% 4.19/0.93  fof(f3416,plain,(
% 4.19/0.93    spl4_39 <=> k1_xboole_0 = k4_xboole_0(sK2,sK3)),
% 4.19/0.93    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 4.19/0.93  fof(f204,plain,(
% 4.19/0.93    ( ! [X1] : (k2_xboole_0(k4_xboole_0(sK2,sK3),X1) = X1) ) | ~spl4_3),
% 4.19/0.93    inference(resolution,[],[f148,f37])).
% 4.19/0.93  fof(f37,plain,(
% 4.19/0.93    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 4.19/0.93    inference(cnf_transformation,[],[f22])).
% 4.19/0.93  fof(f22,plain,(
% 4.19/0.93    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 4.19/0.93    inference(ennf_transformation,[],[f4])).
% 4.19/0.93  fof(f4,axiom,(
% 4.19/0.93    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 4.19/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 4.19/0.93  fof(f148,plain,(
% 4.19/0.93    ( ! [X0] : (r1_tarski(k4_xboole_0(sK2,sK3),X0)) ) | ~spl4_3),
% 4.19/0.93    inference(resolution,[],[f101,f43])).
% 4.19/0.93  fof(f43,plain,(
% 4.19/0.93    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 4.19/0.93    inference(cnf_transformation,[],[f24])).
% 4.19/0.93  fof(f24,plain,(
% 4.19/0.93    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 4.19/0.93    inference(ennf_transformation,[],[f6])).
% 4.19/0.93  fof(f6,axiom,(
% 4.19/0.93    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 4.19/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 4.19/0.93  fof(f101,plain,(
% 4.19/0.93    ( ! [X0] : (r1_tarski(sK2,k2_xboole_0(sK3,X0))) ) | ~spl4_3),
% 4.19/0.93    inference(superposition,[],[f72,f40])).
% 4.19/0.93  fof(f40,plain,(
% 4.19/0.93    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 4.19/0.93    inference(cnf_transformation,[],[f1])).
% 4.19/0.93  fof(f1,axiom,(
% 4.19/0.93    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 4.19/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 4.19/0.93  fof(f72,plain,(
% 4.19/0.93    ( ! [X0] : (r1_tarski(sK2,k2_xboole_0(X0,sK3))) ) | ~spl4_3),
% 4.19/0.93    inference(resolution,[],[f64,f33])).
% 4.19/0.93  fof(f33,plain,(
% 4.19/0.93    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1))) )),
% 4.19/0.93    inference(cnf_transformation,[],[f21])).
% 4.19/0.93  fof(f21,plain,(
% 4.19/0.93    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 4.19/0.93    inference(ennf_transformation,[],[f3])).
% 4.19/0.93  fof(f3,axiom,(
% 4.19/0.93    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 4.19/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 4.19/0.93  fof(f64,plain,(
% 4.19/0.93    r1_tarski(sK2,sK3) | ~spl4_3),
% 4.19/0.93    inference(avatar_component_clause,[],[f63])).
% 4.19/0.93  fof(f63,plain,(
% 4.19/0.93    spl4_3 <=> r1_tarski(sK2,sK3)),
% 4.19/0.93    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 4.19/0.93  fof(f6349,plain,(
% 4.19/0.93    r1_tarski(k9_relat_1(sK2,sK0),k2_xboole_0(k1_xboole_0,k9_relat_1(sK3,sK1))) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_40)),
% 4.19/0.93    inference(forward_demodulation,[],[f6348,f82])).
% 4.19/0.93  fof(f82,plain,(
% 4.19/0.93    k1_xboole_0 = k9_relat_1(sK3,k1_xboole_0) | ~spl4_5),
% 4.19/0.93    inference(avatar_component_clause,[],[f81])).
% 4.19/0.93  fof(f81,plain,(
% 4.19/0.93    spl4_5 <=> k1_xboole_0 = k9_relat_1(sK3,k1_xboole_0)),
% 4.19/0.93    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 4.19/0.93  fof(f6348,plain,(
% 4.19/0.93    r1_tarski(k9_relat_1(sK2,sK0),k2_xboole_0(k9_relat_1(sK3,k1_xboole_0),k9_relat_1(sK3,sK1))) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_40)),
% 4.19/0.93    inference(forward_demodulation,[],[f6331,f40])).
% 4.19/0.93  fof(f6331,plain,(
% 4.19/0.93    r1_tarski(k9_relat_1(sK2,sK0),k2_xboole_0(k9_relat_1(sK3,sK1),k9_relat_1(sK3,k1_xboole_0))) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_40)),
% 4.19/0.93    inference(superposition,[],[f2083,f3421])).
% 4.19/0.93  fof(f3421,plain,(
% 4.19/0.93    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl4_40),
% 4.19/0.93    inference(avatar_component_clause,[],[f3420])).
% 4.19/0.93  fof(f3420,plain,(
% 4.19/0.93    spl4_40 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 4.19/0.93    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 4.19/0.93  fof(f2083,plain,(
% 4.19/0.93    ( ! [X2,X1] : (r1_tarski(k9_relat_1(sK2,X1),k2_xboole_0(k9_relat_1(sK3,X2),k9_relat_1(sK3,k4_xboole_0(X1,X2))))) ) | (~spl4_1 | ~spl4_2 | ~spl4_3)),
% 4.19/0.93    inference(superposition,[],[f278,f385])).
% 4.19/0.93  fof(f385,plain,(
% 4.19/0.93    ( ! [X2,X3] : (k2_xboole_0(k9_relat_1(sK3,X3),k9_relat_1(sK3,k4_xboole_0(X2,X3))) = k2_xboole_0(k9_relat_1(sK3,X2),k2_xboole_0(k9_relat_1(sK3,X3),k9_relat_1(sK3,k4_xboole_0(X2,X3))))) ) | ~spl4_1),
% 4.19/0.93    inference(resolution,[],[f166,f37])).
% 4.19/0.93  fof(f166,plain,(
% 4.19/0.93    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK3,X0),k2_xboole_0(k9_relat_1(sK3,X1),k9_relat_1(sK3,k4_xboole_0(X0,X1))))) ) | ~spl4_1),
% 4.19/0.93    inference(resolution,[],[f57,f42])).
% 4.19/0.93  fof(f42,plain,(
% 4.19/0.93    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 4.19/0.93    inference(cnf_transformation,[],[f23])).
% 4.19/0.93  fof(f23,plain,(
% 4.19/0.93    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 4.19/0.93    inference(ennf_transformation,[],[f7])).
% 4.19/0.93  fof(f7,axiom,(
% 4.19/0.93    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 4.19/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 4.19/0.93  fof(f57,plain,(
% 4.19/0.93    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(k9_relat_1(sK3,X0),k9_relat_1(sK3,X1)),k9_relat_1(sK3,k4_xboole_0(X0,X1)))) ) | ~spl4_1),
% 4.19/0.93    inference(forward_demodulation,[],[f56,f39])).
% 4.19/0.93  fof(f39,plain,(
% 4.19/0.93    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 4.19/0.93    inference(cnf_transformation,[],[f9])).
% 4.19/0.93  fof(f9,axiom,(
% 4.19/0.93    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 4.19/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 4.19/0.93  fof(f56,plain,(
% 4.19/0.93    ( ! [X0,X1] : (r1_tarski(k6_subset_1(k9_relat_1(sK3,X0),k9_relat_1(sK3,X1)),k9_relat_1(sK3,k4_xboole_0(X0,X1)))) ) | ~spl4_1),
% 4.19/0.93    inference(forward_demodulation,[],[f55,f39])).
% 4.19/0.93  fof(f55,plain,(
% 4.19/0.93    ( ! [X0,X1] : (r1_tarski(k6_subset_1(k9_relat_1(sK3,X0),k9_relat_1(sK3,X1)),k9_relat_1(sK3,k6_subset_1(X0,X1)))) ) | ~spl4_1),
% 4.19/0.93    inference(resolution,[],[f48,f30])).
% 4.19/0.93  fof(f30,plain,(
% 4.19/0.93    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1)))) )),
% 4.19/0.93    inference(cnf_transformation,[],[f17])).
% 4.19/0.93  fof(f17,plain,(
% 4.19/0.93    ! [X0,X1,X2] : (r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))) | ~v1_relat_1(X2))),
% 4.19/0.93    inference(ennf_transformation,[],[f11])).
% 4.19/0.93  fof(f11,axiom,(
% 4.19/0.93    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))))),
% 4.19/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_relat_1)).
% 4.19/0.93  fof(f48,plain,(
% 4.19/0.93    v1_relat_1(sK3) | ~spl4_1),
% 4.19/0.93    inference(avatar_component_clause,[],[f47])).
% 4.19/0.93  fof(f47,plain,(
% 4.19/0.93    spl4_1 <=> v1_relat_1(sK3)),
% 4.19/0.93    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 4.19/0.93  fof(f278,plain,(
% 4.19/0.93    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,X1),k2_xboole_0(k9_relat_1(sK3,X1),X0))) ) | (~spl4_1 | ~spl4_2 | ~spl4_3)),
% 4.19/0.93    inference(superposition,[],[f143,f40])).
% 4.19/0.93  fof(f143,plain,(
% 4.19/0.93    ( ! [X2,X3] : (r1_tarski(k9_relat_1(sK2,X2),k2_xboole_0(X3,k9_relat_1(sK3,X2)))) ) | (~spl4_1 | ~spl4_2 | ~spl4_3)),
% 4.19/0.93    inference(resolution,[],[f75,f33])).
% 4.19/0.93  fof(f75,plain,(
% 4.19/0.93    ( ! [X1] : (r1_tarski(k9_relat_1(sK2,X1),k9_relat_1(sK3,X1))) ) | (~spl4_1 | ~spl4_2 | ~spl4_3)),
% 4.19/0.93    inference(subsumption_resolution,[],[f74,f52])).
% 4.19/0.93  fof(f52,plain,(
% 4.19/0.93    v1_relat_1(sK2) | ~spl4_2),
% 4.19/0.93    inference(avatar_component_clause,[],[f51])).
% 4.19/0.93  fof(f51,plain,(
% 4.19/0.93    spl4_2 <=> v1_relat_1(sK2)),
% 4.19/0.93    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 4.19/0.93  fof(f74,plain,(
% 4.19/0.93    ( ! [X1] : (~v1_relat_1(sK2) | r1_tarski(k9_relat_1(sK2,X1),k9_relat_1(sK3,X1))) ) | (~spl4_1 | ~spl4_3)),
% 4.19/0.93    inference(subsumption_resolution,[],[f73,f48])).
% 4.19/0.93  fof(f73,plain,(
% 4.19/0.93    ( ! [X1] : (~v1_relat_1(sK3) | ~v1_relat_1(sK2) | r1_tarski(k9_relat_1(sK2,X1),k9_relat_1(sK3,X1))) ) | ~spl4_3),
% 4.19/0.93    inference(resolution,[],[f64,f31])).
% 4.19/0.93  fof(f31,plain,(
% 4.19/0.93    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))) )),
% 4.19/0.93    inference(cnf_transformation,[],[f19])).
% 4.19/0.93  fof(f19,plain,(
% 4.19/0.93    ! [X0,X1] : (! [X2] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 4.19/0.93    inference(flattening,[],[f18])).
% 4.19/0.93  fof(f18,plain,(
% 4.19/0.93    ! [X0,X1] : (! [X2] : ((r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 4.19/0.93    inference(ennf_transformation,[],[f12])).
% 4.19/0.93  fof(f12,axiom,(
% 4.19/0.93    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)))))),
% 4.19/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_relat_1)).
% 4.19/0.93  fof(f3626,plain,(
% 4.19/0.93    spl4_40 | ~spl4_4),
% 4.19/0.93    inference(avatar_split_clause,[],[f3424,f67,f3420])).
% 4.19/0.93  fof(f67,plain,(
% 4.19/0.93    spl4_4 <=> r1_tarski(sK0,sK1)),
% 4.19/0.93    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 4.19/0.93  fof(f3424,plain,(
% 4.19/0.93    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl4_4),
% 4.19/0.93    inference(resolution,[],[f221,f41])).
% 4.19/0.93  fof(f41,plain,(
% 4.19/0.93    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 4.19/0.93    inference(cnf_transformation,[],[f5])).
% 4.19/0.93  fof(f5,axiom,(
% 4.19/0.93    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 4.19/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 4.19/0.93  fof(f221,plain,(
% 4.19/0.93    ( ! [X2] : (~r1_tarski(X2,k4_xboole_0(sK0,sK1)) | k4_xboole_0(sK0,sK1) = X2) ) | ~spl4_4),
% 4.19/0.93    inference(resolution,[],[f185,f36])).
% 4.19/0.93  fof(f36,plain,(
% 4.19/0.93    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 4.19/0.93    inference(cnf_transformation,[],[f2])).
% 4.19/0.93  fof(f2,axiom,(
% 4.19/0.93    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.19/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 4.19/0.93  fof(f185,plain,(
% 4.19/0.93    ( ! [X0] : (r1_tarski(k4_xboole_0(sK0,sK1),X0)) ) | ~spl4_4),
% 4.19/0.93    inference(resolution,[],[f113,f43])).
% 4.19/0.93  fof(f113,plain,(
% 4.19/0.93    ( ! [X0] : (r1_tarski(sK0,k2_xboole_0(sK1,X0))) ) | ~spl4_4),
% 4.19/0.93    inference(superposition,[],[f78,f40])).
% 4.19/0.93  fof(f78,plain,(
% 4.19/0.93    ( ! [X0] : (r1_tarski(sK0,k2_xboole_0(X0,sK1))) ) | ~spl4_4),
% 4.19/0.93    inference(resolution,[],[f68,f33])).
% 4.19/0.93  fof(f68,plain,(
% 4.19/0.93    r1_tarski(sK0,sK1) | ~spl4_4),
% 4.19/0.93    inference(avatar_component_clause,[],[f67])).
% 4.19/0.93  fof(f3418,plain,(
% 4.19/0.93    spl4_39 | ~spl4_3),
% 4.19/0.93    inference(avatar_split_clause,[],[f3383,f63,f3416])).
% 4.19/0.93  fof(f3383,plain,(
% 4.19/0.93    k1_xboole_0 = k4_xboole_0(sK2,sK3) | ~spl4_3),
% 4.19/0.93    inference(resolution,[],[f205,f41])).
% 4.19/0.93  fof(f205,plain,(
% 4.19/0.93    ( ! [X2] : (~r1_tarski(X2,k4_xboole_0(sK2,sK3)) | k4_xboole_0(sK2,sK3) = X2) ) | ~spl4_3),
% 4.19/0.93    inference(resolution,[],[f148,f36])).
% 4.19/0.93  fof(f87,plain,(
% 4.19/0.93    ~spl4_6),
% 4.19/0.93    inference(avatar_split_clause,[],[f28,f85])).
% 4.19/0.93  fof(f28,plain,(
% 4.19/0.93    ~r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1))),
% 4.19/0.93    inference(cnf_transformation,[],[f16])).
% 4.19/0.93  fof(f16,plain,(
% 4.19/0.93    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 4.19/0.93    inference(flattening,[],[f15])).
% 4.19/0.93  fof(f15,plain,(
% 4.19/0.93    ? [X0,X1,X2] : (? [X3] : ((~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) & (r1_tarski(X0,X1) & r1_tarski(X2,X3))) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 4.19/0.93    inference(ennf_transformation,[],[f14])).
% 4.19/0.93  fof(f14,negated_conjecture,(
% 4.19/0.93    ~! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)))))),
% 4.19/0.93    inference(negated_conjecture,[],[f13])).
% 4.19/0.93  fof(f13,conjecture,(
% 4.19/0.93    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)))))),
% 4.19/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_relat_1)).
% 4.19/0.93  fof(f83,plain,(
% 4.19/0.93    spl4_5 | ~spl4_1),
% 4.19/0.93    inference(avatar_split_clause,[],[f54,f47,f81])).
% 4.19/0.93  fof(f54,plain,(
% 4.19/0.93    k1_xboole_0 = k9_relat_1(sK3,k1_xboole_0) | ~spl4_1),
% 4.19/0.93    inference(resolution,[],[f48,f32])).
% 4.19/0.93  fof(f32,plain,(
% 4.19/0.93    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)) )),
% 4.19/0.93    inference(cnf_transformation,[],[f20])).
% 4.19/0.93  fof(f20,plain,(
% 4.19/0.93    ! [X0] : (k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 4.19/0.93    inference(ennf_transformation,[],[f10])).
% 4.19/0.93  fof(f10,axiom,(
% 4.19/0.93    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0))),
% 4.19/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_relat_1)).
% 4.19/0.93  fof(f69,plain,(
% 4.19/0.93    spl4_4),
% 4.19/0.93    inference(avatar_split_clause,[],[f27,f67])).
% 4.19/0.93  fof(f27,plain,(
% 4.19/0.93    r1_tarski(sK0,sK1)),
% 4.19/0.93    inference(cnf_transformation,[],[f16])).
% 4.19/0.93  fof(f65,plain,(
% 4.19/0.93    spl4_3),
% 4.19/0.93    inference(avatar_split_clause,[],[f26,f63])).
% 4.19/0.93  fof(f26,plain,(
% 4.19/0.93    r1_tarski(sK2,sK3)),
% 4.19/0.93    inference(cnf_transformation,[],[f16])).
% 4.19/0.93  fof(f53,plain,(
% 4.19/0.93    spl4_2),
% 4.19/0.93    inference(avatar_split_clause,[],[f29,f51])).
% 4.19/0.93  fof(f29,plain,(
% 4.19/0.93    v1_relat_1(sK2)),
% 4.19/0.93    inference(cnf_transformation,[],[f16])).
% 4.19/0.93  fof(f49,plain,(
% 4.19/0.93    spl4_1),
% 4.19/0.93    inference(avatar_split_clause,[],[f25,f47])).
% 4.19/0.93  fof(f25,plain,(
% 4.19/0.93    v1_relat_1(sK3)),
% 4.19/0.93    inference(cnf_transformation,[],[f16])).
% 4.19/0.93  % SZS output end Proof for theBenchmark
% 4.19/0.93  % (27012)------------------------------
% 4.19/0.93  % (27012)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.19/0.93  % (27012)Termination reason: Refutation
% 4.19/0.93  
% 4.19/0.93  % (27012)Memory used [KB]: 10106
% 4.19/0.93  % (27012)Time elapsed: 0.521 s
% 4.19/0.93  % (27012)------------------------------
% 4.19/0.93  % (27012)------------------------------
% 4.19/0.94  % (26978)Success in time 0.568 s
%------------------------------------------------------------------------------
