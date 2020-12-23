%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : xboole_1__t78_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:32 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 100 expanded)
%              Number of leaves         :   17 (  39 expanded)
%              Depth                    :    7
%              Number of atoms          :  110 ( 189 expanded)
%              Number of equality atoms :   33 (  62 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f239,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f59,f69,f78,f86,f117,f124,f157,f234,f235])).

fof(f235,plain,
    ( ~ spl3_10
    | spl3_15 ),
    inference(avatar_contradiction_clause,[],[f225])).

fof(f225,plain,
    ( $false
    | ~ spl3_10
    | ~ spl3_15 ),
    inference(unit_resulting_resolution,[],[f156,f217])).

fof(f217,plain,
    ( ! [X12] : k3_xboole_0(sK0,X12) = k3_xboole_0(sK0,k2_xboole_0(sK1,X12))
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f199,f88])).

fof(f88,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f39,f34])).

fof(f34,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t78_xboole_1.p',t1_boole)).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t78_xboole_1.p',commutativity_k2_xboole_0)).

fof(f199,plain,
    ( ! [X12] : k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X12)) = k3_xboole_0(sK0,k2_xboole_0(sK1,X12))
    | ~ spl3_10 ),
    inference(superposition,[],[f45,f116])).

fof(f116,plain,
    ( k3_xboole_0(sK0,sK1) = k1_xboole_0
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl3_10
  <=> k3_xboole_0(sK0,sK1) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f45,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t78_xboole_1.p',t23_xboole_1)).

fof(f156,plain,
    ( k3_xboole_0(sK0,sK2) != k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl3_15
  <=> k3_xboole_0(sK0,sK2) != k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f234,plain,
    ( ~ spl3_10
    | spl3_15 ),
    inference(avatar_contradiction_clause,[],[f233])).

fof(f233,plain,
    ( $false
    | ~ spl3_10
    | ~ spl3_15 ),
    inference(trivial_inequality_removal,[],[f229])).

fof(f229,plain,
    ( k3_xboole_0(sK0,sK2) != k3_xboole_0(sK0,sK2)
    | ~ spl3_10
    | ~ spl3_15 ),
    inference(superposition,[],[f156,f217])).

fof(f157,plain,(
    ~ spl3_15 ),
    inference(avatar_split_clause,[],[f32,f155])).

fof(f32,plain,(
    k3_xboole_0(sK0,sK2) != k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( k3_xboole_0(sK0,sK2) != k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    & r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( k3_xboole_0(X0,X2) != k3_xboole_0(X0,k2_xboole_0(X1,X2))
        & r1_xboole_0(X0,X1) )
   => ( k3_xboole_0(sK0,sK2) != k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))
      & r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(X0,X2) != k3_xboole_0(X0,k2_xboole_0(X1,X2))
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
       => k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t78_xboole_1.p',t78_xboole_1)).

fof(f124,plain,
    ( spl3_12
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f107,f84,f122])).

fof(f122,plain,
    ( spl3_12
  <=> k3_xboole_0(sK1,sK0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f84,plain,
    ( spl3_8
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f107,plain,
    ( k3_xboole_0(sK1,sK0) = k1_xboole_0
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f85,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox/benchmark/xboole_1__t78_xboole_1.p',d7_xboole_0)).

fof(f85,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f84])).

fof(f117,plain,
    ( spl3_10
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f106,f57,f115])).

fof(f57,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f106,plain,
    ( k3_xboole_0(sK0,sK1) = k1_xboole_0
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f58,f42])).

fof(f58,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f86,plain,
    ( spl3_8
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f79,f57,f84])).

fof(f79,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f58,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t78_xboole_1.p',symmetry_r1_xboole_0)).

fof(f78,plain,
    ( spl3_6
    | ~ spl3_0 ),
    inference(avatar_split_clause,[],[f60,f50,f76])).

fof(f76,plain,
    ( spl3_6
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f50,plain,
    ( spl3_0
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_0])])).

fof(f60,plain,
    ( k1_xboole_0 = o_0_0_xboole_0
    | ~ spl3_0 ),
    inference(unit_resulting_resolution,[],[f51,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t78_xboole_1.p',t6_boole)).

fof(f51,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl3_0 ),
    inference(avatar_component_clause,[],[f50])).

fof(f69,plain,
    ( spl3_4
    | ~ spl3_0 ),
    inference(avatar_split_clause,[],[f62,f50,f67])).

fof(f67,plain,
    ( spl3_4
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f62,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_0 ),
    inference(backward_demodulation,[],[f60,f51])).

fof(f59,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f31,f57])).

fof(f31,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f52,plain,(
    spl3_0 ),
    inference(avatar_split_clause,[],[f33,f50])).

fof(f33,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t78_xboole_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
