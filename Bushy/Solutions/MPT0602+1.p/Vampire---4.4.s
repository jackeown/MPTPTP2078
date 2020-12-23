%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t206_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n030.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:58 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   28 (  33 expanded)
%              Number of leaves         :    9 (  13 expanded)
%              Depth                    :    6
%              Number of atoms          :   46 (  54 expanded)
%              Number of equality atoms :    3 (   5 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f75,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f57,f70,f72,f74])).

fof(f74,plain,(
    spl3_7 ),
    inference(avatar_contradiction_clause,[],[f73])).

fof(f73,plain,
    ( $false
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f69,f37])).

fof(f37,plain,(
    ! [X1] : v5_relat_1(k1_xboole_0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v5_relat_1(k1_xboole_0,X1)
      & v4_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t206_relat_1.p',l222_relat_1)).

fof(f69,plain,
    ( ~ v5_relat_1(k1_xboole_0,sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl3_7
  <=> ~ v5_relat_1(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f72,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f71])).

fof(f71,plain,
    ( $false
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f63,f36])).

fof(f36,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f63,plain,
    ( ~ v4_relat_1(k1_xboole_0,sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl3_5
  <=> ~ v4_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f70,plain,
    ( ~ spl3_5
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f30,f68,f62])).

fof(f30,plain,
    ( ~ v5_relat_1(k1_xboole_0,sK1)
    | ~ v4_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ v5_relat_1(k1_xboole_0,sK1)
    | ~ v4_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f26])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( ~ v5_relat_1(k1_xboole_0,X1)
        | ~ v4_relat_1(k1_xboole_0,X0) )
   => ( ~ v5_relat_1(k1_xboole_0,sK1)
      | ~ v4_relat_1(k1_xboole_0,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ~ v5_relat_1(k1_xboole_0,X1)
      | ~ v4_relat_1(k1_xboole_0,X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v5_relat_1(k1_xboole_0,X1)
        & v4_relat_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( v5_relat_1(k1_xboole_0,X1)
      & v4_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t206_relat_1.p',t206_relat_1)).

fof(f57,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f33,f55])).

fof(f55,plain,
    ( spl3_2
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f33,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t206_relat_1.p',d2_xboole_0)).

fof(f50,plain,(
    spl3_0 ),
    inference(avatar_split_clause,[],[f43,f48])).

fof(f48,plain,
    ( spl3_0
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_0])])).

fof(f43,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f31,f33])).

fof(f31,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t206_relat_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
