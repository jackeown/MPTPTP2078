%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0645+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   14 (  15 expanded)
%              Number of leaves         :    4 (   5 expanded)
%              Depth                    :    6
%              Number of atoms          :   19 (  21 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    4 (   2 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1077,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1064,f1076])).

fof(f1076,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f1073])).

fof(f1073,plain,
    ( $false
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f1063,f1023])).

fof(f1023,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f901])).

fof(f901,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f1063,plain,
    ( ~ v2_funct_1(k6_relat_1(sK0))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f1062])).

fof(f1062,plain,
    ( spl8_1
  <=> v2_funct_1(k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f1064,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f1000,f1062])).

fof(f1000,plain,(
    ~ v2_funct_1(k6_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f979])).

fof(f979,plain,(
    ~ v2_funct_1(k6_relat_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f943,f978])).

fof(f978,plain,
    ( ? [X0] : ~ v2_funct_1(k6_relat_1(X0))
   => ~ v2_funct_1(k6_relat_1(sK0)) ),
    introduced(choice_axiom,[])).

fof(f943,plain,(
    ? [X0] : ~ v2_funct_1(k6_relat_1(X0)) ),
    inference(ennf_transformation,[],[f940])).

fof(f940,negated_conjecture,(
    ~ ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(negated_conjecture,[],[f939])).

fof(f939,conjecture,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).
%------------------------------------------------------------------------------
