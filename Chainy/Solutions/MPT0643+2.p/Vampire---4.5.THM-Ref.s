%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0643+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:41 EST 2020

% Result     : Theorem 17.20s
% Output     : Refutation 17.20s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 154 expanded)
%              Number of leaves         :   21 (  57 expanded)
%              Depth                    :   14
%              Number of atoms          :  340 ( 776 expanded)
%              Number of equality atoms :   84 ( 256 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9198,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1941,f1946,f1951,f1956,f1961,f1966,f1971,f1976,f1981,f1986,f2561,f3979,f4223,f4337,f9185])).

fof(f9185,plain,
    ( ~ spl96_2
    | spl96_3
    | ~ spl96_216
    | ~ spl96_200
    | ~ spl96_217
    | ~ spl96_8
    | ~ spl96_109 ),
    inference(avatar_split_clause,[],[f9184,f2555,f1973,f3404,f3318,f3400,f1948,f1943])).

fof(f1943,plain,
    ( spl96_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl96_2])])).

fof(f1948,plain,
    ( spl96_3
  <=> sK2 = k6_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl96_3])])).

fof(f3400,plain,
    ( spl96_216
  <=> v1_funct_1(k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl96_216])])).

fof(f3318,plain,
    ( spl96_200
  <=> v1_relat_1(k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl96_200])])).

fof(f3404,plain,
    ( spl96_217
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl96_217])])).

fof(f1973,plain,
    ( spl96_8
  <=> sK0 = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl96_8])])).

fof(f2555,plain,
    ( spl96_109
  <=> ! [X18] :
        ( sK0 != k1_relat_1(X18)
        | sK2 = X18
        | ~ v1_funct_1(X18)
        | ~ v1_relat_1(X18)
        | sK1 != k5_relat_1(X18,sK1)
        | ~ r1_tarski(k2_relat_1(X18),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl96_109])])).

fof(f9184,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ v1_relat_1(k6_relat_1(sK0))
    | ~ v1_funct_1(k6_relat_1(sK0))
    | sK2 = k6_relat_1(sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl96_8
    | ~ spl96_109 ),
    inference(forward_demodulation,[],[f9183,f1975])).

fof(f1975,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl96_8 ),
    inference(avatar_component_clause,[],[f1973])).

fof(f9183,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),sK0)
    | ~ v1_relat_1(k6_relat_1(sK0))
    | ~ v1_funct_1(k6_relat_1(sK0))
    | sK2 = k6_relat_1(sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl96_8
    | ~ spl96_109 ),
    inference(forward_demodulation,[],[f9182,f1342])).

fof(f1342,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f863])).

fof(f863,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f9182,plain,
    ( ~ v1_relat_1(k6_relat_1(sK0))
    | ~ v1_funct_1(k6_relat_1(sK0))
    | sK2 = k6_relat_1(sK0)
    | ~ r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(sK1))),sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl96_8
    | ~ spl96_109 ),
    inference(trivial_inequality_removal,[],[f9181])).

fof(f9181,plain,
    ( sK0 != sK0
    | ~ v1_relat_1(k6_relat_1(sK0))
    | ~ v1_funct_1(k6_relat_1(sK0))
    | sK2 = k6_relat_1(sK0)
    | ~ r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(sK1))),sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl96_8
    | ~ spl96_109 ),
    inference(forward_demodulation,[],[f9180,f1975])).

fof(f9180,plain,
    ( sK0 != k1_relat_1(sK1)
    | ~ v1_relat_1(k6_relat_1(sK0))
    | ~ v1_funct_1(k6_relat_1(sK0))
    | sK2 = k6_relat_1(sK0)
    | ~ r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(sK1))),sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl96_8
    | ~ spl96_109 ),
    inference(forward_demodulation,[],[f9179,f1341])).

fof(f1341,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f863])).

fof(f9179,plain,
    ( ~ v1_relat_1(k6_relat_1(sK0))
    | ~ v1_funct_1(k6_relat_1(sK0))
    | sK2 = k6_relat_1(sK0)
    | sK0 != k1_relat_1(k6_relat_1(k1_relat_1(sK1)))
    | ~ r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(sK1))),sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl96_8
    | ~ spl96_109 ),
    inference(forward_demodulation,[],[f9178,f1975])).

fof(f9178,plain,
    ( ~ v1_funct_1(k6_relat_1(sK0))
    | sK2 = k6_relat_1(sK0)
    | ~ v1_relat_1(k6_relat_1(k1_relat_1(sK1)))
    | sK0 != k1_relat_1(k6_relat_1(k1_relat_1(sK1)))
    | ~ r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(sK1))),sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl96_8
    | ~ spl96_109 ),
    inference(forward_demodulation,[],[f9177,f1975])).

fof(f9177,plain,
    ( sK2 = k6_relat_1(sK0)
    | ~ v1_funct_1(k6_relat_1(k1_relat_1(sK1)))
    | ~ v1_relat_1(k6_relat_1(k1_relat_1(sK1)))
    | sK0 != k1_relat_1(k6_relat_1(k1_relat_1(sK1)))
    | ~ r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(sK1))),sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl96_8
    | ~ spl96_109 ),
    inference(forward_demodulation,[],[f9161,f1975])).

fof(f9161,plain,
    ( sK2 = k6_relat_1(k1_relat_1(sK1))
    | ~ v1_funct_1(k6_relat_1(k1_relat_1(sK1)))
    | ~ v1_relat_1(k6_relat_1(k1_relat_1(sK1)))
    | sK0 != k1_relat_1(k6_relat_1(k1_relat_1(sK1)))
    | ~ r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(sK1))),sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl96_109 ),
    inference(trivial_inequality_removal,[],[f9154])).

fof(f9154,plain,
    ( sK1 != sK1
    | sK2 = k6_relat_1(k1_relat_1(sK1))
    | ~ v1_funct_1(k6_relat_1(k1_relat_1(sK1)))
    | ~ v1_relat_1(k6_relat_1(k1_relat_1(sK1)))
    | sK0 != k1_relat_1(k6_relat_1(k1_relat_1(sK1)))
    | ~ r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(sK1))),sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl96_109 ),
    inference(superposition,[],[f2556,f1339])).

fof(f1339,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f966])).

fof(f966,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f870])).

fof(f870,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

fof(f2556,plain,
    ( ! [X18] :
        ( sK1 != k5_relat_1(X18,sK1)
        | sK2 = X18
        | ~ v1_funct_1(X18)
        | ~ v1_relat_1(X18)
        | sK0 != k1_relat_1(X18)
        | ~ r1_tarski(k2_relat_1(X18),sK0) )
    | ~ spl96_109 ),
    inference(avatar_component_clause,[],[f2555])).

fof(f4337,plain,(
    spl96_217 ),
    inference(avatar_contradiction_clause,[],[f4333])).

fof(f4333,plain,
    ( $false
    | spl96_217 ),
    inference(resolution,[],[f3406,f1875])).

fof(f1875,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f1387])).

fof(f1387,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f3406,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl96_217 ),
    inference(avatar_component_clause,[],[f3404])).

fof(f4223,plain,(
    spl96_216 ),
    inference(avatar_contradiction_clause,[],[f4221])).

fof(f4221,plain,
    ( $false
    | spl96_216 ),
    inference(resolution,[],[f3402,f1344])).

fof(f1344,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f900])).

fof(f900,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f3402,plain,
    ( ~ v1_funct_1(k6_relat_1(sK0))
    | spl96_216 ),
    inference(avatar_component_clause,[],[f3400])).

fof(f3979,plain,(
    spl96_200 ),
    inference(avatar_contradiction_clause,[],[f3975])).

fof(f3975,plain,
    ( $false
    | spl96_200 ),
    inference(resolution,[],[f3320,f1345])).

fof(f1345,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f668])).

fof(f668,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f3320,plain,
    ( ~ v1_relat_1(k6_relat_1(sK0))
    | spl96_200 ),
    inference(avatar_component_clause,[],[f3318])).

fof(f2561,plain,
    ( ~ spl96_5
    | ~ spl96_2
    | ~ spl96_9
    | ~ spl96_10
    | ~ spl96_1
    | ~ spl96_6
    | spl96_109
    | ~ spl96_4
    | ~ spl96_7
    | ~ spl96_8 ),
    inference(avatar_split_clause,[],[f2560,f1973,f1968,f1953,f2555,f1963,f1938,f1983,f1978,f1943,f1958])).

fof(f1958,plain,
    ( spl96_5
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl96_5])])).

fof(f1978,plain,
    ( spl96_9
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl96_9])])).

fof(f1983,plain,
    ( spl96_10
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl96_10])])).

fof(f1938,plain,
    ( spl96_1
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl96_1])])).

fof(f1963,plain,
    ( spl96_6
  <=> r1_tarski(k2_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl96_6])])).

fof(f1953,plain,
    ( spl96_4
  <=> sK1 = k5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl96_4])])).

fof(f1968,plain,
    ( spl96_7
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl96_7])])).

fof(f2560,plain,
    ( ! [X19] :
        ( sK0 != k1_relat_1(X19)
        | ~ r1_tarski(k2_relat_1(sK2),sK0)
        | ~ r1_tarski(k2_relat_1(X19),sK0)
        | sK1 != k5_relat_1(X19,sK1)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19)
        | ~ v1_relat_1(sK2)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK1)
        | sK2 = X19
        | ~ v2_funct_1(sK1) )
    | ~ spl96_4
    | ~ spl96_7
    | ~ spl96_8 ),
    inference(forward_demodulation,[],[f2559,f1970])).

fof(f1970,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl96_7 ),
    inference(avatar_component_clause,[],[f1968])).

fof(f2559,plain,
    ( ! [X19] :
        ( ~ r1_tarski(k2_relat_1(sK2),sK0)
        | ~ r1_tarski(k2_relat_1(X19),sK0)
        | sK1 != k5_relat_1(X19,sK1)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19)
        | ~ v1_relat_1(sK2)
        | ~ v1_funct_1(sK2)
        | k1_relat_1(sK2) != k1_relat_1(X19)
        | ~ v1_relat_1(sK1)
        | sK2 = X19
        | ~ v2_funct_1(sK1) )
    | ~ spl96_4
    | ~ spl96_8 ),
    inference(forward_demodulation,[],[f2558,f1975])).

fof(f2558,plain,
    ( ! [X19] :
        ( ~ r1_tarski(k2_relat_1(X19),sK0)
        | sK1 != k5_relat_1(X19,sK1)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19)
        | ~ v1_relat_1(sK2)
        | ~ v1_funct_1(sK2)
        | ~ r1_tarski(k2_relat_1(sK2),k1_relat_1(sK1))
        | k1_relat_1(sK2) != k1_relat_1(X19)
        | ~ v1_relat_1(sK1)
        | sK2 = X19
        | ~ v2_funct_1(sK1) )
    | ~ spl96_4
    | ~ spl96_8 ),
    inference(forward_demodulation,[],[f2473,f1975])).

fof(f2473,plain,
    ( ! [X19] :
        ( sK1 != k5_relat_1(X19,sK1)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19)
        | ~ v1_relat_1(sK2)
        | ~ v1_funct_1(sK2)
        | ~ r1_tarski(k2_relat_1(X19),k1_relat_1(sK1))
        | ~ r1_tarski(k2_relat_1(sK2),k1_relat_1(sK1))
        | k1_relat_1(sK2) != k1_relat_1(X19)
        | ~ v1_relat_1(sK1)
        | sK2 = X19
        | ~ v2_funct_1(sK1) )
    | ~ spl96_4 ),
    inference(superposition,[],[f1383,f1955])).

fof(f1955,plain,
    ( sK1 = k5_relat_1(sK2,sK1)
    | ~ spl96_4 ),
    inference(avatar_component_clause,[],[f1953])).

fof(f1383,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X1,X0) != k5_relat_1(X2,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
      | k1_relat_1(X1) != k1_relat_1(X2)
      | ~ v1_relat_1(X0)
      | X1 = X2
      | ~ v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f1005])).

fof(f1005,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | k5_relat_1(X1,X0) != k5_relat_1(X2,X0)
                | k1_relat_1(X1) != k1_relat_1(X2)
                | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
                | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
                | ~ v1_funct_1(X2)
                | ~ v1_relat_1(X2) )
            | ~ v1_funct_1(X1)
            | ~ v1_relat_1(X1) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1004])).

fof(f1004,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | k5_relat_1(X1,X0) != k5_relat_1(X2,X0)
                | k1_relat_1(X1) != k1_relat_1(X2)
                | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
                | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
                | ~ v1_funct_1(X2)
                | ~ v1_relat_1(X2) )
            | ~ v1_funct_1(X1)
            | ~ v1_relat_1(X1) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f935])).

fof(f935,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( k5_relat_1(X1,X0) = k5_relat_1(X2,X0)
                    & k1_relat_1(X1) = k1_relat_1(X2)
                    & r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
                    & r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) )
                 => X1 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_funct_1)).

fof(f1986,plain,(
    spl96_10 ),
    inference(avatar_split_clause,[],[f1305,f1983])).

fof(f1305,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f947])).

fof(f947,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k6_relat_1(X0) != X2
          & k5_relat_1(X2,X1) = X1
          & v2_funct_1(X1)
          & r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X0
          & k1_relat_1(X1) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f946])).

fof(f946,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k6_relat_1(X0) != X2
          & k5_relat_1(X2,X1) = X1
          & v2_funct_1(X1)
          & r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X0
          & k1_relat_1(X1) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f937])).

fof(f937,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( ( k5_relat_1(X2,X1) = X1
                & v2_funct_1(X1)
                & r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X0
                & k1_relat_1(X1) = X0 )
             => k6_relat_1(X0) = X2 ) ) ) ),
    inference(negated_conjecture,[],[f936])).

fof(f936,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( ( k5_relat_1(X2,X1) = X1
              & v2_funct_1(X1)
              & r1_tarski(k2_relat_1(X2),X0)
              & k1_relat_1(X2) = X0
              & k1_relat_1(X1) = X0 )
           => k6_relat_1(X0) = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_funct_1)).

fof(f1981,plain,(
    spl96_9 ),
    inference(avatar_split_clause,[],[f1306,f1978])).

fof(f1306,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f947])).

fof(f1976,plain,(
    spl96_8 ),
    inference(avatar_split_clause,[],[f1307,f1973])).

fof(f1307,plain,(
    sK0 = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f947])).

fof(f1971,plain,(
    spl96_7 ),
    inference(avatar_split_clause,[],[f1308,f1968])).

fof(f1308,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f947])).

fof(f1966,plain,(
    spl96_6 ),
    inference(avatar_split_clause,[],[f1309,f1963])).

fof(f1309,plain,(
    r1_tarski(k2_relat_1(sK2),sK0) ),
    inference(cnf_transformation,[],[f947])).

fof(f1961,plain,(
    spl96_5 ),
    inference(avatar_split_clause,[],[f1310,f1958])).

fof(f1310,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f947])).

fof(f1956,plain,(
    spl96_4 ),
    inference(avatar_split_clause,[],[f1311,f1953])).

fof(f1311,plain,(
    sK1 = k5_relat_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f947])).

fof(f1951,plain,(
    ~ spl96_3 ),
    inference(avatar_split_clause,[],[f1312,f1948])).

fof(f1312,plain,(
    sK2 != k6_relat_1(sK0) ),
    inference(cnf_transformation,[],[f947])).

fof(f1946,plain,(
    spl96_2 ),
    inference(avatar_split_clause,[],[f1313,f1943])).

fof(f1313,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f947])).

fof(f1941,plain,(
    spl96_1 ),
    inference(avatar_split_clause,[],[f1314,f1938])).

fof(f1314,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f947])).
%------------------------------------------------------------------------------
