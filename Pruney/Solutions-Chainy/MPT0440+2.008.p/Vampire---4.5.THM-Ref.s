%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:57 EST 2020

% Result     : Theorem 2.16s
% Output     : Refutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 826 expanded)
%              Number of leaves         :   27 ( 271 expanded)
%              Depth                    :   17
%              Number of atoms          :  324 (1192 expanded)
%              Number of equality atoms :  127 ( 855 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2003,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f92,f367,f887,f902,f938,f962,f966,f970,f1023,f1980,f1988,f1996,f2002])).

fof(f2002,plain,
    ( ~ spl12_24
    | spl12_57
    | ~ spl12_58 ),
    inference(avatar_contradiction_clause,[],[f1999])).

fof(f1999,plain,
    ( $false
    | ~ spl12_24
    | spl12_57
    | ~ spl12_58 ),
    inference(unit_resulting_resolution,[],[f1974,f1979,f1094])).

fof(f1094,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_relat_1(sK2))
        | sK0 = X3 )
    | ~ spl12_24 ),
    inference(resolution,[],[f981,f73])).

fof(f73,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,sK4(X0,X2)),X0)
      | ~ r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,sK4(X0,X2)),X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f981,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | sK0 = X0 )
    | ~ spl12_24 ),
    inference(superposition,[],[f901,f294])).

fof(f294,plain,(
    ! [X0,X1] : sK10(k4_tarski(X0,X1)) = X0 ),
    inference(resolution,[],[f227,f79])).

fof(f79,plain,(
    ! [X2] : r2_hidden(X2,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) != X1 ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f33,f57])).

fof(f57,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f23,f56])).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f24,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f37,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f39,f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f49,f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f51,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f37,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f24,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f23,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f227,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))
      | sK10(k4_tarski(X0,X1)) = X2 ) ),
    inference(resolution,[],[f186,f80])).

fof(f80,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(k4_tarski(X0,X3),k2_zfmisc_1(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)))
      | ~ r2_hidden(X0,X2) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X2)
      | X1 != X3
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) ) ),
    inference(definition_unfolding,[],[f42,f57])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X2)
      | X1 != X3
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
    <=> ( X1 = X3
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).

fof(f186,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2))
      | sK10(X0) = X1 ) ),
    inference(condensation,[],[f185])).

fof(f185,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2))
      | sK10(X0) = X1
      | ~ r2_hidden(X0,k2_zfmisc_1(X3,X4)) ) ),
    inference(superposition,[],[f69,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(sK10(X0),sK11(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X0
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X3))
      | X0 = X2 ) ),
    inference(definition_unfolding,[],[f43,f57])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
    <=> ( r2_hidden(X1,X3)
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).

fof(f901,plain,
    ( ! [X36] :
        ( sK0 = sK10(X36)
        | ~ r2_hidden(X36,sK2) )
    | ~ spl12_24 ),
    inference(avatar_component_clause,[],[f900])).

fof(f900,plain,
    ( spl12_24
  <=> ! [X36] :
        ( sK0 = sK10(X36)
        | ~ r2_hidden(X36,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_24])])).

fof(f1979,plain,
    ( r2_hidden(sK9(sK0,k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ spl12_58 ),
    inference(avatar_component_clause,[],[f1977])).

fof(f1977,plain,
    ( spl12_58
  <=> r2_hidden(sK9(sK0,k1_relat_1(sK2)),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_58])])).

fof(f1974,plain,
    ( sK0 != sK9(sK0,k1_relat_1(sK2))
    | spl12_57 ),
    inference(avatar_component_clause,[],[f1973])).

fof(f1973,plain,
    ( spl12_57
  <=> sK0 = sK9(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_57])])).

fof(f1996,plain,(
    spl12_59 ),
    inference(avatar_contradiction_clause,[],[f1989])).

fof(f1989,plain,
    ( $false
    | spl12_59 ),
    inference(subsumption_resolution,[],[f821,f1987])).

fof(f1987,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | spl12_59 ),
    inference(avatar_component_clause,[],[f1985])).

fof(f1985,plain,
    ( spl12_59
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_59])])).

fof(f821,plain,(
    r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(resolution,[],[f794,f74])).

fof(f74,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f794,plain,(
    r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(superposition,[],[f79,f58])).

fof(f58,plain,(
    sK2 = k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)) ),
    inference(definition_unfolding,[],[f22,f57])).

fof(f22,plain,(
    sK2 = k1_tarski(k4_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relat_1(X2) != k1_tarski(X1)
        | k1_tarski(X0) != k1_relat_1(X2) )
      & k1_tarski(k4_tarski(X0,X1)) = X2
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relat_1(X2) != k1_tarski(X1)
        | k1_tarski(X0) != k1_relat_1(X2) )
      & k1_tarski(k4_tarski(X0,X1)) = X2
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( k1_tarski(k4_tarski(X0,X1)) = X2
         => ( k2_relat_1(X2) = k1_tarski(X1)
            & k1_tarski(X0) = k1_relat_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( k1_tarski(k4_tarski(X0,X1)) = X2
       => ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_tarski(X0) = k1_relat_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relat_1)).

fof(f1988,plain,
    ( spl12_2
    | ~ spl12_59
    | ~ spl12_57 ),
    inference(avatar_split_clause,[],[f1983,f1973,f1985,f89])).

fof(f89,plain,
    ( spl12_2
  <=> k1_relat_1(sK2) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f1983,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | k1_relat_1(sK2) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl12_57 ),
    inference(trivial_inequality_removal,[],[f1982])).

fof(f1982,plain,
    ( sK0 != sK0
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | k1_relat_1(sK2) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl12_57 ),
    inference(superposition,[],[f60,f1975])).

fof(f1975,plain,
    ( sK0 = sK9(sK0,k1_relat_1(sK2))
    | ~ spl12_57 ),
    inference(avatar_component_clause,[],[f1973])).

fof(f60,plain,(
    ! [X0,X1] :
      ( sK9(X0,X1) != X0
      | ~ r2_hidden(sK9(X0,X1),X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1 ) ),
    inference(definition_unfolding,[],[f36,f57])).

fof(f36,plain,(
    ! [X0,X1] :
      ( sK9(X0,X1) != X0
      | ~ r2_hidden(sK9(X0,X1),X1)
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1980,plain,
    ( spl12_57
    | spl12_58
    | spl12_2 ),
    inference(avatar_split_clause,[],[f1971,f89,f1977,f1973])).

fof(f1971,plain,
    ( r2_hidden(sK9(sK0,k1_relat_1(sK2)),k1_relat_1(sK2))
    | sK0 = sK9(sK0,k1_relat_1(sK2))
    | spl12_2 ),
    inference(equality_resolution,[],[f411])).

fof(f411,plain,
    ( ! [X0] :
        ( k1_relat_1(sK2) != X0
        | r2_hidden(sK9(sK0,X0),X0)
        | sK0 = sK9(sK0,X0) )
    | spl12_2 ),
    inference(superposition,[],[f91,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
      | r2_hidden(sK9(X0,X1),X1)
      | sK9(X0,X1) = X0 ) ),
    inference(definition_unfolding,[],[f35,f57])).

fof(f35,plain,(
    ! [X0,X1] :
      ( sK9(X0,X1) = X0
      | r2_hidden(sK9(X0,X1),X1)
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f91,plain,
    ( k1_relat_1(sK2) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | spl12_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f1023,plain,
    ( spl12_3
    | ~ spl12_4
    | ~ spl12_20 ),
    inference(avatar_contradiction_clause,[],[f1007])).

fof(f1007,plain,
    ( $false
    | spl12_3
    | ~ spl12_4
    | ~ spl12_20 ),
    inference(unit_resulting_resolution,[],[f361,f366,f1001])).

fof(f1001,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK2))
        | sK1 = X0 )
    | ~ spl12_20 ),
    inference(resolution,[],[f972,f75])).

fof(f75,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK7(X0,X2),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X2),X2),X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f972,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | sK1 = X1 )
    | ~ spl12_20 ),
    inference(superposition,[],[f886,f305])).

fof(f305,plain,(
    ! [X0,X1] : sK11(k4_tarski(X0,X1)) = X1 ),
    inference(resolution,[],[f249,f79])).

fof(f249,plain,(
    ! [X37,X38,X36] :
      ( ~ r2_hidden(X36,k6_enumset1(X37,X37,X37,X37,X37,X37,X37,X37))
      | sK11(k4_tarski(X38,X36)) = X37 ) ),
    inference(resolution,[],[f81,f135])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))
      | sK11(X0) = X2 ) ),
    inference(condensation,[],[f134])).

fof(f134,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))
      | sK11(X0) = X2
      | ~ r2_hidden(X0,k2_zfmisc_1(X3,X4)) ) ),
    inference(superposition,[],[f65,f38])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)))
      | X1 = X3 ) ),
    inference(definition_unfolding,[],[f41,f57])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f81,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X3))
      | ~ r2_hidden(X1,X3) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X2
      | ~ r2_hidden(X1,X3)
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X3)) ) ),
    inference(definition_unfolding,[],[f45,f57])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X2
      | ~ r2_hidden(X1,X3)
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f886,plain,
    ( ! [X28] :
        ( sK1 = sK11(X28)
        | ~ r2_hidden(X28,sK2) )
    | ~ spl12_20 ),
    inference(avatar_component_clause,[],[f885])).

fof(f885,plain,
    ( spl12_20
  <=> ! [X28] :
        ( sK1 = sK11(X28)
        | ~ r2_hidden(X28,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_20])])).

fof(f366,plain,
    ( r2_hidden(sK9(sK1,k2_relat_1(sK2)),k2_relat_1(sK2))
    | ~ spl12_4 ),
    inference(avatar_component_clause,[],[f364])).

fof(f364,plain,
    ( spl12_4
  <=> r2_hidden(sK9(sK1,k2_relat_1(sK2)),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f361,plain,
    ( sK1 != sK9(sK1,k2_relat_1(sK2))
    | spl12_3 ),
    inference(avatar_component_clause,[],[f360])).

fof(f360,plain,
    ( spl12_3
  <=> sK1 = sK9(sK1,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f970,plain,(
    spl12_17 ),
    inference(avatar_contradiction_clause,[],[f967])).

fof(f967,plain,
    ( $false
    | spl12_17 ),
    inference(subsumption_resolution,[],[f820,f780])).

fof(f780,plain,
    ( ~ r2_hidden(sK1,k2_relat_1(sK2))
    | spl12_17 ),
    inference(avatar_component_clause,[],[f778])).

fof(f778,plain,
    ( spl12_17
  <=> r2_hidden(sK1,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_17])])).

fof(f820,plain,(
    r2_hidden(sK1,k2_relat_1(sK2)) ),
    inference(resolution,[],[f794,f76])).

fof(f76,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f966,plain,
    ( spl12_1
    | ~ spl12_17
    | ~ spl12_3 ),
    inference(avatar_split_clause,[],[f965,f360,f778,f85])).

fof(f85,plain,
    ( spl12_1
  <=> k2_relat_1(sK2) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f965,plain,
    ( ~ r2_hidden(sK1,k2_relat_1(sK2))
    | k2_relat_1(sK2) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | ~ spl12_3 ),
    inference(trivial_inequality_removal,[],[f964])).

fof(f964,plain,
    ( sK1 != sK1
    | ~ r2_hidden(sK1,k2_relat_1(sK2))
    | k2_relat_1(sK2) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | ~ spl12_3 ),
    inference(superposition,[],[f60,f362])).

fof(f362,plain,
    ( sK1 = sK9(sK1,k2_relat_1(sK2))
    | ~ spl12_3 ),
    inference(avatar_component_clause,[],[f360])).

fof(f962,plain,(
    ~ spl12_23 ),
    inference(avatar_contradiction_clause,[],[f947])).

fof(f947,plain,
    ( $false
    | ~ spl12_23 ),
    inference(unit_resulting_resolution,[],[f83,f898,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X3))
      | r2_hidden(X1,X3) ) ),
    inference(definition_unfolding,[],[f44,f57])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f898,plain,
    ( ! [X37] : ~ r2_hidden(sK1,X37)
    | ~ spl12_23 ),
    inference(avatar_component_clause,[],[f897])).

fof(f897,plain,
    ( spl12_23
  <=> ! [X37] : ~ r2_hidden(sK1,X37) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_23])])).

fof(f83,plain,(
    ! [X2,X3] : r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X2,X3,X1] :
      ( X1 != X3
      | r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X2
      | X1 != X3
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) ) ),
    inference(definition_unfolding,[],[f48,f57,f57])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X2
      | X1 != X3
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
    <=> ( X1 = X3
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_zfmisc_1)).

fof(f938,plain,(
    ~ spl12_19 ),
    inference(avatar_contradiction_clause,[],[f913])).

fof(f913,plain,
    ( $false
    | ~ spl12_19 ),
    inference(subsumption_resolution,[],[f821,f883])).

fof(f883,plain,
    ( ! [X29] : ~ r2_hidden(sK0,X29)
    | ~ spl12_19 ),
    inference(avatar_component_clause,[],[f882])).

fof(f882,plain,
    ( spl12_19
  <=> ! [X29] : ~ r2_hidden(sK0,X29) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_19])])).

fof(f902,plain,
    ( spl12_23
    | spl12_24 ),
    inference(avatar_split_clause,[],[f867,f900,f897])).

fof(f867,plain,(
    ! [X37,X36] :
      ( sK0 = sK10(X36)
      | ~ r2_hidden(sK1,X37)
      | ~ r2_hidden(X36,sK2) ) ),
    inference(superposition,[],[f244,f793])).

fof(f793,plain,(
    ! [X13] :
      ( k4_tarski(sK0,sK1) = X13
      | ~ r2_hidden(X13,sK2) ) ),
    inference(superposition,[],[f77,f58])).

fof(f77,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f34,f57])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f244,plain,(
    ! [X21,X19,X20] :
      ( sK10(k4_tarski(X21,X19)) = X21
      | ~ r2_hidden(X19,X20) ) ),
    inference(resolution,[],[f81,f186])).

fof(f887,plain,
    ( spl12_19
    | spl12_20 ),
    inference(avatar_split_clause,[],[f864,f885,f882])).

fof(f864,plain,(
    ! [X28,X29] :
      ( sK1 = sK11(X28)
      | ~ r2_hidden(sK0,X29)
      | ~ r2_hidden(X28,sK2) ) ),
    inference(superposition,[],[f195,f793])).

fof(f195,plain,(
    ! [X24,X23,X22] :
      ( sK11(k4_tarski(X22,X24)) = X24
      | ~ r2_hidden(X22,X23) ) ),
    inference(resolution,[],[f80,f135])).

fof(f367,plain,
    ( spl12_3
    | spl12_4
    | spl12_1 ),
    inference(avatar_split_clause,[],[f358,f85,f364,f360])).

fof(f358,plain,
    ( r2_hidden(sK9(sK1,k2_relat_1(sK2)),k2_relat_1(sK2))
    | sK1 = sK9(sK1,k2_relat_1(sK2))
    | spl12_1 ),
    inference(equality_resolution,[],[f340])).

fof(f340,plain,
    ( ! [X89] :
        ( k2_relat_1(sK2) != X89
        | r2_hidden(sK9(sK1,X89),X89)
        | sK1 = sK9(sK1,X89) )
    | spl12_1 ),
    inference(superposition,[],[f87,f61])).

fof(f87,plain,
    ( k2_relat_1(sK2) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | spl12_1 ),
    inference(avatar_component_clause,[],[f85])).

fof(f92,plain,
    ( ~ spl12_1
    | ~ spl12_2 ),
    inference(avatar_split_clause,[],[f59,f89,f85])).

fof(f59,plain,
    ( k1_relat_1(sK2) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k2_relat_1(sK2) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f20,f57,f57])).

fof(f20,plain,
    ( k1_tarski(sK0) != k1_relat_1(sK2)
    | k2_relat_1(sK2) != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:03:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (18042)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (18040)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (18051)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (18044)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (18050)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (18045)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (18061)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (18058)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.53  % (18039)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (18053)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (18063)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.53  % (18054)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (18062)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (18059)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  % (18049)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.54  % (18052)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.54  % (18064)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (18057)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (18047)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (18041)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (18055)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (18043)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (18068)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (18068)Refutation not found, incomplete strategy% (18068)------------------------------
% 0.21/0.54  % (18068)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (18067)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (18066)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (18048)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (18055)Refutation not found, incomplete strategy% (18055)------------------------------
% 0.21/0.55  % (18055)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (18055)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (18055)Memory used [KB]: 10618
% 0.21/0.55  % (18055)Time elapsed: 0.119 s
% 0.21/0.55  % (18055)------------------------------
% 0.21/0.55  % (18055)------------------------------
% 0.21/0.55  % (18056)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.56  % (18068)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (18068)Memory used [KB]: 1663
% 0.21/0.56  % (18068)Time elapsed: 0.127 s
% 0.21/0.56  % (18068)------------------------------
% 0.21/0.56  % (18068)------------------------------
% 0.21/0.56  % (18046)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.56  % (18065)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (18060)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 2.16/0.68  % (18052)Refutation found. Thanks to Tanya!
% 2.16/0.68  % SZS status Theorem for theBenchmark
% 2.16/0.68  % SZS output start Proof for theBenchmark
% 2.16/0.68  fof(f2003,plain,(
% 2.16/0.68    $false),
% 2.16/0.68    inference(avatar_sat_refutation,[],[f92,f367,f887,f902,f938,f962,f966,f970,f1023,f1980,f1988,f1996,f2002])).
% 2.16/0.68  fof(f2002,plain,(
% 2.16/0.68    ~spl12_24 | spl12_57 | ~spl12_58),
% 2.16/0.68    inference(avatar_contradiction_clause,[],[f1999])).
% 2.16/0.68  fof(f1999,plain,(
% 2.16/0.68    $false | (~spl12_24 | spl12_57 | ~spl12_58)),
% 2.16/0.68    inference(unit_resulting_resolution,[],[f1974,f1979,f1094])).
% 2.16/0.68  fof(f1094,plain,(
% 2.16/0.68    ( ! [X3] : (~r2_hidden(X3,k1_relat_1(sK2)) | sK0 = X3) ) | ~spl12_24),
% 2.16/0.68    inference(resolution,[],[f981,f73])).
% 2.16/0.68  fof(f73,plain,(
% 2.16/0.68    ( ! [X2,X0] : (r2_hidden(k4_tarski(X2,sK4(X0,X2)),X0) | ~r2_hidden(X2,k1_relat_1(X0))) )),
% 2.16/0.68    inference(equality_resolution,[],[f26])).
% 2.16/0.68  fof(f26,plain,(
% 2.16/0.68    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,sK4(X0,X2)),X0) | ~r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 2.16/0.68    inference(cnf_transformation,[],[f13])).
% 2.16/0.68  fof(f13,axiom,(
% 2.16/0.68    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 2.16/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 2.16/0.68  fof(f981,plain,(
% 2.16/0.68    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | sK0 = X0) ) | ~spl12_24),
% 2.16/0.68    inference(superposition,[],[f901,f294])).
% 2.16/0.68  fof(f294,plain,(
% 2.16/0.68    ( ! [X0,X1] : (sK10(k4_tarski(X0,X1)) = X0) )),
% 2.16/0.68    inference(resolution,[],[f227,f79])).
% 2.16/0.68  fof(f79,plain,(
% 2.16/0.68    ( ! [X2] : (r2_hidden(X2,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))) )),
% 2.16/0.68    inference(equality_resolution,[],[f78])).
% 2.16/0.68  fof(f78,plain,(
% 2.16/0.68    ( ! [X2,X1] : (r2_hidden(X2,X1) | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) != X1) )),
% 2.16/0.68    inference(equality_resolution,[],[f63])).
% 2.16/0.68  fof(f63,plain,(
% 2.16/0.68    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 2.16/0.68    inference(definition_unfolding,[],[f33,f57])).
% 2.16/0.68  fof(f57,plain,(
% 2.16/0.68    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.16/0.68    inference(definition_unfolding,[],[f23,f56])).
% 2.16/0.68  fof(f56,plain,(
% 2.16/0.68    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.16/0.68    inference(definition_unfolding,[],[f24,f55])).
% 2.16/0.68  fof(f55,plain,(
% 2.16/0.68    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.16/0.68    inference(definition_unfolding,[],[f37,f54])).
% 2.16/0.68  fof(f54,plain,(
% 2.16/0.68    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.16/0.68    inference(definition_unfolding,[],[f39,f53])).
% 2.16/0.68  fof(f53,plain,(
% 2.16/0.68    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.16/0.68    inference(definition_unfolding,[],[f49,f52])).
% 2.16/0.68  fof(f52,plain,(
% 2.16/0.68    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.16/0.68    inference(definition_unfolding,[],[f50,f51])).
% 2.16/0.68  fof(f51,plain,(
% 2.16/0.68    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.16/0.68    inference(cnf_transformation,[],[f8])).
% 2.16/0.68  fof(f8,axiom,(
% 2.16/0.68    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.16/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 2.16/0.68  fof(f50,plain,(
% 2.16/0.68    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.16/0.68    inference(cnf_transformation,[],[f7])).
% 2.16/0.68  fof(f7,axiom,(
% 2.16/0.68    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.16/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 2.16/0.68  fof(f49,plain,(
% 2.16/0.68    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.16/0.68    inference(cnf_transformation,[],[f6])).
% 2.16/0.68  fof(f6,axiom,(
% 2.16/0.68    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.16/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 2.16/0.68  fof(f39,plain,(
% 2.16/0.68    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.16/0.68    inference(cnf_transformation,[],[f5])).
% 2.16/0.68  fof(f5,axiom,(
% 2.16/0.68    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.16/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 2.16/0.68  fof(f37,plain,(
% 2.16/0.68    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.16/0.68    inference(cnf_transformation,[],[f4])).
% 2.16/0.68  fof(f4,axiom,(
% 2.16/0.68    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.16/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.16/0.68  fof(f24,plain,(
% 2.16/0.68    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.16/0.68    inference(cnf_transformation,[],[f3])).
% 2.16/0.68  fof(f3,axiom,(
% 2.16/0.68    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.16/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.16/0.68  fof(f23,plain,(
% 2.16/0.68    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.16/0.68    inference(cnf_transformation,[],[f2])).
% 2.16/0.68  fof(f2,axiom,(
% 2.16/0.68    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.16/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.16/0.68  fof(f33,plain,(
% 2.16/0.68    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 2.16/0.68    inference(cnf_transformation,[],[f1])).
% 2.16/0.68  fof(f1,axiom,(
% 2.16/0.68    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.16/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 2.16/0.68  fof(f227,plain,(
% 2.16/0.68    ( ! [X2,X0,X1] : (~r2_hidden(X0,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) | sK10(k4_tarski(X0,X1)) = X2) )),
% 2.16/0.68    inference(resolution,[],[f186,f80])).
% 2.16/0.68  fof(f80,plain,(
% 2.16/0.68    ( ! [X2,X0,X3] : (r2_hidden(k4_tarski(X0,X3),k2_zfmisc_1(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) | ~r2_hidden(X0,X2)) )),
% 2.16/0.68    inference(equality_resolution,[],[f64])).
% 2.16/0.68  fof(f64,plain,(
% 2.16/0.68    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,X2) | X1 != X3 | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)))) )),
% 2.16/0.68    inference(definition_unfolding,[],[f42,f57])).
% 2.16/0.68  fof(f42,plain,(
% 2.16/0.68    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,X2) | X1 != X3 | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))) )),
% 2.16/0.68    inference(cnf_transformation,[],[f11])).
% 2.16/0.68  fof(f11,axiom,(
% 2.16/0.68    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <=> (X1 = X3 & r2_hidden(X0,X2)))),
% 2.16/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).
% 2.16/0.68  fof(f186,plain,(
% 2.16/0.68    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)) | sK10(X0) = X1) )),
% 2.16/0.68    inference(condensation,[],[f185])).
% 2.16/0.68  fof(f185,plain,(
% 2.16/0.68    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)) | sK10(X0) = X1 | ~r2_hidden(X0,k2_zfmisc_1(X3,X4))) )),
% 2.16/0.68    inference(superposition,[],[f69,f38])).
% 2.16/0.68  fof(f38,plain,(
% 2.16/0.68    ( ! [X2,X0,X1] : (k4_tarski(sK10(X0),sK11(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 2.16/0.68    inference(cnf_transformation,[],[f19])).
% 2.16/0.68  fof(f19,plain,(
% 2.16/0.68    ! [X0,X1,X2] : (? [X3,X4] : k4_tarski(X3,X4) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 2.16/0.68    inference(ennf_transformation,[],[f9])).
% 2.16/0.68  fof(f9,axiom,(
% 2.16/0.68    ! [X0,X1,X2] : ~(! [X3,X4] : k4_tarski(X3,X4) != X0 & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 2.16/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).
% 2.16/0.68  fof(f69,plain,(
% 2.16/0.68    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X3)) | X0 = X2) )),
% 2.16/0.68    inference(definition_unfolding,[],[f43,f57])).
% 2.16/0.68  fof(f43,plain,(
% 2.16/0.68    ( ! [X2,X0,X3,X1] : (X0 = X2 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))) )),
% 2.16/0.68    inference(cnf_transformation,[],[f10])).
% 2.16/0.68  fof(f10,axiom,(
% 2.16/0.68    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) <=> (r2_hidden(X1,X3) & X0 = X2))),
% 2.16/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).
% 2.16/0.68  fof(f901,plain,(
% 2.16/0.68    ( ! [X36] : (sK0 = sK10(X36) | ~r2_hidden(X36,sK2)) ) | ~spl12_24),
% 2.16/0.68    inference(avatar_component_clause,[],[f900])).
% 2.16/0.68  fof(f900,plain,(
% 2.16/0.68    spl12_24 <=> ! [X36] : (sK0 = sK10(X36) | ~r2_hidden(X36,sK2))),
% 2.16/0.68    introduced(avatar_definition,[new_symbols(naming,[spl12_24])])).
% 2.16/0.68  fof(f1979,plain,(
% 2.16/0.68    r2_hidden(sK9(sK0,k1_relat_1(sK2)),k1_relat_1(sK2)) | ~spl12_58),
% 2.16/0.68    inference(avatar_component_clause,[],[f1977])).
% 2.16/0.68  fof(f1977,plain,(
% 2.16/0.68    spl12_58 <=> r2_hidden(sK9(sK0,k1_relat_1(sK2)),k1_relat_1(sK2))),
% 2.16/0.68    introduced(avatar_definition,[new_symbols(naming,[spl12_58])])).
% 2.16/0.68  fof(f1974,plain,(
% 2.16/0.68    sK0 != sK9(sK0,k1_relat_1(sK2)) | spl12_57),
% 2.16/0.68    inference(avatar_component_clause,[],[f1973])).
% 2.16/0.68  fof(f1973,plain,(
% 2.16/0.68    spl12_57 <=> sK0 = sK9(sK0,k1_relat_1(sK2))),
% 2.16/0.68    introduced(avatar_definition,[new_symbols(naming,[spl12_57])])).
% 2.16/0.68  fof(f1996,plain,(
% 2.16/0.68    spl12_59),
% 2.16/0.68    inference(avatar_contradiction_clause,[],[f1989])).
% 2.16/0.68  fof(f1989,plain,(
% 2.16/0.68    $false | spl12_59),
% 2.16/0.68    inference(subsumption_resolution,[],[f821,f1987])).
% 2.16/0.68  fof(f1987,plain,(
% 2.16/0.68    ~r2_hidden(sK0,k1_relat_1(sK2)) | spl12_59),
% 2.16/0.68    inference(avatar_component_clause,[],[f1985])).
% 2.16/0.68  fof(f1985,plain,(
% 2.16/0.68    spl12_59 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 2.16/0.68    introduced(avatar_definition,[new_symbols(naming,[spl12_59])])).
% 2.16/0.68  fof(f821,plain,(
% 2.16/0.68    r2_hidden(sK0,k1_relat_1(sK2))),
% 2.16/0.68    inference(resolution,[],[f794,f74])).
% 2.16/0.68  fof(f74,plain,(
% 2.16/0.68    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,k1_relat_1(X0))) )),
% 2.16/0.68    inference(equality_resolution,[],[f25])).
% 2.16/0.68  fof(f25,plain,(
% 2.16/0.68    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 2.16/0.68    inference(cnf_transformation,[],[f13])).
% 2.16/0.68  fof(f794,plain,(
% 2.16/0.68    r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 2.16/0.68    inference(superposition,[],[f79,f58])).
% 2.16/0.68  fof(f58,plain,(
% 2.16/0.68    sK2 = k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))),
% 2.16/0.68    inference(definition_unfolding,[],[f22,f57])).
% 2.16/0.68  fof(f22,plain,(
% 2.16/0.68    sK2 = k1_tarski(k4_tarski(sK0,sK1))),
% 2.16/0.68    inference(cnf_transformation,[],[f18])).
% 2.16/0.68  fof(f18,plain,(
% 2.16/0.68    ? [X0,X1,X2] : ((k2_relat_1(X2) != k1_tarski(X1) | k1_tarski(X0) != k1_relat_1(X2)) & k1_tarski(k4_tarski(X0,X1)) = X2 & v1_relat_1(X2))),
% 2.16/0.68    inference(flattening,[],[f17])).
% 2.16/0.68  fof(f17,plain,(
% 2.16/0.68    ? [X0,X1,X2] : (((k2_relat_1(X2) != k1_tarski(X1) | k1_tarski(X0) != k1_relat_1(X2)) & k1_tarski(k4_tarski(X0,X1)) = X2) & v1_relat_1(X2))),
% 2.16/0.68    inference(ennf_transformation,[],[f16])).
% 2.16/0.68  fof(f16,negated_conjecture,(
% 2.16/0.68    ~! [X0,X1,X2] : (v1_relat_1(X2) => (k1_tarski(k4_tarski(X0,X1)) = X2 => (k2_relat_1(X2) = k1_tarski(X1) & k1_tarski(X0) = k1_relat_1(X2))))),
% 2.16/0.68    inference(negated_conjecture,[],[f15])).
% 2.16/0.68  fof(f15,conjecture,(
% 2.16/0.68    ! [X0,X1,X2] : (v1_relat_1(X2) => (k1_tarski(k4_tarski(X0,X1)) = X2 => (k2_relat_1(X2) = k1_tarski(X1) & k1_tarski(X0) = k1_relat_1(X2))))),
% 2.16/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relat_1)).
% 2.16/0.68  fof(f1988,plain,(
% 2.16/0.68    spl12_2 | ~spl12_59 | ~spl12_57),
% 2.16/0.68    inference(avatar_split_clause,[],[f1983,f1973,f1985,f89])).
% 2.16/0.68  fof(f89,plain,(
% 2.16/0.68    spl12_2 <=> k1_relat_1(sK2) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.16/0.68    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).
% 2.16/0.68  fof(f1983,plain,(
% 2.16/0.68    ~r2_hidden(sK0,k1_relat_1(sK2)) | k1_relat_1(sK2) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~spl12_57),
% 2.16/0.68    inference(trivial_inequality_removal,[],[f1982])).
% 2.16/0.68  fof(f1982,plain,(
% 2.16/0.68    sK0 != sK0 | ~r2_hidden(sK0,k1_relat_1(sK2)) | k1_relat_1(sK2) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~spl12_57),
% 2.16/0.68    inference(superposition,[],[f60,f1975])).
% 2.16/0.68  fof(f1975,plain,(
% 2.16/0.68    sK0 = sK9(sK0,k1_relat_1(sK2)) | ~spl12_57),
% 2.16/0.68    inference(avatar_component_clause,[],[f1973])).
% 2.16/0.68  fof(f60,plain,(
% 2.16/0.68    ( ! [X0,X1] : (sK9(X0,X1) != X0 | ~r2_hidden(sK9(X0,X1),X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1) )),
% 2.16/0.68    inference(definition_unfolding,[],[f36,f57])).
% 2.16/0.68  fof(f36,plain,(
% 2.16/0.68    ( ! [X0,X1] : (sK9(X0,X1) != X0 | ~r2_hidden(sK9(X0,X1),X1) | k1_tarski(X0) = X1) )),
% 2.16/0.68    inference(cnf_transformation,[],[f1])).
% 2.16/0.68  fof(f1980,plain,(
% 2.16/0.68    spl12_57 | spl12_58 | spl12_2),
% 2.16/0.68    inference(avatar_split_clause,[],[f1971,f89,f1977,f1973])).
% 2.16/0.68  fof(f1971,plain,(
% 2.16/0.68    r2_hidden(sK9(sK0,k1_relat_1(sK2)),k1_relat_1(sK2)) | sK0 = sK9(sK0,k1_relat_1(sK2)) | spl12_2),
% 2.16/0.68    inference(equality_resolution,[],[f411])).
% 2.16/0.68  fof(f411,plain,(
% 2.16/0.68    ( ! [X0] : (k1_relat_1(sK2) != X0 | r2_hidden(sK9(sK0,X0),X0) | sK0 = sK9(sK0,X0)) ) | spl12_2),
% 2.16/0.68    inference(superposition,[],[f91,f61])).
% 2.16/0.68  fof(f61,plain,(
% 2.16/0.68    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1 | r2_hidden(sK9(X0,X1),X1) | sK9(X0,X1) = X0) )),
% 2.16/0.68    inference(definition_unfolding,[],[f35,f57])).
% 2.16/0.68  fof(f35,plain,(
% 2.16/0.68    ( ! [X0,X1] : (sK9(X0,X1) = X0 | r2_hidden(sK9(X0,X1),X1) | k1_tarski(X0) = X1) )),
% 2.16/0.68    inference(cnf_transformation,[],[f1])).
% 2.16/0.68  fof(f91,plain,(
% 2.16/0.68    k1_relat_1(sK2) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | spl12_2),
% 2.16/0.68    inference(avatar_component_clause,[],[f89])).
% 2.16/0.68  fof(f1023,plain,(
% 2.16/0.68    spl12_3 | ~spl12_4 | ~spl12_20),
% 2.16/0.68    inference(avatar_contradiction_clause,[],[f1007])).
% 2.16/0.68  fof(f1007,plain,(
% 2.16/0.68    $false | (spl12_3 | ~spl12_4 | ~spl12_20)),
% 2.16/0.68    inference(unit_resulting_resolution,[],[f361,f366,f1001])).
% 2.16/0.68  fof(f1001,plain,(
% 2.16/0.68    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK2)) | sK1 = X0) ) | ~spl12_20),
% 2.16/0.68    inference(resolution,[],[f972,f75])).
% 2.16/0.68  fof(f75,plain,(
% 2.16/0.68    ( ! [X2,X0] : (r2_hidden(k4_tarski(sK7(X0,X2),X2),X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 2.16/0.68    inference(equality_resolution,[],[f30])).
% 2.16/0.68  fof(f30,plain,(
% 2.16/0.68    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK7(X0,X2),X2),X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 2.16/0.68    inference(cnf_transformation,[],[f14])).
% 2.16/0.68  fof(f14,axiom,(
% 2.16/0.68    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 2.16/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 2.16/0.68  fof(f972,plain,(
% 2.16/0.68    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | sK1 = X1) ) | ~spl12_20),
% 2.16/0.68    inference(superposition,[],[f886,f305])).
% 2.16/0.68  fof(f305,plain,(
% 2.16/0.68    ( ! [X0,X1] : (sK11(k4_tarski(X0,X1)) = X1) )),
% 2.16/0.68    inference(resolution,[],[f249,f79])).
% 2.16/0.68  fof(f249,plain,(
% 2.16/0.68    ( ! [X37,X38,X36] : (~r2_hidden(X36,k6_enumset1(X37,X37,X37,X37,X37,X37,X37,X37)) | sK11(k4_tarski(X38,X36)) = X37) )),
% 2.16/0.68    inference(resolution,[],[f81,f135])).
% 2.16/0.68  fof(f135,plain,(
% 2.16/0.68    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))) | sK11(X0) = X2) )),
% 2.16/0.68    inference(condensation,[],[f134])).
% 2.16/0.68  fof(f134,plain,(
% 2.16/0.68    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))) | sK11(X0) = X2 | ~r2_hidden(X0,k2_zfmisc_1(X3,X4))) )),
% 2.16/0.68    inference(superposition,[],[f65,f38])).
% 2.16/0.68  fof(f65,plain,(
% 2.16/0.68    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) | X1 = X3) )),
% 2.16/0.68    inference(definition_unfolding,[],[f41,f57])).
% 2.16/0.68  fof(f41,plain,(
% 2.16/0.68    ( ! [X2,X0,X3,X1] : (X1 = X3 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))) )),
% 2.16/0.68    inference(cnf_transformation,[],[f11])).
% 2.16/0.68  fof(f81,plain,(
% 2.16/0.68    ( ! [X2,X3,X1] : (r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X3)) | ~r2_hidden(X1,X3)) )),
% 2.16/0.68    inference(equality_resolution,[],[f67])).
% 2.16/0.68  fof(f67,plain,(
% 2.16/0.68    ( ! [X2,X0,X3,X1] : (X0 != X2 | ~r2_hidden(X1,X3) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X3))) )),
% 2.16/0.68    inference(definition_unfolding,[],[f45,f57])).
% 2.16/0.68  fof(f45,plain,(
% 2.16/0.68    ( ! [X2,X0,X3,X1] : (X0 != X2 | ~r2_hidden(X1,X3) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))) )),
% 2.16/0.68    inference(cnf_transformation,[],[f10])).
% 2.16/0.68  fof(f886,plain,(
% 2.16/0.68    ( ! [X28] : (sK1 = sK11(X28) | ~r2_hidden(X28,sK2)) ) | ~spl12_20),
% 2.16/0.68    inference(avatar_component_clause,[],[f885])).
% 2.16/0.68  fof(f885,plain,(
% 2.16/0.68    spl12_20 <=> ! [X28] : (sK1 = sK11(X28) | ~r2_hidden(X28,sK2))),
% 2.16/0.68    introduced(avatar_definition,[new_symbols(naming,[spl12_20])])).
% 2.16/0.68  fof(f366,plain,(
% 2.16/0.68    r2_hidden(sK9(sK1,k2_relat_1(sK2)),k2_relat_1(sK2)) | ~spl12_4),
% 2.16/0.68    inference(avatar_component_clause,[],[f364])).
% 2.16/0.68  fof(f364,plain,(
% 2.16/0.68    spl12_4 <=> r2_hidden(sK9(sK1,k2_relat_1(sK2)),k2_relat_1(sK2))),
% 2.16/0.68    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).
% 2.16/0.68  fof(f361,plain,(
% 2.16/0.68    sK1 != sK9(sK1,k2_relat_1(sK2)) | spl12_3),
% 2.16/0.68    inference(avatar_component_clause,[],[f360])).
% 2.16/0.68  fof(f360,plain,(
% 2.16/0.68    spl12_3 <=> sK1 = sK9(sK1,k2_relat_1(sK2))),
% 2.16/0.68    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).
% 2.16/0.68  fof(f970,plain,(
% 2.16/0.68    spl12_17),
% 2.16/0.68    inference(avatar_contradiction_clause,[],[f967])).
% 2.16/0.68  fof(f967,plain,(
% 2.16/0.68    $false | spl12_17),
% 2.16/0.68    inference(subsumption_resolution,[],[f820,f780])).
% 2.16/0.68  fof(f780,plain,(
% 2.16/0.68    ~r2_hidden(sK1,k2_relat_1(sK2)) | spl12_17),
% 2.16/0.68    inference(avatar_component_clause,[],[f778])).
% 2.16/0.68  fof(f778,plain,(
% 2.16/0.68    spl12_17 <=> r2_hidden(sK1,k2_relat_1(sK2))),
% 2.16/0.68    introduced(avatar_definition,[new_symbols(naming,[spl12_17])])).
% 2.16/0.68  fof(f820,plain,(
% 2.16/0.68    r2_hidden(sK1,k2_relat_1(sK2))),
% 2.16/0.68    inference(resolution,[],[f794,f76])).
% 2.16/0.68  fof(f76,plain,(
% 2.16/0.68    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,k2_relat_1(X0))) )),
% 2.16/0.68    inference(equality_resolution,[],[f29])).
% 2.16/0.68  fof(f29,plain,(
% 2.16/0.68    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 2.16/0.68    inference(cnf_transformation,[],[f14])).
% 2.16/0.68  fof(f966,plain,(
% 2.16/0.68    spl12_1 | ~spl12_17 | ~spl12_3),
% 2.16/0.68    inference(avatar_split_clause,[],[f965,f360,f778,f85])).
% 2.16/0.68  fof(f85,plain,(
% 2.16/0.68    spl12_1 <=> k2_relat_1(sK2) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),
% 2.16/0.68    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).
% 2.16/0.68  fof(f965,plain,(
% 2.16/0.68    ~r2_hidden(sK1,k2_relat_1(sK2)) | k2_relat_1(sK2) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | ~spl12_3),
% 2.16/0.68    inference(trivial_inequality_removal,[],[f964])).
% 2.16/0.68  fof(f964,plain,(
% 2.16/0.68    sK1 != sK1 | ~r2_hidden(sK1,k2_relat_1(sK2)) | k2_relat_1(sK2) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | ~spl12_3),
% 2.16/0.68    inference(superposition,[],[f60,f362])).
% 2.16/0.68  fof(f362,plain,(
% 2.16/0.68    sK1 = sK9(sK1,k2_relat_1(sK2)) | ~spl12_3),
% 2.16/0.68    inference(avatar_component_clause,[],[f360])).
% 2.16/0.68  fof(f962,plain,(
% 2.16/0.68    ~spl12_23),
% 2.16/0.68    inference(avatar_contradiction_clause,[],[f947])).
% 2.16/0.68  fof(f947,plain,(
% 2.16/0.68    $false | ~spl12_23),
% 2.16/0.68    inference(unit_resulting_resolution,[],[f83,f898,f68])).
% 2.16/0.68  fof(f68,plain,(
% 2.16/0.68    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X3)) | r2_hidden(X1,X3)) )),
% 2.16/0.68    inference(definition_unfolding,[],[f44,f57])).
% 2.16/0.68  fof(f44,plain,(
% 2.16/0.68    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))) )),
% 2.16/0.68    inference(cnf_transformation,[],[f10])).
% 2.16/0.68  fof(f898,plain,(
% 2.16/0.68    ( ! [X37] : (~r2_hidden(sK1,X37)) ) | ~spl12_23),
% 2.16/0.68    inference(avatar_component_clause,[],[f897])).
% 2.16/0.68  fof(f897,plain,(
% 2.16/0.68    spl12_23 <=> ! [X37] : ~r2_hidden(sK1,X37)),
% 2.16/0.68    introduced(avatar_definition,[new_symbols(naming,[spl12_23])])).
% 2.16/0.68  fof(f83,plain,(
% 2.16/0.68    ( ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)))) )),
% 2.16/0.68    inference(equality_resolution,[],[f82])).
% 2.16/0.68  fof(f82,plain,(
% 2.16/0.68    ( ! [X2,X3,X1] : (X1 != X3 | r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)))) )),
% 2.16/0.68    inference(equality_resolution,[],[f70])).
% 2.16/0.68  fof(f70,plain,(
% 2.16/0.68    ( ! [X2,X0,X3,X1] : (X0 != X2 | X1 != X3 | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)))) )),
% 2.16/0.68    inference(definition_unfolding,[],[f48,f57,f57])).
% 2.16/0.68  fof(f48,plain,(
% 2.16/0.68    ( ! [X2,X0,X3,X1] : (X0 != X2 | X1 != X3 | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))) )),
% 2.16/0.68    inference(cnf_transformation,[],[f12])).
% 2.16/0.68  fof(f12,axiom,(
% 2.16/0.68    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) <=> (X1 = X3 & X0 = X2))),
% 2.16/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_zfmisc_1)).
% 2.16/0.68  fof(f938,plain,(
% 2.16/0.68    ~spl12_19),
% 2.16/0.68    inference(avatar_contradiction_clause,[],[f913])).
% 2.16/0.68  fof(f913,plain,(
% 2.16/0.68    $false | ~spl12_19),
% 2.16/0.68    inference(subsumption_resolution,[],[f821,f883])).
% 2.16/0.68  fof(f883,plain,(
% 2.16/0.68    ( ! [X29] : (~r2_hidden(sK0,X29)) ) | ~spl12_19),
% 2.16/0.68    inference(avatar_component_clause,[],[f882])).
% 2.16/0.68  fof(f882,plain,(
% 2.16/0.68    spl12_19 <=> ! [X29] : ~r2_hidden(sK0,X29)),
% 2.16/0.68    introduced(avatar_definition,[new_symbols(naming,[spl12_19])])).
% 2.16/0.68  fof(f902,plain,(
% 2.16/0.68    spl12_23 | spl12_24),
% 2.16/0.68    inference(avatar_split_clause,[],[f867,f900,f897])).
% 2.16/0.68  fof(f867,plain,(
% 2.16/0.68    ( ! [X37,X36] : (sK0 = sK10(X36) | ~r2_hidden(sK1,X37) | ~r2_hidden(X36,sK2)) )),
% 2.16/0.68    inference(superposition,[],[f244,f793])).
% 2.16/0.68  fof(f793,plain,(
% 2.16/0.68    ( ! [X13] : (k4_tarski(sK0,sK1) = X13 | ~r2_hidden(X13,sK2)) )),
% 2.16/0.68    inference(superposition,[],[f77,f58])).
% 2.16/0.68  fof(f77,plain,(
% 2.16/0.68    ( ! [X2,X0] : (~r2_hidden(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) | X0 = X2) )),
% 2.16/0.68    inference(equality_resolution,[],[f62])).
% 2.16/0.68  fof(f62,plain,(
% 2.16/0.68    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 2.16/0.68    inference(definition_unfolding,[],[f34,f57])).
% 2.16/0.68  fof(f34,plain,(
% 2.16/0.68    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 2.16/0.68    inference(cnf_transformation,[],[f1])).
% 2.16/0.68  fof(f244,plain,(
% 2.16/0.68    ( ! [X21,X19,X20] : (sK10(k4_tarski(X21,X19)) = X21 | ~r2_hidden(X19,X20)) )),
% 2.16/0.68    inference(resolution,[],[f81,f186])).
% 2.16/0.68  fof(f887,plain,(
% 2.16/0.68    spl12_19 | spl12_20),
% 2.16/0.68    inference(avatar_split_clause,[],[f864,f885,f882])).
% 2.16/0.68  fof(f864,plain,(
% 2.16/0.68    ( ! [X28,X29] : (sK1 = sK11(X28) | ~r2_hidden(sK0,X29) | ~r2_hidden(X28,sK2)) )),
% 2.16/0.68    inference(superposition,[],[f195,f793])).
% 2.16/0.68  fof(f195,plain,(
% 2.16/0.68    ( ! [X24,X23,X22] : (sK11(k4_tarski(X22,X24)) = X24 | ~r2_hidden(X22,X23)) )),
% 2.16/0.68    inference(resolution,[],[f80,f135])).
% 2.16/0.68  fof(f367,plain,(
% 2.16/0.68    spl12_3 | spl12_4 | spl12_1),
% 2.16/0.68    inference(avatar_split_clause,[],[f358,f85,f364,f360])).
% 2.16/0.68  fof(f358,plain,(
% 2.16/0.68    r2_hidden(sK9(sK1,k2_relat_1(sK2)),k2_relat_1(sK2)) | sK1 = sK9(sK1,k2_relat_1(sK2)) | spl12_1),
% 2.16/0.68    inference(equality_resolution,[],[f340])).
% 2.16/0.68  fof(f340,plain,(
% 2.16/0.68    ( ! [X89] : (k2_relat_1(sK2) != X89 | r2_hidden(sK9(sK1,X89),X89) | sK1 = sK9(sK1,X89)) ) | spl12_1),
% 2.16/0.68    inference(superposition,[],[f87,f61])).
% 2.16/0.68  fof(f87,plain,(
% 2.16/0.68    k2_relat_1(sK2) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | spl12_1),
% 2.16/0.68    inference(avatar_component_clause,[],[f85])).
% 2.16/0.68  fof(f92,plain,(
% 2.16/0.68    ~spl12_1 | ~spl12_2),
% 2.16/0.68    inference(avatar_split_clause,[],[f59,f89,f85])).
% 2.16/0.68  fof(f59,plain,(
% 2.16/0.68    k1_relat_1(sK2) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | k2_relat_1(sK2) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),
% 2.16/0.68    inference(definition_unfolding,[],[f20,f57,f57])).
% 2.16/0.68  fof(f20,plain,(
% 2.16/0.68    k1_tarski(sK0) != k1_relat_1(sK2) | k2_relat_1(sK2) != k1_tarski(sK1)),
% 2.16/0.68    inference(cnf_transformation,[],[f18])).
% 2.16/0.68  % SZS output end Proof for theBenchmark
% 2.16/0.68  % (18052)------------------------------
% 2.16/0.68  % (18052)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.68  % (18052)Termination reason: Refutation
% 2.16/0.68  
% 2.16/0.68  % (18052)Memory used [KB]: 7419
% 2.16/0.68  % (18052)Time elapsed: 0.275 s
% 2.16/0.68  % (18052)------------------------------
% 2.16/0.68  % (18052)------------------------------
% 2.16/0.68  % (18038)Success in time 0.314 s
%------------------------------------------------------------------------------
