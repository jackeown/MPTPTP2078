%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:53 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 104 expanded)
%              Number of leaves         :   10 (  29 expanded)
%              Depth                    :   20
%              Number of atoms          :  237 ( 373 expanded)
%              Number of equality atoms :   72 ( 126 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (1747)Refutation not found, incomplete strategy% (1747)------------------------------
% (1747)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (1747)Termination reason: Refutation not found, incomplete strategy

% (1747)Memory used [KB]: 1663
% (1747)Time elapsed: 0.183 s
% (1747)------------------------------
% (1747)------------------------------
fof(f225,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f197,f209,f213,f217,f224])).

fof(f224,plain,(
    ~ spl8_5 ),
    inference(avatar_contradiction_clause,[],[f218])).

fof(f218,plain,
    ( $false
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f14,f208,f22])).

fof(f22,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f208,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f207])).

fof(f207,plain,
    ( spl8_5
  <=> ! [X0] : ~ r2_hidden(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f14,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
        ! [X2] :
          ( k2_relat_1(X2) != k1_tarski(X1)
          | k1_relat_1(X2) != X0
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( k1_xboole_0 != X0
       => ! [X1] :
          ? [X2] :
            ( k2_relat_1(X2) = k1_tarski(X1)
            & k1_relat_1(X2) = X0
            & v1_funct_1(X2)
            & v1_relat_1(X2) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

fof(f217,plain,(
    spl8_3 ),
    inference(avatar_contradiction_clause,[],[f214])).

fof(f214,plain,
    ( $false
    | spl8_3 ),
    inference(unit_resulting_resolution,[],[f29,f196])).

fof(f196,plain,
    ( ~ v1_funct_1(sK7(sK0,sK1))
    | spl8_3 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl8_3
  <=> v1_funct_1(sK7(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f29,plain,(
    ! [X0,X1] : v1_funct_1(sK7(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(f213,plain,(
    spl8_2 ),
    inference(avatar_contradiction_clause,[],[f210])).

fof(f210,plain,
    ( $false
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f28,f192])).

fof(f192,plain,
    ( ~ v1_relat_1(sK7(sK0,sK1))
    | spl8_2 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl8_2
  <=> v1_relat_1(sK7(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f28,plain,(
    ! [X0,X1] : v1_relat_1(sK7(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f209,plain,
    ( ~ spl8_2
    | ~ spl8_3
    | spl8_5
    | spl8_1 ),
    inference(avatar_split_clause,[],[f199,f186,f207,f194,f190])).

fof(f186,plain,
    ( spl8_1
  <=> r2_hidden(sK1,k2_relat_1(sK7(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f199,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ v1_funct_1(sK7(sK0,sK1))
        | ~ v1_relat_1(sK7(sK0,sK1)) )
    | spl8_1 ),
    inference(resolution,[],[f188,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k2_relat_1(sK7(X0,X1)))
      | ~ r2_hidden(X2,X0)
      | ~ v1_funct_1(sK7(X0,X1))
      | ~ v1_relat_1(sK7(X0,X1)) ) ),
    inference(duplicate_literal_removal,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X1,k2_relat_1(sK7(X0,X1)))
      | ~ v1_funct_1(sK7(X0,X1))
      | ~ v1_relat_1(sK7(X0,X1))
      | ~ r2_hidden(X2,X0) ) ),
    inference(forward_demodulation,[],[f47,f30])).

fof(f30,plain,(
    ! [X0,X1] : k1_relat_1(sK7(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k2_relat_1(sK7(X0,X1)))
      | ~ v1_funct_1(sK7(X0,X1))
      | ~ r2_hidden(X2,k1_relat_1(sK7(X0,X1)))
      | ~ v1_relat_1(sK7(X0,X1))
      | ~ r2_hidden(X2,X0) ) ),
    inference(superposition,[],[f37,f27])).

fof(f27,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(sK7(X0,X1),X3) = X1
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0,X3] :
      ( r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | r2_hidden(k1_funct_1(X0,X3),X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(f188,plain,
    ( ~ r2_hidden(sK1,k2_relat_1(sK7(sK0,sK1)))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f186])).

fof(f197,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f184,f194,f190,f186])).

fof(f184,plain,
    ( ~ v1_funct_1(sK7(sK0,sK1))
    | ~ v1_relat_1(sK7(sK0,sK1))
    | ~ r2_hidden(sK1,k2_relat_1(sK7(sK0,sK1))) ),
    inference(equality_resolution,[],[f183])).

fof(f183,plain,(
    ! [X0] :
      ( sK0 != X0
      | ~ v1_funct_1(sK7(X0,sK1))
      | ~ v1_relat_1(sK7(X0,sK1))
      | ~ r2_hidden(sK1,k2_relat_1(sK7(X0,sK1))) ) ),
    inference(equality_resolution,[],[f181])).

fof(f181,plain,(
    ! [X28,X29] :
      ( k2_tarski(sK1,sK1) != k2_tarski(X29,X29)
      | sK0 != X28
      | ~ v1_funct_1(sK7(X28,X29))
      | ~ v1_relat_1(sK7(X28,X29))
      | ~ r2_hidden(X29,k2_relat_1(sK7(X28,X29))) ) ),
    inference(forward_demodulation,[],[f170,f30])).

fof(f170,plain,(
    ! [X28,X29] :
      ( k2_tarski(sK1,sK1) != k2_tarski(X29,X29)
      | ~ v1_funct_1(sK7(X28,X29))
      | sK0 != k1_relat_1(sK7(X28,X29))
      | ~ v1_relat_1(sK7(X28,X29))
      | ~ r2_hidden(X29,k2_relat_1(sK7(X28,X29))) ) ),
    inference(duplicate_literal_removal,[],[f169])).

fof(f169,plain,(
    ! [X28,X29] :
      ( k2_tarski(sK1,sK1) != k2_tarski(X29,X29)
      | ~ v1_funct_1(sK7(X28,X29))
      | sK0 != k1_relat_1(sK7(X28,X29))
      | ~ v1_relat_1(sK7(X28,X29))
      | ~ r2_hidden(X29,k2_relat_1(sK7(X28,X29)))
      | ~ v1_funct_1(sK7(X28,X29))
      | ~ v1_relat_1(sK7(X28,X29)) ) ),
    inference(superposition,[],[f31,f150])).

fof(f150,plain,(
    ! [X4,X5] :
      ( k2_tarski(X4,X4) = k2_relat_1(sK7(X5,X4))
      | ~ r2_hidden(X4,k2_relat_1(sK7(X5,X4)))
      | ~ v1_funct_1(sK7(X5,X4))
      | ~ v1_relat_1(sK7(X5,X4)) ) ),
    inference(trivial_inequality_removal,[],[f149])).

fof(f149,plain,(
    ! [X4,X5] :
      ( X4 != X4
      | ~ r2_hidden(X4,k2_relat_1(sK7(X5,X4)))
      | k2_tarski(X4,X4) = k2_relat_1(sK7(X5,X4))
      | ~ v1_funct_1(sK7(X5,X4))
      | ~ v1_relat_1(sK7(X5,X4)) ) ),
    inference(duplicate_literal_removal,[],[f148])).

fof(f148,plain,(
    ! [X4,X5] :
      ( X4 != X4
      | ~ r2_hidden(X4,k2_relat_1(sK7(X5,X4)))
      | k2_tarski(X4,X4) = k2_relat_1(sK7(X5,X4))
      | ~ v1_funct_1(sK7(X5,X4))
      | ~ v1_relat_1(sK7(X5,X4))
      | k2_tarski(X4,X4) = k2_relat_1(sK7(X5,X4)) ) ),
    inference(superposition,[],[f32,f146])).

fof(f146,plain,(
    ! [X0,X1] :
      ( sK6(X1,k2_relat_1(sK7(X0,X1))) = X1
      | ~ v1_funct_1(sK7(X0,X1))
      | ~ v1_relat_1(sK7(X0,X1))
      | k2_tarski(X1,X1) = k2_relat_1(sK7(X0,X1)) ) ),
    inference(equality_resolution,[],[f143])).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ v1_funct_1(sK7(X1,X2))
      | sK6(X0,k2_relat_1(sK7(X1,X2))) = X2
      | ~ v1_relat_1(sK7(X1,X2))
      | k2_tarski(X0,X0) = k2_relat_1(sK7(X1,X2)) ) ),
    inference(equality_factoring,[],[f81])).

fof(f81,plain,(
    ! [X14,X12,X13] :
      ( sK6(X14,k2_relat_1(sK7(X12,X13))) = X14
      | ~ v1_funct_1(sK7(X12,X13))
      | sK6(X14,k2_relat_1(sK7(X12,X13))) = X13
      | ~ v1_relat_1(sK7(X12,X13))
      | k2_relat_1(sK7(X12,X13)) = k2_tarski(X14,X14) ) ),
    inference(resolution,[],[f76,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X1)
      | sK6(X0,X1) = X0
      | k2_tarski(X0,X0) = X1 ) ),
    inference(definition_unfolding,[],[f25,f15])).

fof(f15,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( sK6(X0,X1) = X0
      | r2_hidden(sK6(X0,X1),X1)
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_relat_1(sK7(X0,X1)))
      | ~ v1_relat_1(sK7(X0,X1))
      | ~ v1_funct_1(sK7(X0,X1))
      | X1 = X2 ) ),
    inference(duplicate_literal_removal,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(sK7(X0,X1))
      | ~ v1_relat_1(sK7(X0,X1))
      | ~ r2_hidden(X2,k2_relat_1(sK7(X0,X1)))
      | X1 = X2
      | ~ v1_funct_1(sK7(X0,X1))
      | ~ v1_relat_1(sK7(X0,X1))
      | ~ r2_hidden(X2,k2_relat_1(sK7(X0,X1))) ) ),
    inference(resolution,[],[f52,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(sK7(X0,X1),X2),X0)
      | ~ v1_funct_1(sK7(X0,X1))
      | ~ v1_relat_1(sK7(X0,X1))
      | ~ r2_hidden(X2,k2_relat_1(sK7(X0,X1))) ) ),
    inference(superposition,[],[f39,f30])).

fof(f39,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK3(X0,X2),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK3(X0,X2),k1_relat_1(X0))
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(sK7(X0,X1),X2),X0)
      | ~ v1_funct_1(sK7(X0,X1))
      | ~ v1_relat_1(sK7(X0,X1))
      | ~ r2_hidden(X2,k2_relat_1(sK7(X0,X1)))
      | X1 = X2 ) ),
    inference(superposition,[],[f38,f27])).

fof(f38,plain,(
    ! [X2,X0] :
      ( k1_funct_1(X0,sK3(X0,X2)) = X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK3(X0,X2)) = X2
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0,X1] :
      ( sK6(X0,X1) != X0
      | ~ r2_hidden(sK6(X0,X1),X1)
      | k2_tarski(X0,X0) = X1 ) ),
    inference(definition_unfolding,[],[f26,f15])).

fof(f26,plain,(
    ! [X0,X1] :
      ( sK6(X0,X1) != X0
      | ~ r2_hidden(sK6(X0,X1),X1)
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X2] :
      ( k2_relat_1(X2) != k2_tarski(sK1,sK1)
      | ~ v1_funct_1(X2)
      | k1_relat_1(X2) != sK0
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f13,f15])).

fof(f13,plain,(
    ! [X2] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k1_relat_1(X2) != sK0
      | k2_relat_1(X2) != k1_tarski(sK1) ) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:52:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.55  % (1734)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.55  % (1743)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.55  % (1743)Refutation not found, incomplete strategy% (1743)------------------------------
% 0.22/0.55  % (1743)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (1743)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (1743)Memory used [KB]: 1663
% 0.22/0.56  % (1743)Time elapsed: 0.120 s
% 0.22/0.56  % (1743)------------------------------
% 0.22/0.56  % (1743)------------------------------
% 0.22/0.56  % (1735)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (1730)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.57  % (1730)Refutation not found, incomplete strategy% (1730)------------------------------
% 0.22/0.57  % (1730)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (1751)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.58  % (1742)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.58  % (1730)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (1730)Memory used [KB]: 1663
% 0.22/0.58  % (1730)Time elapsed: 0.125 s
% 0.22/0.58  % (1730)------------------------------
% 0.22/0.58  % (1730)------------------------------
% 0.22/0.58  % (1750)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.59  % (1738)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.59  % (1742)Refutation found. Thanks to Tanya!
% 0.22/0.59  % SZS status Theorem for theBenchmark
% 0.22/0.59  % (1731)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.73/0.60  % (1746)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.73/0.60  % (1733)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.73/0.60  % (1732)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.73/0.60  % (1746)Refutation not found, incomplete strategy% (1746)------------------------------
% 1.73/0.60  % (1746)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.60  % (1746)Termination reason: Refutation not found, incomplete strategy
% 1.73/0.60  
% 1.73/0.60  % (1746)Memory used [KB]: 1663
% 1.73/0.60  % (1746)Time elapsed: 0.165 s
% 1.73/0.60  % (1746)------------------------------
% 1.73/0.60  % (1746)------------------------------
% 1.73/0.60  % (1754)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.73/0.61  % (1755)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.73/0.61  % (1755)Refutation not found, incomplete strategy% (1755)------------------------------
% 1.73/0.61  % (1755)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.61  % (1755)Termination reason: Refutation not found, incomplete strategy
% 1.73/0.61  
% 1.73/0.61  % (1755)Memory used [KB]: 6140
% 1.73/0.61  % (1755)Time elapsed: 0.171 s
% 1.73/0.61  % (1755)------------------------------
% 1.73/0.61  % (1755)------------------------------
% 1.73/0.61  % (1758)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.73/0.61  % (1757)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.73/0.61  % (1758)Refutation not found, incomplete strategy% (1758)------------------------------
% 1.73/0.61  % (1758)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.61  % (1758)Termination reason: Refutation not found, incomplete strategy
% 1.73/0.61  
% 1.73/0.61  % (1758)Memory used [KB]: 1663
% 1.73/0.61  % (1758)Time elapsed: 0.181 s
% 1.73/0.61  % (1758)------------------------------
% 1.73/0.61  % (1758)------------------------------
% 1.73/0.61  % (1757)Refutation not found, incomplete strategy% (1757)------------------------------
% 1.73/0.61  % (1757)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.61  % (1757)Termination reason: Refutation not found, incomplete strategy
% 1.73/0.61  
% 1.73/0.61  % (1757)Memory used [KB]: 10618
% 1.73/0.61  % (1757)Time elapsed: 0.184 s
% 1.73/0.61  % (1757)------------------------------
% 1.73/0.61  % (1757)------------------------------
% 1.73/0.61  % (1756)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.73/0.61  % (1756)Refutation not found, incomplete strategy% (1756)------------------------------
% 1.73/0.61  % (1756)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.61  % (1756)Termination reason: Refutation not found, incomplete strategy
% 1.73/0.61  
% 1.73/0.61  % (1756)Memory used [KB]: 6140
% 1.73/0.61  % (1756)Time elapsed: 0.181 s
% 1.73/0.61  % (1756)------------------------------
% 1.73/0.61  % (1756)------------------------------
% 1.73/0.61  % (1747)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.73/0.61  % SZS output start Proof for theBenchmark
% 1.73/0.61  % (1747)Refutation not found, incomplete strategy% (1747)------------------------------
% 1.73/0.61  % (1747)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.61  % (1747)Termination reason: Refutation not found, incomplete strategy
% 1.73/0.61  
% 1.73/0.61  % (1747)Memory used [KB]: 1663
% 1.73/0.61  % (1747)Time elapsed: 0.183 s
% 1.73/0.61  % (1747)------------------------------
% 1.73/0.61  % (1747)------------------------------
% 1.73/0.61  fof(f225,plain,(
% 1.73/0.61    $false),
% 1.73/0.61    inference(avatar_sat_refutation,[],[f197,f209,f213,f217,f224])).
% 1.73/0.61  fof(f224,plain,(
% 1.73/0.61    ~spl8_5),
% 1.73/0.61    inference(avatar_contradiction_clause,[],[f218])).
% 1.73/0.61  fof(f218,plain,(
% 1.73/0.61    $false | ~spl8_5),
% 1.73/0.61    inference(unit_resulting_resolution,[],[f14,f208,f22])).
% 1.73/0.61  fof(f22,plain,(
% 1.73/0.61    ( ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0) )),
% 1.73/0.61    inference(cnf_transformation,[],[f11])).
% 1.73/0.61  fof(f11,plain,(
% 1.73/0.61    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.73/0.61    inference(ennf_transformation,[],[f1])).
% 1.73/0.61  fof(f1,axiom,(
% 1.73/0.61    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.73/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.73/0.61  fof(f208,plain,(
% 1.73/0.61    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl8_5),
% 1.73/0.61    inference(avatar_component_clause,[],[f207])).
% 1.73/0.61  fof(f207,plain,(
% 1.73/0.61    spl8_5 <=> ! [X0] : ~r2_hidden(X0,sK0)),
% 1.73/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.73/0.61  fof(f14,plain,(
% 1.73/0.61    k1_xboole_0 != sK0),
% 1.73/0.61    inference(cnf_transformation,[],[f8])).
% 1.73/0.61  fof(f8,plain,(
% 1.73/0.61    ? [X0] : (? [X1] : ! [X2] : (k2_relat_1(X2) != k1_tarski(X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & k1_xboole_0 != X0)),
% 1.73/0.61    inference(ennf_transformation,[],[f7])).
% 1.73/0.61  fof(f7,negated_conjecture,(
% 1.73/0.61    ~! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.73/0.61    inference(negated_conjecture,[],[f6])).
% 1.73/0.61  fof(f6,conjecture,(
% 1.73/0.61    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.73/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).
% 1.73/0.61  fof(f217,plain,(
% 1.73/0.61    spl8_3),
% 1.73/0.61    inference(avatar_contradiction_clause,[],[f214])).
% 1.73/0.61  fof(f214,plain,(
% 1.73/0.61    $false | spl8_3),
% 1.73/0.61    inference(unit_resulting_resolution,[],[f29,f196])).
% 1.73/0.61  fof(f196,plain,(
% 1.73/0.61    ~v1_funct_1(sK7(sK0,sK1)) | spl8_3),
% 1.73/0.61    inference(avatar_component_clause,[],[f194])).
% 1.73/0.61  fof(f194,plain,(
% 1.73/0.61    spl8_3 <=> v1_funct_1(sK7(sK0,sK1))),
% 1.73/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.73/0.61  fof(f29,plain,(
% 1.73/0.61    ( ! [X0,X1] : (v1_funct_1(sK7(X0,X1))) )),
% 1.73/0.61    inference(cnf_transformation,[],[f12])).
% 1.73/0.61  fof(f12,plain,(
% 1.73/0.61    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.73/0.61    inference(ennf_transformation,[],[f5])).
% 1.73/0.61  fof(f5,axiom,(
% 1.73/0.61    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.73/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 1.73/0.61  fof(f213,plain,(
% 1.73/0.61    spl8_2),
% 1.73/0.61    inference(avatar_contradiction_clause,[],[f210])).
% 1.73/0.61  fof(f210,plain,(
% 1.73/0.61    $false | spl8_2),
% 1.73/0.61    inference(unit_resulting_resolution,[],[f28,f192])).
% 1.73/0.61  fof(f192,plain,(
% 1.73/0.61    ~v1_relat_1(sK7(sK0,sK1)) | spl8_2),
% 1.73/0.61    inference(avatar_component_clause,[],[f190])).
% 1.73/0.61  fof(f190,plain,(
% 1.73/0.61    spl8_2 <=> v1_relat_1(sK7(sK0,sK1))),
% 1.73/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.73/0.61  fof(f28,plain,(
% 1.73/0.61    ( ! [X0,X1] : (v1_relat_1(sK7(X0,X1))) )),
% 1.73/0.61    inference(cnf_transformation,[],[f12])).
% 1.73/0.61  fof(f209,plain,(
% 1.73/0.61    ~spl8_2 | ~spl8_3 | spl8_5 | spl8_1),
% 1.73/0.61    inference(avatar_split_clause,[],[f199,f186,f207,f194,f190])).
% 1.73/0.61  fof(f186,plain,(
% 1.73/0.61    spl8_1 <=> r2_hidden(sK1,k2_relat_1(sK7(sK0,sK1)))),
% 1.73/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.73/0.61  fof(f199,plain,(
% 1.73/0.61    ( ! [X0] : (~r2_hidden(X0,sK0) | ~v1_funct_1(sK7(sK0,sK1)) | ~v1_relat_1(sK7(sK0,sK1))) ) | spl8_1),
% 1.73/0.61    inference(resolution,[],[f188,f49])).
% 1.73/0.61  fof(f49,plain,(
% 1.73/0.61    ( ! [X2,X0,X1] : (r2_hidden(X1,k2_relat_1(sK7(X0,X1))) | ~r2_hidden(X2,X0) | ~v1_funct_1(sK7(X0,X1)) | ~v1_relat_1(sK7(X0,X1))) )),
% 1.73/0.61    inference(duplicate_literal_removal,[],[f48])).
% 1.73/0.61  fof(f48,plain,(
% 1.73/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X1,k2_relat_1(sK7(X0,X1))) | ~v1_funct_1(sK7(X0,X1)) | ~v1_relat_1(sK7(X0,X1)) | ~r2_hidden(X2,X0)) )),
% 1.73/0.61    inference(forward_demodulation,[],[f47,f30])).
% 1.73/0.61  fof(f30,plain,(
% 1.73/0.61    ( ! [X0,X1] : (k1_relat_1(sK7(X0,X1)) = X0) )),
% 1.73/0.61    inference(cnf_transformation,[],[f12])).
% 1.73/0.61  fof(f47,plain,(
% 1.73/0.61    ( ! [X2,X0,X1] : (r2_hidden(X1,k2_relat_1(sK7(X0,X1))) | ~v1_funct_1(sK7(X0,X1)) | ~r2_hidden(X2,k1_relat_1(sK7(X0,X1))) | ~v1_relat_1(sK7(X0,X1)) | ~r2_hidden(X2,X0)) )),
% 1.73/0.61    inference(superposition,[],[f37,f27])).
% 1.73/0.61  fof(f27,plain,(
% 1.73/0.61    ( ! [X0,X3,X1] : (k1_funct_1(sK7(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) )),
% 1.73/0.61    inference(cnf_transformation,[],[f12])).
% 1.73/0.61  fof(f37,plain,(
% 1.73/0.61    ( ! [X0,X3] : (r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.73/0.61    inference(equality_resolution,[],[f36])).
% 1.73/0.61  fof(f36,plain,(
% 1.73/0.61    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | r2_hidden(k1_funct_1(X0,X3),X1) | k2_relat_1(X0) != X1) )),
% 1.73/0.61    inference(equality_resolution,[],[f21])).
% 1.73/0.61  fof(f21,plain,(
% 1.73/0.61    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X0,X3) != X2 | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.73/0.61    inference(cnf_transformation,[],[f10])).
% 1.73/0.61  fof(f10,plain,(
% 1.73/0.61    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.73/0.61    inference(flattening,[],[f9])).
% 1.73/0.61  fof(f9,plain,(
% 1.73/0.61    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.73/0.61    inference(ennf_transformation,[],[f4])).
% 1.73/0.61  fof(f4,axiom,(
% 1.73/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.73/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 1.73/0.61  fof(f188,plain,(
% 1.73/0.61    ~r2_hidden(sK1,k2_relat_1(sK7(sK0,sK1))) | spl8_1),
% 1.73/0.61    inference(avatar_component_clause,[],[f186])).
% 1.73/0.61  fof(f197,plain,(
% 1.73/0.61    ~spl8_1 | ~spl8_2 | ~spl8_3),
% 1.73/0.61    inference(avatar_split_clause,[],[f184,f194,f190,f186])).
% 1.73/0.61  fof(f184,plain,(
% 1.73/0.61    ~v1_funct_1(sK7(sK0,sK1)) | ~v1_relat_1(sK7(sK0,sK1)) | ~r2_hidden(sK1,k2_relat_1(sK7(sK0,sK1)))),
% 1.73/0.61    inference(equality_resolution,[],[f183])).
% 1.73/0.61  fof(f183,plain,(
% 1.73/0.61    ( ! [X0] : (sK0 != X0 | ~v1_funct_1(sK7(X0,sK1)) | ~v1_relat_1(sK7(X0,sK1)) | ~r2_hidden(sK1,k2_relat_1(sK7(X0,sK1)))) )),
% 1.73/0.61    inference(equality_resolution,[],[f181])).
% 1.73/0.61  fof(f181,plain,(
% 1.73/0.61    ( ! [X28,X29] : (k2_tarski(sK1,sK1) != k2_tarski(X29,X29) | sK0 != X28 | ~v1_funct_1(sK7(X28,X29)) | ~v1_relat_1(sK7(X28,X29)) | ~r2_hidden(X29,k2_relat_1(sK7(X28,X29)))) )),
% 1.73/0.61    inference(forward_demodulation,[],[f170,f30])).
% 1.73/0.61  fof(f170,plain,(
% 1.73/0.61    ( ! [X28,X29] : (k2_tarski(sK1,sK1) != k2_tarski(X29,X29) | ~v1_funct_1(sK7(X28,X29)) | sK0 != k1_relat_1(sK7(X28,X29)) | ~v1_relat_1(sK7(X28,X29)) | ~r2_hidden(X29,k2_relat_1(sK7(X28,X29)))) )),
% 1.73/0.61    inference(duplicate_literal_removal,[],[f169])).
% 1.73/0.61  fof(f169,plain,(
% 1.73/0.61    ( ! [X28,X29] : (k2_tarski(sK1,sK1) != k2_tarski(X29,X29) | ~v1_funct_1(sK7(X28,X29)) | sK0 != k1_relat_1(sK7(X28,X29)) | ~v1_relat_1(sK7(X28,X29)) | ~r2_hidden(X29,k2_relat_1(sK7(X28,X29))) | ~v1_funct_1(sK7(X28,X29)) | ~v1_relat_1(sK7(X28,X29))) )),
% 1.73/0.61    inference(superposition,[],[f31,f150])).
% 1.73/0.61  fof(f150,plain,(
% 1.73/0.61    ( ! [X4,X5] : (k2_tarski(X4,X4) = k2_relat_1(sK7(X5,X4)) | ~r2_hidden(X4,k2_relat_1(sK7(X5,X4))) | ~v1_funct_1(sK7(X5,X4)) | ~v1_relat_1(sK7(X5,X4))) )),
% 1.73/0.61    inference(trivial_inequality_removal,[],[f149])).
% 1.73/0.61  fof(f149,plain,(
% 1.73/0.61    ( ! [X4,X5] : (X4 != X4 | ~r2_hidden(X4,k2_relat_1(sK7(X5,X4))) | k2_tarski(X4,X4) = k2_relat_1(sK7(X5,X4)) | ~v1_funct_1(sK7(X5,X4)) | ~v1_relat_1(sK7(X5,X4))) )),
% 1.73/0.61    inference(duplicate_literal_removal,[],[f148])).
% 1.73/0.61  fof(f148,plain,(
% 1.73/0.61    ( ! [X4,X5] : (X4 != X4 | ~r2_hidden(X4,k2_relat_1(sK7(X5,X4))) | k2_tarski(X4,X4) = k2_relat_1(sK7(X5,X4)) | ~v1_funct_1(sK7(X5,X4)) | ~v1_relat_1(sK7(X5,X4)) | k2_tarski(X4,X4) = k2_relat_1(sK7(X5,X4))) )),
% 1.73/0.61    inference(superposition,[],[f32,f146])).
% 1.73/0.61  fof(f146,plain,(
% 1.73/0.61    ( ! [X0,X1] : (sK6(X1,k2_relat_1(sK7(X0,X1))) = X1 | ~v1_funct_1(sK7(X0,X1)) | ~v1_relat_1(sK7(X0,X1)) | k2_tarski(X1,X1) = k2_relat_1(sK7(X0,X1))) )),
% 1.73/0.61    inference(equality_resolution,[],[f143])).
% 1.73/0.61  fof(f143,plain,(
% 1.73/0.61    ( ! [X2,X0,X1] : (X0 != X2 | ~v1_funct_1(sK7(X1,X2)) | sK6(X0,k2_relat_1(sK7(X1,X2))) = X2 | ~v1_relat_1(sK7(X1,X2)) | k2_tarski(X0,X0) = k2_relat_1(sK7(X1,X2))) )),
% 1.73/0.61    inference(equality_factoring,[],[f81])).
% 1.73/0.61  fof(f81,plain,(
% 1.73/0.61    ( ! [X14,X12,X13] : (sK6(X14,k2_relat_1(sK7(X12,X13))) = X14 | ~v1_funct_1(sK7(X12,X13)) | sK6(X14,k2_relat_1(sK7(X12,X13))) = X13 | ~v1_relat_1(sK7(X12,X13)) | k2_relat_1(sK7(X12,X13)) = k2_tarski(X14,X14)) )),
% 1.73/0.61    inference(resolution,[],[f76,f33])).
% 1.73/0.61  fof(f33,plain,(
% 1.73/0.61    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X1) | sK6(X0,X1) = X0 | k2_tarski(X0,X0) = X1) )),
% 1.73/0.61    inference(definition_unfolding,[],[f25,f15])).
% 1.73/0.61  fof(f15,plain,(
% 1.73/0.61    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.73/0.61    inference(cnf_transformation,[],[f3])).
% 1.73/0.61  fof(f3,axiom,(
% 1.73/0.61    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.73/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.73/0.61  fof(f25,plain,(
% 1.73/0.61    ( ! [X0,X1] : (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1) | k1_tarski(X0) = X1) )),
% 1.73/0.61    inference(cnf_transformation,[],[f2])).
% 1.73/0.61  fof(f2,axiom,(
% 1.73/0.61    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.73/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.73/0.61  fof(f76,plain,(
% 1.73/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X2,k2_relat_1(sK7(X0,X1))) | ~v1_relat_1(sK7(X0,X1)) | ~v1_funct_1(sK7(X0,X1)) | X1 = X2) )),
% 1.73/0.61    inference(duplicate_literal_removal,[],[f75])).
% 1.73/0.61  fof(f75,plain,(
% 1.73/0.61    ( ! [X2,X0,X1] : (~v1_funct_1(sK7(X0,X1)) | ~v1_relat_1(sK7(X0,X1)) | ~r2_hidden(X2,k2_relat_1(sK7(X0,X1))) | X1 = X2 | ~v1_funct_1(sK7(X0,X1)) | ~v1_relat_1(sK7(X0,X1)) | ~r2_hidden(X2,k2_relat_1(sK7(X0,X1)))) )),
% 1.73/0.61    inference(resolution,[],[f52,f50])).
% 1.73/0.61  fof(f50,plain,(
% 1.73/0.61    ( ! [X2,X0,X1] : (r2_hidden(sK3(sK7(X0,X1),X2),X0) | ~v1_funct_1(sK7(X0,X1)) | ~v1_relat_1(sK7(X0,X1)) | ~r2_hidden(X2,k2_relat_1(sK7(X0,X1)))) )),
% 1.73/0.61    inference(superposition,[],[f39,f30])).
% 1.73/0.61  fof(f39,plain,(
% 1.73/0.61    ( ! [X2,X0] : (r2_hidden(sK3(X0,X2),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 1.73/0.61    inference(equality_resolution,[],[f19])).
% 1.73/0.61  fof(f19,plain,(
% 1.73/0.61    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK3(X0,X2),k1_relat_1(X0)) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.73/0.61    inference(cnf_transformation,[],[f10])).
% 1.73/0.61  fof(f52,plain,(
% 1.73/0.61    ( ! [X2,X0,X1] : (~r2_hidden(sK3(sK7(X0,X1),X2),X0) | ~v1_funct_1(sK7(X0,X1)) | ~v1_relat_1(sK7(X0,X1)) | ~r2_hidden(X2,k2_relat_1(sK7(X0,X1))) | X1 = X2) )),
% 1.73/0.61    inference(superposition,[],[f38,f27])).
% 1.73/0.61  fof(f38,plain,(
% 1.73/0.61    ( ! [X2,X0] : (k1_funct_1(X0,sK3(X0,X2)) = X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 1.73/0.61    inference(equality_resolution,[],[f20])).
% 1.73/0.61  fof(f20,plain,(
% 1.73/0.61    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK3(X0,X2)) = X2 | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.73/0.61    inference(cnf_transformation,[],[f10])).
% 1.73/0.61  fof(f32,plain,(
% 1.73/0.61    ( ! [X0,X1] : (sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1) | k2_tarski(X0,X0) = X1) )),
% 1.73/0.61    inference(definition_unfolding,[],[f26,f15])).
% 1.73/0.61  fof(f26,plain,(
% 1.73/0.61    ( ! [X0,X1] : (sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1) | k1_tarski(X0) = X1) )),
% 1.73/0.61    inference(cnf_transformation,[],[f2])).
% 1.73/0.61  fof(f31,plain,(
% 1.73/0.61    ( ! [X2] : (k2_relat_1(X2) != k2_tarski(sK1,sK1) | ~v1_funct_1(X2) | k1_relat_1(X2) != sK0 | ~v1_relat_1(X2)) )),
% 1.73/0.61    inference(definition_unfolding,[],[f13,f15])).
% 1.97/0.61  fof(f13,plain,(
% 1.97/0.61    ( ! [X2] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_relat_1(X2) != sK0 | k2_relat_1(X2) != k1_tarski(sK1)) )),
% 1.97/0.61    inference(cnf_transformation,[],[f8])).
% 1.97/0.61  % SZS output end Proof for theBenchmark
% 1.97/0.61  % (1742)------------------------------
% 1.97/0.61  % (1742)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.97/0.61  % (1742)Termination reason: Refutation
% 1.97/0.61  
% 1.97/0.61  % (1742)Memory used [KB]: 6396
% 1.97/0.61  % (1742)Time elapsed: 0.156 s
% 1.97/0.61  % (1742)------------------------------
% 1.97/0.61  % (1742)------------------------------
% 1.97/0.61  % (1745)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.97/0.61  % (1728)Success in time 0.245 s
%------------------------------------------------------------------------------
