%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:36 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 176 expanded)
%              Number of leaves         :   13 (  57 expanded)
%              Depth                    :   11
%              Number of atoms          :  261 ( 843 expanded)
%              Number of equality atoms :   55 ( 191 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f583,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f66,f318,f415,f517,f523,f531,f582])).

fof(f582,plain,
    ( ~ spl3_2
    | spl3_12
    | ~ spl3_15 ),
    inference(avatar_contradiction_clause,[],[f577])).

fof(f577,plain,
    ( $false
    | ~ spl3_2
    | spl3_12
    | ~ spl3_15 ),
    inference(unit_resulting_resolution,[],[f295,f435,f108])).

fof(f108,plain,
    ( ! [X4] :
        ( r2_hidden(X4,sK0)
        | ~ r2_hidden(X4,k1_xboole_0) )
    | ~ spl3_2 ),
    inference(superposition,[],[f47,f68])).

% (26927)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
fof(f68,plain,
    ( k1_xboole_0 = k3_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl3_2 ),
    inference(resolution,[],[f61,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f61,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl3_2
  <=> r1_xboole_0(k2_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f47,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f435,plain,
    ( r2_hidden(sK2(sK0,k2_relat_1(sK1),k1_xboole_0),k1_xboole_0)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f434])).

fof(f434,plain,
    ( spl3_15
  <=> r2_hidden(sK2(sK0,k2_relat_1(sK1),k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f295,plain,
    ( ~ r2_hidden(sK2(sK0,k2_relat_1(sK1),k1_xboole_0),sK0)
    | spl3_12 ),
    inference(avatar_component_clause,[],[f294])).

fof(f294,plain,
    ( spl3_12
  <=> r2_hidden(sK2(sK0,k2_relat_1(sK1),k1_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f531,plain,
    ( spl3_15
    | spl3_4
    | spl3_12 ),
    inference(avatar_split_clause,[],[f530,f294,f86,f434])).

fof(f86,plain,
    ( spl3_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f530,plain,
    ( k1_xboole_0 = sK0
    | r2_hidden(sK2(sK0,k2_relat_1(sK1),k1_xboole_0),k1_xboole_0)
    | spl3_12 ),
    inference(forward_demodulation,[],[f525,f51])).

fof(f51,plain,(
    sK0 = k3_xboole_0(sK0,k2_relat_1(sK1)) ),
    inference(resolution,[],[f33,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f33,plain,(
    r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,sK0)
    & r1_tarski(sK0,k2_relat_1(sK1))
    & k1_xboole_0 != sK0
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 = k10_relat_1(X1,X0)
        & r1_tarski(X0,k2_relat_1(X1))
        & k1_xboole_0 != X0
        & v1_relat_1(X1) )
   => ( k1_xboole_0 = k10_relat_1(sK1,sK0)
      & r1_tarski(sK0,k2_relat_1(sK1))
      & k1_xboole_0 != sK0
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k10_relat_1(X1,X0)
      & r1_tarski(X0,k2_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k10_relat_1(X1,X0)
      & r1_tarski(X0,k2_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ~ ( k1_xboole_0 = k10_relat_1(X1,X0)
            & r1_tarski(X0,k2_relat_1(X1))
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k10_relat_1(X1,X0)
          & r1_tarski(X0,k2_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).

fof(f525,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k2_relat_1(sK1))
    | r2_hidden(sK2(sK0,k2_relat_1(sK1),k1_xboole_0),k1_xboole_0)
    | spl3_12 ),
    inference(resolution,[],[f295,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f523,plain,
    ( ~ spl3_15
    | ~ spl3_12
    | spl3_4
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f463,f298,f86,f294,f434])).

fof(f298,plain,
    ( spl3_13
  <=> r2_hidden(sK2(sK0,k2_relat_1(sK1),k1_xboole_0),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f463,plain,
    ( k1_xboole_0 = sK0
    | ~ r2_hidden(sK2(sK0,k2_relat_1(sK1),k1_xboole_0),sK0)
    | ~ r2_hidden(sK2(sK0,k2_relat_1(sK1),k1_xboole_0),k1_xboole_0)
    | ~ spl3_13 ),
    inference(resolution,[],[f300,f71])).

fof(f71,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK2(sK0,k2_relat_1(sK1),X2),k2_relat_1(sK1))
      | sK0 = X2
      | ~ r2_hidden(sK2(sK0,k2_relat_1(sK1),X2),sK0)
      | ~ r2_hidden(sK2(sK0,k2_relat_1(sK1),X2),X2) ) ),
    inference(superposition,[],[f51,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f300,plain,
    ( r2_hidden(sK2(sK0,k2_relat_1(sK1),k1_xboole_0),k2_relat_1(sK1))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f298])).

fof(f517,plain,
    ( ~ spl3_13
    | spl3_15
    | ~ spl3_2
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f512,f294,f59,f434,f298])).

fof(f512,plain,
    ( r2_hidden(sK2(sK0,k2_relat_1(sK1),k1_xboole_0),k1_xboole_0)
    | ~ r2_hidden(sK2(sK0,k2_relat_1(sK1),k1_xboole_0),k2_relat_1(sK1))
    | ~ spl3_2
    | ~ spl3_12 ),
    inference(resolution,[],[f107,f296])).

fof(f296,plain,
    ( r2_hidden(sK2(sK0,k2_relat_1(sK1),k1_xboole_0),sK0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f294])).

fof(f107,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK0)
        | r2_hidden(X3,k1_xboole_0)
        | ~ r2_hidden(X3,k2_relat_1(sK1)) )
    | ~ spl3_2 ),
    inference(superposition,[],[f46,f68])).

fof(f46,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f415,plain,
    ( spl3_4
    | spl3_13
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f414,f59,f298,f86])).

fof(f414,plain,
    ( r2_hidden(sK2(sK0,k2_relat_1(sK1),k1_xboole_0),k2_relat_1(sK1))
    | k1_xboole_0 = sK0
    | ~ spl3_2 ),
    inference(duplicate_literal_removal,[],[f410])).

fof(f410,plain,
    ( r2_hidden(sK2(sK0,k2_relat_1(sK1),k1_xboole_0),k2_relat_1(sK1))
    | k1_xboole_0 = sK0
    | r2_hidden(sK2(sK0,k2_relat_1(sK1),k1_xboole_0),k2_relat_1(sK1))
    | ~ spl3_2 ),
    inference(resolution,[],[f70,f109])).

fof(f109,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,k1_xboole_0)
        | r2_hidden(X5,k2_relat_1(sK1)) )
    | ~ spl3_2 ),
    inference(superposition,[],[f48,f68])).

fof(f48,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f70,plain,(
    ! [X1] :
      ( r2_hidden(sK2(sK0,k2_relat_1(sK1),X1),k2_relat_1(sK1))
      | r2_hidden(sK2(sK0,k2_relat_1(sK1),X1),X1)
      | sK0 = X1 ) ),
    inference(superposition,[],[f51,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f318,plain,(
    ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f314])).

fof(f314,plain,
    ( $false
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f32,f88])).

fof(f88,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f86])).

fof(f32,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f23])).

fof(f66,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f63])).

fof(f63,plain,
    ( $false
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f31,f57])).

fof(f57,plain,
    ( ~ v1_relat_1(sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl3_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f31,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f62,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f53,f59,f55])).

fof(f53,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK1) ),
    inference(trivial_inequality_removal,[],[f52])).

fof(f52,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f35,f34])).

fof(f34,plain,(
    k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_relat_1(X1),X0)
      | k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k10_relat_1(X1,X0)
          | ~ r1_xboole_0(k2_relat_1(X1),X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:34:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (26932)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.50  % (26920)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.51  % (26924)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.51  % (26928)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.51  % (26919)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.52  % (26924)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f583,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f62,f66,f318,f415,f517,f523,f531,f582])).
% 0.22/0.52  fof(f582,plain,(
% 0.22/0.52    ~spl3_2 | spl3_12 | ~spl3_15),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f577])).
% 0.22/0.52  fof(f577,plain,(
% 0.22/0.52    $false | (~spl3_2 | spl3_12 | ~spl3_15)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f295,f435,f108])).
% 0.22/0.52  fof(f108,plain,(
% 0.22/0.52    ( ! [X4] : (r2_hidden(X4,sK0) | ~r2_hidden(X4,k1_xboole_0)) ) | ~spl3_2),
% 0.22/0.52    inference(superposition,[],[f47,f68])).
% 0.22/0.52  % (26927)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    k1_xboole_0 = k3_xboole_0(k2_relat_1(sK1),sK0) | ~spl3_2),
% 0.22/0.52    inference(resolution,[],[f61,f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.52    inference(nnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    r1_xboole_0(k2_relat_1(sK1),sK0) | ~spl3_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f59])).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    spl3_2 <=> r1_xboole_0(k2_relat_1(sK1),sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 0.22/0.52    inference(equality_resolution,[],[f40])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.22/0.52    inference(cnf_transformation,[],[f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.52    inference(rectify,[],[f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.52    inference(flattening,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.52    inference(nnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.22/0.52  fof(f435,plain,(
% 0.22/0.52    r2_hidden(sK2(sK0,k2_relat_1(sK1),k1_xboole_0),k1_xboole_0) | ~spl3_15),
% 0.22/0.52    inference(avatar_component_clause,[],[f434])).
% 0.22/0.52  fof(f434,plain,(
% 0.22/0.52    spl3_15 <=> r2_hidden(sK2(sK0,k2_relat_1(sK1),k1_xboole_0),k1_xboole_0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.52  fof(f295,plain,(
% 0.22/0.52    ~r2_hidden(sK2(sK0,k2_relat_1(sK1),k1_xboole_0),sK0) | spl3_12),
% 0.22/0.52    inference(avatar_component_clause,[],[f294])).
% 0.22/0.52  fof(f294,plain,(
% 0.22/0.52    spl3_12 <=> r2_hidden(sK2(sK0,k2_relat_1(sK1),k1_xboole_0),sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.52  fof(f531,plain,(
% 0.22/0.52    spl3_15 | spl3_4 | spl3_12),
% 0.22/0.52    inference(avatar_split_clause,[],[f530,f294,f86,f434])).
% 0.22/0.52  fof(f86,plain,(
% 0.22/0.52    spl3_4 <=> k1_xboole_0 = sK0),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.52  fof(f530,plain,(
% 0.22/0.52    k1_xboole_0 = sK0 | r2_hidden(sK2(sK0,k2_relat_1(sK1),k1_xboole_0),k1_xboole_0) | spl3_12),
% 0.22/0.52    inference(forward_demodulation,[],[f525,f51])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    sK0 = k3_xboole_0(sK0,k2_relat_1(sK1))),
% 0.22/0.52    inference(resolution,[],[f33,f45])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    r1_tarski(sK0,k2_relat_1(sK1))),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    k1_xboole_0 = k10_relat_1(sK1,sK0) & r1_tarski(sK0,k2_relat_1(sK1)) & k1_xboole_0 != sK0 & v1_relat_1(sK1)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ? [X0,X1] : (k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1)) => (k1_xboole_0 = k10_relat_1(sK1,sK0) & r1_tarski(sK0,k2_relat_1(sK1)) & k1_xboole_0 != sK0 & v1_relat_1(sK1))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ? [X0,X1] : (k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1))),
% 0.22/0.52    inference(flattening,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0) & v1_relat_1(X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.22/0.52    inference(negated_conjecture,[],[f16])).
% 0.22/0.52  fof(f16,conjecture,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).
% 0.22/0.52  fof(f525,plain,(
% 0.22/0.52    k1_xboole_0 = k3_xboole_0(sK0,k2_relat_1(sK1)) | r2_hidden(sK2(sK0,k2_relat_1(sK1),k1_xboole_0),k1_xboole_0) | spl3_12),
% 0.22/0.52    inference(resolution,[],[f295,f42])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f30])).
% 0.22/0.52  fof(f523,plain,(
% 0.22/0.52    ~spl3_15 | ~spl3_12 | spl3_4 | ~spl3_13),
% 0.22/0.52    inference(avatar_split_clause,[],[f463,f298,f86,f294,f434])).
% 0.22/0.52  fof(f298,plain,(
% 0.22/0.52    spl3_13 <=> r2_hidden(sK2(sK0,k2_relat_1(sK1),k1_xboole_0),k2_relat_1(sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.52  fof(f463,plain,(
% 0.22/0.52    k1_xboole_0 = sK0 | ~r2_hidden(sK2(sK0,k2_relat_1(sK1),k1_xboole_0),sK0) | ~r2_hidden(sK2(sK0,k2_relat_1(sK1),k1_xboole_0),k1_xboole_0) | ~spl3_13),
% 0.22/0.52    inference(resolution,[],[f300,f71])).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    ( ! [X2] : (~r2_hidden(sK2(sK0,k2_relat_1(sK1),X2),k2_relat_1(sK1)) | sK0 = X2 | ~r2_hidden(sK2(sK0,k2_relat_1(sK1),X2),sK0) | ~r2_hidden(sK2(sK0,k2_relat_1(sK1),X2),X2)) )),
% 0.22/0.52    inference(superposition,[],[f51,f44])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f30])).
% 0.22/0.52  fof(f300,plain,(
% 0.22/0.52    r2_hidden(sK2(sK0,k2_relat_1(sK1),k1_xboole_0),k2_relat_1(sK1)) | ~spl3_13),
% 0.22/0.52    inference(avatar_component_clause,[],[f298])).
% 0.22/0.52  fof(f517,plain,(
% 0.22/0.52    ~spl3_13 | spl3_15 | ~spl3_2 | ~spl3_12),
% 0.22/0.52    inference(avatar_split_clause,[],[f512,f294,f59,f434,f298])).
% 0.22/0.52  fof(f512,plain,(
% 0.22/0.52    r2_hidden(sK2(sK0,k2_relat_1(sK1),k1_xboole_0),k1_xboole_0) | ~r2_hidden(sK2(sK0,k2_relat_1(sK1),k1_xboole_0),k2_relat_1(sK1)) | (~spl3_2 | ~spl3_12)),
% 0.22/0.52    inference(resolution,[],[f107,f296])).
% 0.22/0.52  fof(f296,plain,(
% 0.22/0.52    r2_hidden(sK2(sK0,k2_relat_1(sK1),k1_xboole_0),sK0) | ~spl3_12),
% 0.22/0.52    inference(avatar_component_clause,[],[f294])).
% 0.22/0.52  fof(f107,plain,(
% 0.22/0.52    ( ! [X3] : (~r2_hidden(X3,sK0) | r2_hidden(X3,k1_xboole_0) | ~r2_hidden(X3,k2_relat_1(sK1))) ) | ~spl3_2),
% 0.22/0.52    inference(superposition,[],[f46,f68])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 0.22/0.52    inference(equality_resolution,[],[f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 0.22/0.52    inference(cnf_transformation,[],[f30])).
% 0.22/0.52  fof(f415,plain,(
% 0.22/0.52    spl3_4 | spl3_13 | ~spl3_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f414,f59,f298,f86])).
% 0.22/0.52  fof(f414,plain,(
% 0.22/0.52    r2_hidden(sK2(sK0,k2_relat_1(sK1),k1_xboole_0),k2_relat_1(sK1)) | k1_xboole_0 = sK0 | ~spl3_2),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f410])).
% 0.22/0.52  fof(f410,plain,(
% 0.22/0.52    r2_hidden(sK2(sK0,k2_relat_1(sK1),k1_xboole_0),k2_relat_1(sK1)) | k1_xboole_0 = sK0 | r2_hidden(sK2(sK0,k2_relat_1(sK1),k1_xboole_0),k2_relat_1(sK1)) | ~spl3_2),
% 0.22/0.52    inference(resolution,[],[f70,f109])).
% 0.22/0.52  fof(f109,plain,(
% 0.22/0.52    ( ! [X5] : (~r2_hidden(X5,k1_xboole_0) | r2_hidden(X5,k2_relat_1(sK1))) ) | ~spl3_2),
% 0.22/0.52    inference(superposition,[],[f48,f68])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 0.22/0.52    inference(equality_resolution,[],[f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.22/0.52    inference(cnf_transformation,[],[f30])).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    ( ! [X1] : (r2_hidden(sK2(sK0,k2_relat_1(sK1),X1),k2_relat_1(sK1)) | r2_hidden(sK2(sK0,k2_relat_1(sK1),X1),X1) | sK0 = X1) )),
% 0.22/0.52    inference(superposition,[],[f51,f43])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f30])).
% 0.22/0.52  fof(f318,plain,(
% 0.22/0.52    ~spl3_4),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f314])).
% 0.22/0.52  fof(f314,plain,(
% 0.22/0.52    $false | ~spl3_4),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f32,f88])).
% 0.22/0.52  fof(f88,plain,(
% 0.22/0.52    k1_xboole_0 = sK0 | ~spl3_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f86])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    k1_xboole_0 != sK0),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    spl3_1),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f63])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    $false | spl3_1),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f31,f57])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    ~v1_relat_1(sK1) | spl3_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f55])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    spl3_1 <=> v1_relat_1(sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    v1_relat_1(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    ~spl3_1 | spl3_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f53,f59,f55])).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    r1_xboole_0(k2_relat_1(sK1),sK0) | ~v1_relat_1(sK1)),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f52])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k2_relat_1(sK1),sK0) | ~v1_relat_1(sK1)),
% 0.22/0.52    inference(superposition,[],[f35,f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0,X1] : (((k1_xboole_0 = k10_relat_1(X1,X0) | ~r1_xboole_0(k2_relat_1(X1),X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(nnf_transformation,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,axiom,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (26924)------------------------------
% 0.22/0.52  % (26924)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (26924)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (26924)Memory used [KB]: 6268
% 0.22/0.52  % (26924)Time elapsed: 0.087 s
% 0.22/0.52  % (26924)------------------------------
% 0.22/0.52  % (26924)------------------------------
% 0.22/0.53  % (26912)Success in time 0.16 s
%------------------------------------------------------------------------------
