%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0002+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:09 EST 2020

% Result     : Theorem 3.86s
% Output     : Refutation 3.86s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 202 expanded)
%              Number of leaves         :    9 (  61 expanded)
%              Depth                    :   13
%              Number of atoms          :  246 ( 562 expanded)
%              Number of equality atoms :   22 (  91 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4241,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1519,f3860,f3925,f3943,f3944,f4063,f4223,f4227,f4234,f4238])).

fof(f4238,plain,
    ( ~ spl5_10
    | ~ spl5_11 ),
    inference(avatar_contradiction_clause,[],[f4237])).

fof(f4237,plain,
    ( $false
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f4042,f3855])).

fof(f3855,plain,
    ( r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK2)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f3853])).

fof(f3853,plain,
    ( spl5_11
  <=> r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f4042,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK2)
    | ~ spl5_10 ),
    inference(resolution,[],[f1517,f30])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f1517,plain,
    ( r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),k4_xboole_0(sK1,sK2))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f1516])).

fof(f1516,plain,
    ( spl5_10
  <=> r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f4234,plain,
    ( spl5_9
    | spl5_10
    | ~ spl5_12 ),
    inference(avatar_contradiction_clause,[],[f4233])).

fof(f4233,plain,
    ( $false
    | spl5_9
    | spl5_10
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f3904,f3858])).

fof(f3858,plain,
    ( r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK1)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f3857])).

fof(f3857,plain,
    ( spl5_12
  <=> r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f3904,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK1)
    | spl5_9
    | spl5_10 ),
    inference(resolution,[],[f3748,f30])).

fof(f3748,plain,
    ( r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),k4_xboole_0(sK2,sK1))
    | spl5_9
    | spl5_10 ),
    inference(subsumption_resolution,[],[f3747,f1514])).

fof(f1514,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK0)
    | spl5_9 ),
    inference(avatar_component_clause,[],[f1512])).

fof(f1512,plain,
    ( spl5_9
  <=> r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f3747,plain,
    ( r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),k4_xboole_0(sK2,sK1))
    | r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK0)
    | spl5_10 ),
    inference(subsumption_resolution,[],[f3746,f1518])).

fof(f1518,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),k4_xboole_0(sK1,sK2))
    | spl5_10 ),
    inference(avatar_component_clause,[],[f1516])).

fof(f3746,plain,
    ( r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),k4_xboole_0(sK1,sK2))
    | r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),k4_xboole_0(sK2,sK1))
    | r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK0) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X2] :
      ( sK0 != X2
      | r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),X2),k4_xboole_0(sK1,sK2))
      | r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),X2),k4_xboole_0(sK2,sK1))
      | r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),X2),X2) ) ),
    inference(superposition,[],[f25,f15])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f25,plain,(
    sK0 != k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)) ),
    inference(definition_unfolding,[],[f11,f12])).

fof(f12,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f11,plain,(
    sK0 != k5_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( k5_xboole_0(X1,X2) != X0
      & ! [X3] :
          ( ~ r2_hidden(X3,X0)
        <=> ( r2_hidden(X3,X1)
          <=> r2_hidden(X3,X2) ) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ! [X3] :
            ( ~ r2_hidden(X3,X0)
          <=> ( r2_hidden(X3,X1)
            <=> r2_hidden(X3,X2) ) )
       => k5_xboole_0(X1,X2) = X0 ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r2_hidden(X3,X0)
        <=> ( r2_hidden(X3,X1)
          <=> r2_hidden(X3,X2) ) )
     => k5_xboole_0(X1,X2) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_0)).

fof(f4227,plain,
    ( ~ spl5_9
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(avatar_contradiction_clause,[],[f4226])).

fof(f4226,plain,
    ( $false
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f3858,f4225])).

fof(f4225,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK1)
    | ~ spl5_9
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f4224,f4121])).

fof(f4121,plain,
    ( ! [X0] : ~ r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),k4_xboole_0(X0,sK2))
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f3855,f30])).

fof(f4224,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK1)
    | r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),k4_xboole_0(sK2,sK2))
    | ~ spl5_9
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f4131,f1513])).

fof(f1513,plain,
    ( r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK0)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f1512])).

fof(f4131,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK0)
    | ~ r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK1)
    | r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),k4_xboole_0(sK2,sK2))
    | ~ spl5_11 ),
    inference(resolution,[],[f3855,f66])).

fof(f66,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X2,sK0)
      | ~ r2_hidden(X2,sK1)
      | r2_hidden(X2,k4_xboole_0(X3,sK2)) ) ),
    inference(resolution,[],[f10,f29])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f10,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK2)
      | ~ r2_hidden(X3,sK1)
      | ~ r2_hidden(X3,sK0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f4223,plain,
    ( ~ spl5_11
    | spl5_12
    | spl5_13 ),
    inference(avatar_contradiction_clause,[],[f4222])).

fof(f4222,plain,
    ( $false
    | ~ spl5_11
    | spl5_12
    | spl5_13 ),
    inference(subsumption_resolution,[],[f4210,f3935])).

fof(f3935,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),k4_xboole_0(sK2,sK1))
    | spl5_13 ),
    inference(avatar_component_clause,[],[f3934])).

fof(f3934,plain,
    ( spl5_13
  <=> r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),k4_xboole_0(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f4210,plain,
    ( r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),k4_xboole_0(sK2,sK1))
    | ~ spl5_11
    | spl5_12 ),
    inference(unit_resulting_resolution,[],[f3855,f3859,f29])).

fof(f3859,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK1)
    | spl5_12 ),
    inference(avatar_component_clause,[],[f3857])).

fof(f4063,plain,
    ( spl5_9
    | ~ spl5_10
    | spl5_11 ),
    inference(avatar_contradiction_clause,[],[f4062])).

fof(f4062,plain,
    ( $false
    | spl5_9
    | ~ spl5_10
    | spl5_11 ),
    inference(subsumption_resolution,[],[f4061,f3854])).

fof(f3854,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK2)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f3853])).

fof(f4061,plain,
    ( r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK2)
    | spl5_9
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f4040,f1514])).

fof(f4040,plain,
    ( r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK0)
    | r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK2)
    | ~ spl5_10 ),
    inference(resolution,[],[f1517,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(sK1,X1))
      | r2_hidden(X0,sK0)
      | r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f8,f31])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f8,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK1)
      | r2_hidden(X3,sK2)
      | r2_hidden(X3,sK0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f3944,plain,
    ( ~ spl5_9
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f1526,f3934,f1512])).

fof(f1526,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),k4_xboole_0(sK2,sK1))
    | ~ r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK0) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X1] :
      ( sK0 != X1
      | ~ r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),X1),k4_xboole_0(sK2,sK1))
      | ~ r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),X1),X1) ) ),
    inference(superposition,[],[f25,f14])).

fof(f14,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f3943,plain,
    ( ~ spl5_9
    | spl5_10
    | spl5_11
    | spl5_12 ),
    inference(avatar_contradiction_clause,[],[f3942])).

fof(f3942,plain,
    ( $false
    | ~ spl5_9
    | spl5_10
    | spl5_11
    | spl5_12 ),
    inference(subsumption_resolution,[],[f1513,f3941])).

fof(f3941,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK0)
    | spl5_10
    | spl5_11
    | spl5_12 ),
    inference(subsumption_resolution,[],[f1526,f3940])).

fof(f3940,plain,
    ( r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),k4_xboole_0(sK2,sK1))
    | spl5_10
    | spl5_11
    | spl5_12 ),
    inference(subsumption_resolution,[],[f3939,f25])).

fof(f3939,plain,
    ( r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),k4_xboole_0(sK2,sK1))
    | sK0 = k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))
    | spl5_10
    | spl5_11
    | spl5_12 ),
    inference(subsumption_resolution,[],[f3938,f3859])).

fof(f3938,plain,
    ( r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),k4_xboole_0(sK2,sK1))
    | r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK1)
    | sK0 = k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))
    | spl5_10
    | spl5_11 ),
    inference(subsumption_resolution,[],[f3839,f3854])).

fof(f3839,plain,
    ( r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK2)
    | r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),k4_xboole_0(sK2,sK1))
    | r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK1)
    | sK0 = k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))
    | spl5_10 ),
    inference(resolution,[],[f1518,f60])).

fof(f60,plain,(
    ! [X12,X13] :
      ( r2_hidden(sK3(X12,X13,sK0),sK2)
      | r2_hidden(sK3(X12,X13,sK0),X12)
      | r2_hidden(sK3(X12,X13,sK0),X13)
      | r2_hidden(sK3(X12,X13,sK0),sK1)
      | sK0 = k2_xboole_0(X12,X13) ) ),
    inference(resolution,[],[f9,f15])).

fof(f9,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK0)
      | r2_hidden(X3,sK1)
      | r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f3925,plain,
    ( spl5_9
    | spl5_10
    | spl5_12 ),
    inference(avatar_contradiction_clause,[],[f3924])).

fof(f3924,plain,
    ( $false
    | spl5_9
    | spl5_10
    | spl5_12 ),
    inference(subsumption_resolution,[],[f3923,f3859])).

fof(f3923,plain,
    ( r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK1)
    | spl5_9
    | spl5_10 ),
    inference(subsumption_resolution,[],[f3902,f1514])).

fof(f3902,plain,
    ( r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK0)
    | r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK1)
    | spl5_9
    | spl5_10 ),
    inference(resolution,[],[f3748,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(sK2,X1))
      | r2_hidden(X0,sK0)
      | r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f7,f31])).

fof(f7,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK2)
      | r2_hidden(X3,sK1)
      | r2_hidden(X3,sK0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f3860,plain,
    ( spl5_11
    | ~ spl5_12
    | spl5_10 ),
    inference(avatar_split_clause,[],[f3841,f1516,f3857,f3853])).

fof(f3841,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK1)
    | r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK2)
    | spl5_10 ),
    inference(resolution,[],[f1518,f29])).

fof(f1519,plain,
    ( ~ spl5_9
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f1510,f1516,f1512])).

fof(f1510,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),k4_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK0) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X0] :
      ( sK0 != X0
      | ~ r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),X0),k4_xboole_0(sK1,sK2))
      | ~ r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),X0),X0) ) ),
    inference(superposition,[],[f25,f13])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

%------------------------------------------------------------------------------
