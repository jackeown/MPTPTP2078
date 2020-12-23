%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:29 EST 2020

% Result     : Theorem 3.56s
% Output     : Refutation 3.66s
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f25,plain,(
    sK0 != k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)) ),
    inference(definition_unfolding,[],[f11,f12])).

fof(f12,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_0)).

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
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:50:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.52  % (7511)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (7514)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (7509)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (7502)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (7521)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (7508)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (7529)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (7524)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.56  % (7530)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.56  % (7532)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.56  % (7523)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.57  % (7516)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.58  % (7507)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.58  % (7518)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.55/0.59  % (7506)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.55/0.60  % (7504)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.55/0.60  % (7512)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.55/0.60  % (7512)Refutation not found, incomplete strategy% (7512)------------------------------
% 1.55/0.60  % (7512)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.60  % (7512)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.60  
% 1.55/0.60  % (7512)Memory used [KB]: 10618
% 1.55/0.60  % (7512)Time elapsed: 0.174 s
% 1.55/0.60  % (7512)------------------------------
% 1.55/0.60  % (7512)------------------------------
% 1.55/0.60  % (7520)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.94/0.61  % (7513)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.94/0.61  % (7513)Refutation not found, incomplete strategy% (7513)------------------------------
% 1.94/0.61  % (7513)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.94/0.61  % (7513)Termination reason: Refutation not found, incomplete strategy
% 1.94/0.61  
% 1.94/0.61  % (7513)Memory used [KB]: 10618
% 1.94/0.61  % (7513)Time elapsed: 0.195 s
% 1.94/0.61  % (7513)------------------------------
% 1.94/0.61  % (7513)------------------------------
% 1.94/0.62  % (7503)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.94/0.62  % (7528)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.94/0.62  % (7527)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.94/0.62  % (7531)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.94/0.62  % (7501)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.94/0.63  % (7525)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.94/0.63  % (7519)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.94/0.63  % (7522)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.94/0.63  % (7519)Refutation not found, incomplete strategy% (7519)------------------------------
% 1.94/0.63  % (7519)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.94/0.63  % (7519)Termination reason: Refutation not found, incomplete strategy
% 1.94/0.63  
% 1.94/0.63  % (7519)Memory used [KB]: 10618
% 1.94/0.63  % (7519)Time elapsed: 0.209 s
% 1.94/0.63  % (7519)------------------------------
% 1.94/0.63  % (7519)------------------------------
% 1.94/0.64  % (7515)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.94/0.64  % (7517)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.94/0.65  % (7510)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 3.29/0.80  % (7559)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 3.29/0.81  % (7558)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 3.29/0.82  % (7557)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 3.56/0.84  % (7507)Time limit reached!
% 3.56/0.84  % (7507)------------------------------
% 3.56/0.84  % (7507)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.56/0.84  % (7507)Termination reason: Time limit
% 3.56/0.84  % (7507)Termination phase: Saturation
% 3.56/0.84  
% 3.56/0.84  % (7507)Memory used [KB]: 8315
% 3.56/0.84  % (7507)Time elapsed: 0.400 s
% 3.56/0.84  % (7507)------------------------------
% 3.56/0.84  % (7507)------------------------------
% 3.56/0.84  % (7511)Refutation found. Thanks to Tanya!
% 3.56/0.84  % SZS status Theorem for theBenchmark
% 3.66/0.85  % SZS output start Proof for theBenchmark
% 3.66/0.85  fof(f4241,plain,(
% 3.66/0.85    $false),
% 3.66/0.85    inference(avatar_sat_refutation,[],[f1519,f3860,f3925,f3943,f3944,f4063,f4223,f4227,f4234,f4238])).
% 3.66/0.85  fof(f4238,plain,(
% 3.66/0.85    ~spl5_10 | ~spl5_11),
% 3.66/0.85    inference(avatar_contradiction_clause,[],[f4237])).
% 3.66/0.85  fof(f4237,plain,(
% 3.66/0.85    $false | (~spl5_10 | ~spl5_11)),
% 3.66/0.85    inference(subsumption_resolution,[],[f4042,f3855])).
% 3.66/0.85  fof(f3855,plain,(
% 3.66/0.85    r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK2) | ~spl5_11),
% 3.66/0.85    inference(avatar_component_clause,[],[f3853])).
% 3.66/0.85  fof(f3853,plain,(
% 3.66/0.85    spl5_11 <=> r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK2)),
% 3.66/0.85    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 3.66/0.85  fof(f4042,plain,(
% 3.66/0.85    ~r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK2) | ~spl5_10),
% 3.66/0.85    inference(resolution,[],[f1517,f30])).
% 3.66/0.85  fof(f30,plain,(
% 3.66/0.85    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 3.66/0.85    inference(equality_resolution,[],[f23])).
% 3.66/0.85  fof(f23,plain,(
% 3.66/0.85    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.66/0.85    inference(cnf_transformation,[],[f2])).
% 3.66/0.85  fof(f2,axiom,(
% 3.66/0.85    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.66/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 3.66/0.85  fof(f1517,plain,(
% 3.66/0.85    r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),k4_xboole_0(sK1,sK2)) | ~spl5_10),
% 3.66/0.85    inference(avatar_component_clause,[],[f1516])).
% 3.66/0.85  fof(f1516,plain,(
% 3.66/0.85    spl5_10 <=> r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),k4_xboole_0(sK1,sK2))),
% 3.66/0.85    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 3.66/0.85  fof(f4234,plain,(
% 3.66/0.85    spl5_9 | spl5_10 | ~spl5_12),
% 3.66/0.85    inference(avatar_contradiction_clause,[],[f4233])).
% 3.66/0.85  fof(f4233,plain,(
% 3.66/0.85    $false | (spl5_9 | spl5_10 | ~spl5_12)),
% 3.66/0.85    inference(subsumption_resolution,[],[f3904,f3858])).
% 3.66/0.85  fof(f3858,plain,(
% 3.66/0.85    r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK1) | ~spl5_12),
% 3.66/0.85    inference(avatar_component_clause,[],[f3857])).
% 3.66/0.85  fof(f3857,plain,(
% 3.66/0.85    spl5_12 <=> r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK1)),
% 3.66/0.85    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 3.66/0.85  fof(f3904,plain,(
% 3.66/0.85    ~r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK1) | (spl5_9 | spl5_10)),
% 3.66/0.85    inference(resolution,[],[f3748,f30])).
% 3.66/0.85  fof(f3748,plain,(
% 3.66/0.85    r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),k4_xboole_0(sK2,sK1)) | (spl5_9 | spl5_10)),
% 3.66/0.85    inference(subsumption_resolution,[],[f3747,f1514])).
% 3.66/0.85  fof(f1514,plain,(
% 3.66/0.85    ~r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK0) | spl5_9),
% 3.66/0.85    inference(avatar_component_clause,[],[f1512])).
% 3.66/0.85  fof(f1512,plain,(
% 3.66/0.85    spl5_9 <=> r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK0)),
% 3.66/0.85    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 3.66/0.85  fof(f3747,plain,(
% 3.66/0.85    r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),k4_xboole_0(sK2,sK1)) | r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK0) | spl5_10),
% 3.66/0.85    inference(subsumption_resolution,[],[f3746,f1518])).
% 3.66/0.85  fof(f1518,plain,(
% 3.66/0.85    ~r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),k4_xboole_0(sK1,sK2)) | spl5_10),
% 3.66/0.85    inference(avatar_component_clause,[],[f1516])).
% 3.66/0.85  fof(f3746,plain,(
% 3.66/0.85    r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),k4_xboole_0(sK1,sK2)) | r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),k4_xboole_0(sK2,sK1)) | r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK0)),
% 3.66/0.85    inference(equality_resolution,[],[f84])).
% 3.66/0.85  fof(f84,plain,(
% 3.66/0.85    ( ! [X2] : (sK0 != X2 | r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),X2),k4_xboole_0(sK1,sK2)) | r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),X2),k4_xboole_0(sK2,sK1)) | r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),X2),X2)) )),
% 3.66/0.85    inference(superposition,[],[f25,f15])).
% 3.66/0.85  fof(f15,plain,(
% 3.66/0.85    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2) | k2_xboole_0(X0,X1) = X2) )),
% 3.66/0.85    inference(cnf_transformation,[],[f1])).
% 3.66/0.85  fof(f1,axiom,(
% 3.66/0.85    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 3.66/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 3.66/0.85  fof(f25,plain,(
% 3.66/0.85    sK0 != k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))),
% 3.66/0.85    inference(definition_unfolding,[],[f11,f12])).
% 3.66/0.85  fof(f12,plain,(
% 3.66/0.85    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 3.66/0.85    inference(cnf_transformation,[],[f3])).
% 3.66/0.85  fof(f3,axiom,(
% 3.66/0.85    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 3.66/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 3.66/0.85  fof(f11,plain,(
% 3.66/0.85    sK0 != k5_xboole_0(sK1,sK2)),
% 3.66/0.85    inference(cnf_transformation,[],[f6])).
% 3.66/0.85  fof(f6,plain,(
% 3.66/0.85    ? [X0,X1,X2] : (k5_xboole_0(X1,X2) != X0 & ! [X3] : (~r2_hidden(X3,X0) <=> (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))))),
% 3.66/0.85    inference(ennf_transformation,[],[f5])).
% 3.66/0.85  fof(f5,negated_conjecture,(
% 3.66/0.85    ~! [X0,X1,X2] : (! [X3] : (~r2_hidden(X3,X0) <=> (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => k5_xboole_0(X1,X2) = X0)),
% 3.66/0.85    inference(negated_conjecture,[],[f4])).
% 3.66/0.85  fof(f4,conjecture,(
% 3.66/0.85    ! [X0,X1,X2] : (! [X3] : (~r2_hidden(X3,X0) <=> (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => k5_xboole_0(X1,X2) = X0)),
% 3.66/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_0)).
% 3.66/0.85  fof(f4227,plain,(
% 3.66/0.85    ~spl5_9 | ~spl5_11 | ~spl5_12),
% 3.66/0.85    inference(avatar_contradiction_clause,[],[f4226])).
% 3.66/0.85  fof(f4226,plain,(
% 3.66/0.85    $false | (~spl5_9 | ~spl5_11 | ~spl5_12)),
% 3.66/0.85    inference(subsumption_resolution,[],[f3858,f4225])).
% 3.66/0.85  fof(f4225,plain,(
% 3.66/0.85    ~r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK1) | (~spl5_9 | ~spl5_11)),
% 3.66/0.85    inference(subsumption_resolution,[],[f4224,f4121])).
% 3.66/0.85  fof(f4121,plain,(
% 3.66/0.85    ( ! [X0] : (~r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),k4_xboole_0(X0,sK2))) ) | ~spl5_11),
% 3.66/0.85    inference(unit_resulting_resolution,[],[f3855,f30])).
% 3.66/0.85  fof(f4224,plain,(
% 3.66/0.85    ~r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK1) | r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),k4_xboole_0(sK2,sK2)) | (~spl5_9 | ~spl5_11)),
% 3.66/0.85    inference(subsumption_resolution,[],[f4131,f1513])).
% 3.66/0.85  fof(f1513,plain,(
% 3.66/0.85    r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK0) | ~spl5_9),
% 3.66/0.85    inference(avatar_component_clause,[],[f1512])).
% 3.66/0.85  fof(f4131,plain,(
% 3.66/0.85    ~r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK0) | ~r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK1) | r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),k4_xboole_0(sK2,sK2)) | ~spl5_11),
% 3.66/0.85    inference(resolution,[],[f3855,f66])).
% 3.66/0.85  fof(f66,plain,(
% 3.66/0.85    ( ! [X2,X3] : (~r2_hidden(X2,X3) | ~r2_hidden(X2,sK0) | ~r2_hidden(X2,sK1) | r2_hidden(X2,k4_xboole_0(X3,sK2))) )),
% 3.66/0.85    inference(resolution,[],[f10,f29])).
% 3.66/0.85  fof(f29,plain,(
% 3.66/0.85    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 3.66/0.85    inference(equality_resolution,[],[f24])).
% 3.66/0.85  fof(f24,plain,(
% 3.66/0.85    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.66/0.85    inference(cnf_transformation,[],[f2])).
% 3.66/0.85  fof(f10,plain,(
% 3.66/0.85    ( ! [X3] : (~r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1) | ~r2_hidden(X3,sK0)) )),
% 3.66/0.85    inference(cnf_transformation,[],[f6])).
% 3.66/0.85  fof(f4223,plain,(
% 3.66/0.85    ~spl5_11 | spl5_12 | spl5_13),
% 3.66/0.85    inference(avatar_contradiction_clause,[],[f4222])).
% 3.66/0.85  fof(f4222,plain,(
% 3.66/0.85    $false | (~spl5_11 | spl5_12 | spl5_13)),
% 3.66/0.85    inference(subsumption_resolution,[],[f4210,f3935])).
% 3.66/0.85  fof(f3935,plain,(
% 3.66/0.85    ~r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),k4_xboole_0(sK2,sK1)) | spl5_13),
% 3.66/0.85    inference(avatar_component_clause,[],[f3934])).
% 3.66/0.85  fof(f3934,plain,(
% 3.66/0.85    spl5_13 <=> r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),k4_xboole_0(sK2,sK1))),
% 3.66/0.85    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 3.66/0.85  fof(f4210,plain,(
% 3.66/0.85    r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),k4_xboole_0(sK2,sK1)) | (~spl5_11 | spl5_12)),
% 3.66/0.85    inference(unit_resulting_resolution,[],[f3855,f3859,f29])).
% 3.66/0.85  fof(f3859,plain,(
% 3.66/0.85    ~r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK1) | spl5_12),
% 3.66/0.85    inference(avatar_component_clause,[],[f3857])).
% 3.66/0.85  fof(f4063,plain,(
% 3.66/0.85    spl5_9 | ~spl5_10 | spl5_11),
% 3.66/0.85    inference(avatar_contradiction_clause,[],[f4062])).
% 3.66/0.85  fof(f4062,plain,(
% 3.66/0.85    $false | (spl5_9 | ~spl5_10 | spl5_11)),
% 3.66/0.85    inference(subsumption_resolution,[],[f4061,f3854])).
% 3.66/0.85  fof(f3854,plain,(
% 3.66/0.85    ~r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK2) | spl5_11),
% 3.66/0.85    inference(avatar_component_clause,[],[f3853])).
% 3.66/0.85  fof(f4061,plain,(
% 3.66/0.85    r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK2) | (spl5_9 | ~spl5_10)),
% 3.66/0.85    inference(subsumption_resolution,[],[f4040,f1514])).
% 3.66/0.85  fof(f4040,plain,(
% 3.66/0.85    r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK0) | r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK2) | ~spl5_10),
% 3.66/0.85    inference(resolution,[],[f1517,f43])).
% 3.66/0.85  fof(f43,plain,(
% 3.66/0.85    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(sK1,X1)) | r2_hidden(X0,sK0) | r2_hidden(X0,sK2)) )),
% 3.66/0.85    inference(resolution,[],[f8,f31])).
% 3.66/0.85  fof(f31,plain,(
% 3.66/0.85    ( ! [X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 3.66/0.85    inference(equality_resolution,[],[f22])).
% 3.66/0.85  fof(f22,plain,(
% 3.66/0.85    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.66/0.85    inference(cnf_transformation,[],[f2])).
% 3.66/0.85  fof(f8,plain,(
% 3.66/0.85    ( ! [X3] : (~r2_hidden(X3,sK1) | r2_hidden(X3,sK2) | r2_hidden(X3,sK0)) )),
% 3.66/0.85    inference(cnf_transformation,[],[f6])).
% 3.66/0.85  fof(f3944,plain,(
% 3.66/0.85    ~spl5_9 | ~spl5_13),
% 3.66/0.85    inference(avatar_split_clause,[],[f1526,f3934,f1512])).
% 3.66/0.85  fof(f1526,plain,(
% 3.66/0.85    ~r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),k4_xboole_0(sK2,sK1)) | ~r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK0)),
% 3.66/0.85    inference(equality_resolution,[],[f83])).
% 3.66/0.85  fof(f83,plain,(
% 3.66/0.85    ( ! [X1] : (sK0 != X1 | ~r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),X1),k4_xboole_0(sK2,sK1)) | ~r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),X1),X1)) )),
% 3.66/0.85    inference(superposition,[],[f25,f14])).
% 3.66/0.85  fof(f14,plain,(
% 3.66/0.85    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X2) | k2_xboole_0(X0,X1) = X2) )),
% 3.66/0.85    inference(cnf_transformation,[],[f1])).
% 3.66/0.85  fof(f3943,plain,(
% 3.66/0.85    ~spl5_9 | spl5_10 | spl5_11 | spl5_12),
% 3.66/0.85    inference(avatar_contradiction_clause,[],[f3942])).
% 3.66/0.85  fof(f3942,plain,(
% 3.66/0.85    $false | (~spl5_9 | spl5_10 | spl5_11 | spl5_12)),
% 3.66/0.85    inference(subsumption_resolution,[],[f1513,f3941])).
% 3.66/0.85  fof(f3941,plain,(
% 3.66/0.85    ~r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK0) | (spl5_10 | spl5_11 | spl5_12)),
% 3.66/0.85    inference(subsumption_resolution,[],[f1526,f3940])).
% 3.66/0.85  fof(f3940,plain,(
% 3.66/0.85    r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),k4_xboole_0(sK2,sK1)) | (spl5_10 | spl5_11 | spl5_12)),
% 3.66/0.85    inference(subsumption_resolution,[],[f3939,f25])).
% 3.66/0.85  fof(f3939,plain,(
% 3.66/0.85    r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),k4_xboole_0(sK2,sK1)) | sK0 = k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)) | (spl5_10 | spl5_11 | spl5_12)),
% 3.66/0.85    inference(subsumption_resolution,[],[f3938,f3859])).
% 3.66/0.85  fof(f3938,plain,(
% 3.66/0.85    r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),k4_xboole_0(sK2,sK1)) | r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK1) | sK0 = k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)) | (spl5_10 | spl5_11)),
% 3.66/0.85    inference(subsumption_resolution,[],[f3839,f3854])).
% 3.66/0.85  fof(f3839,plain,(
% 3.66/0.85    r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK2) | r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),k4_xboole_0(sK2,sK1)) | r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK1) | sK0 = k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)) | spl5_10),
% 3.66/0.85    inference(resolution,[],[f1518,f60])).
% 3.66/0.85  fof(f60,plain,(
% 3.66/0.85    ( ! [X12,X13] : (r2_hidden(sK3(X12,X13,sK0),sK2) | r2_hidden(sK3(X12,X13,sK0),X12) | r2_hidden(sK3(X12,X13,sK0),X13) | r2_hidden(sK3(X12,X13,sK0),sK1) | sK0 = k2_xboole_0(X12,X13)) )),
% 3.66/0.85    inference(resolution,[],[f9,f15])).
% 3.66/0.85  fof(f9,plain,(
% 3.66/0.85    ( ! [X3] : (~r2_hidden(X3,sK0) | r2_hidden(X3,sK1) | r2_hidden(X3,sK2)) )),
% 3.66/0.85    inference(cnf_transformation,[],[f6])).
% 3.66/0.85  fof(f3925,plain,(
% 3.66/0.85    spl5_9 | spl5_10 | spl5_12),
% 3.66/0.85    inference(avatar_contradiction_clause,[],[f3924])).
% 3.66/0.85  fof(f3924,plain,(
% 3.66/0.85    $false | (spl5_9 | spl5_10 | spl5_12)),
% 3.66/0.85    inference(subsumption_resolution,[],[f3923,f3859])).
% 3.66/0.85  fof(f3923,plain,(
% 3.66/0.85    r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK1) | (spl5_9 | spl5_10)),
% 3.66/0.85    inference(subsumption_resolution,[],[f3902,f1514])).
% 3.66/0.85  fof(f3902,plain,(
% 3.66/0.85    r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK0) | r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK1) | (spl5_9 | spl5_10)),
% 3.66/0.85    inference(resolution,[],[f3748,f32])).
% 3.66/0.85  fof(f32,plain,(
% 3.66/0.85    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(sK2,X1)) | r2_hidden(X0,sK0) | r2_hidden(X0,sK1)) )),
% 3.66/0.85    inference(resolution,[],[f7,f31])).
% 3.66/0.85  fof(f7,plain,(
% 3.66/0.85    ( ! [X3] : (~r2_hidden(X3,sK2) | r2_hidden(X3,sK1) | r2_hidden(X3,sK0)) )),
% 3.66/0.85    inference(cnf_transformation,[],[f6])).
% 3.66/0.85  fof(f3860,plain,(
% 3.66/0.85    spl5_11 | ~spl5_12 | spl5_10),
% 3.66/0.85    inference(avatar_split_clause,[],[f3841,f1516,f3857,f3853])).
% 3.66/0.85  fof(f3841,plain,(
% 3.66/0.85    ~r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK1) | r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK2) | spl5_10),
% 3.66/0.85    inference(resolution,[],[f1518,f29])).
% 3.66/0.85  fof(f1519,plain,(
% 3.66/0.85    ~spl5_9 | ~spl5_10),
% 3.66/0.85    inference(avatar_split_clause,[],[f1510,f1516,f1512])).
% 3.66/0.85  fof(f1510,plain,(
% 3.66/0.85    ~r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),k4_xboole_0(sK1,sK2)) | ~r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),sK0),sK0)),
% 3.66/0.85    inference(equality_resolution,[],[f82])).
% 3.66/0.85  fof(f82,plain,(
% 3.66/0.85    ( ! [X0] : (sK0 != X0 | ~r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),X0),k4_xboole_0(sK1,sK2)) | ~r2_hidden(sK3(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1),X0),X0)) )),
% 3.66/0.85    inference(superposition,[],[f25,f13])).
% 3.66/0.85  fof(f13,plain,(
% 3.66/0.85    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2) | k2_xboole_0(X0,X1) = X2) )),
% 3.66/0.85    inference(cnf_transformation,[],[f1])).
% 3.66/0.85  % SZS output end Proof for theBenchmark
% 3.66/0.85  % (7511)------------------------------
% 3.66/0.85  % (7511)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.66/0.85  % (7511)Termination reason: Refutation
% 3.66/0.85  
% 3.66/0.85  % (7511)Memory used [KB]: 14583
% 3.66/0.85  % (7511)Time elapsed: 0.402 s
% 3.66/0.85  % (7511)------------------------------
% 3.66/0.85  % (7511)------------------------------
% 3.66/0.86  % (7500)Success in time 0.496 s
%------------------------------------------------------------------------------
