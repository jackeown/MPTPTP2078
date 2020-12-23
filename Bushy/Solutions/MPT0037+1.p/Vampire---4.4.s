%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : xboole_1__t30_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:25 EDT 2019

% Result     : Theorem 11.36s
% Output     : Refutation 11.36s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 172 expanded)
%              Number of leaves         :   15 (  54 expanded)
%              Depth                    :    9
%              Number of atoms          :  218 ( 400 expanded)
%              Number of equality atoms :   21 (  64 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8014,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f263,f466,f740,f3507,f5805,f5864,f5900,f5902,f5904,f7978,f8010])).

fof(f8010,plain,
    ( ~ spl6_6
    | spl6_13 ),
    inference(avatar_contradiction_clause,[],[f8009])).

fof(f8009,plain,
    ( $false
    | ~ spl6_6
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f6026,f465])).

fof(f465,plain,
    ( ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))),sK1)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f464])).

fof(f464,plain,
    ( spl6_13
  <=> ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f6026,plain,
    ( r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))),sK1)
    | ~ spl6_6 ),
    inference(resolution,[],[f256,f53])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t30_xboole_1.p',d4_xboole_0)).

fof(f256,plain,
    ( r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))),k3_xboole_0(sK1,sK2))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f255])).

fof(f255,plain,
    ( spl6_6
  <=> r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))),k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f7978,plain,
    ( spl6_5
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(avatar_contradiction_clause,[],[f7977])).

fof(f7977,plain,
    ( $false
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f7943,f456])).

fof(f456,plain,
    ( r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))),sK2)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f455])).

fof(f455,plain,
    ( spl6_10
  <=> r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f7943,plain,
    ( ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))),sK2)
    | ~ spl6_5
    | ~ spl6_12 ),
    inference(resolution,[],[f6091,f54])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t30_xboole_1.p',d3_xboole_0)).

fof(f6091,plain,
    ( ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))),k2_xboole_0(sK0,sK2))
    | ~ spl6_5
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f6073,f462])).

fof(f462,plain,
    ( r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))),sK1)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f461])).

fof(f461,plain,
    ( spl6_12
  <=> r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f6073,plain,
    ( ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))),sK1)
    | ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))),k2_xboole_0(sK0,sK2))
    | ~ spl6_5 ),
    inference(resolution,[],[f247,f51])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f247,plain,
    ( ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f246])).

fof(f246,plain,
    ( spl6_5
  <=> ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f5904,plain,
    ( ~ spl6_6
    | spl6_11 ),
    inference(avatar_contradiction_clause,[],[f5903])).

fof(f5903,plain,
    ( $false
    | ~ spl6_6
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f256,f5466])).

fof(f5466,plain,
    ( ! [X4] : ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))),k3_xboole_0(X4,sK2))
    | ~ spl6_11 ),
    inference(resolution,[],[f459,f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f459,plain,
    ( ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))),sK2)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f458])).

fof(f458,plain,
    ( spl6_11
  <=> ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f5902,plain,
    ( ~ spl6_4
    | ~ spl6_8 ),
    inference(avatar_contradiction_clause,[],[f5901])).

fof(f5901,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f262,f701])).

fof(f701,plain,
    ( ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))),sK0)
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f60,f250,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f250,plain,
    ( r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f249])).

fof(f249,plain,
    ( spl6_4
  <=> r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f60,plain,(
    k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)) != k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f59,f34])).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t30_xboole_1.p',commutativity_k3_xboole_0)).

fof(f59,plain,(
    k3_xboole_0(k2_xboole_0(sK0,sK2),sK1) != k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f27,f34])).

fof(f27,plain,(
    k3_xboole_0(k2_xboole_0(sK0,sK2),sK1) != k2_xboole_0(sK0,k3_xboole_0(sK2,sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(k2_xboole_0(X0,X2),X1) != k2_xboole_0(X0,k3_xboole_0(X2,X1))
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => k3_xboole_0(k2_xboole_0(X0,X2),X1) = k2_xboole_0(X0,k3_xboole_0(X2,X1)) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(k2_xboole_0(X0,X2),X1) = k2_xboole_0(X0,k3_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t30_xboole_1.p',t30_xboole_1)).

fof(f262,plain,
    ( r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))),sK0)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f261])).

fof(f261,plain,
    ( spl6_8
  <=> r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f5900,plain,
    ( ~ spl6_4
    | spl6_9
    | spl6_11 ),
    inference(avatar_contradiction_clause,[],[f5899])).

fof(f5899,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_9
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f5875,f704])).

fof(f704,plain,
    ( r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))),k2_xboole_0(sK0,sK2))
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f250,f52])).

fof(f5875,plain,
    ( ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))),k2_xboole_0(sK0,sK2))
    | ~ spl6_9
    | ~ spl6_11 ),
    inference(unit_resulting_resolution,[],[f459,f259,f56])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f259,plain,
    ( ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))),sK0)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f258])).

fof(f258,plain,
    ( spl6_9
  <=> ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f5864,plain,
    ( spl6_5
    | ~ spl6_8 ),
    inference(avatar_contradiction_clause,[],[f5863])).

fof(f5863,plain,
    ( $false
    | ~ spl6_5
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f5862,f5779])).

fof(f5779,plain,
    ( ! [X6] : r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))),k2_xboole_0(sK0,X6))
    | ~ spl6_8 ),
    inference(resolution,[],[f262,f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f5862,plain,
    ( ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))),k2_xboole_0(sK0,sK2))
    | ~ spl6_5
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f5844,f5772])).

fof(f5772,plain,
    ( r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))),sK1)
    | ~ spl6_8 ),
    inference(resolution,[],[f262,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f26,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t30_xboole_1.p',d3_tarski)).

fof(f26,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f5844,plain,
    ( ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))),sK1)
    | ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))),k2_xboole_0(sK0,sK2))
    | ~ spl6_5 ),
    inference(resolution,[],[f247,f51])).

fof(f5805,plain,
    ( ~ spl6_8
    | spl6_13 ),
    inference(avatar_contradiction_clause,[],[f5804])).

fof(f5804,plain,
    ( $false
    | ~ spl6_8
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f5772,f465])).

fof(f3507,plain,
    ( ~ spl6_4
    | ~ spl6_6 ),
    inference(avatar_contradiction_clause,[],[f3506])).

fof(f3506,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f256,f3505])).

fof(f3505,plain,
    ( ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))),k3_xboole_0(sK1,sK2))
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f716,f60])).

fof(f716,plain,
    ( ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))),k3_xboole_0(sK1,sK2))
    | k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)) = k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl6_4 ),
    inference(resolution,[],[f250,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f740,plain,
    ( ~ spl6_4
    | spl6_13 ),
    inference(avatar_contradiction_clause,[],[f739])).

fof(f739,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f717,f465])).

fof(f717,plain,
    ( r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))),sK1)
    | ~ spl6_4 ),
    inference(resolution,[],[f250,f53])).

fof(f466,plain,
    ( ~ spl6_11
    | ~ spl6_13
    | spl6_7 ),
    inference(avatar_split_clause,[],[f436,f252,f464,f458])).

fof(f252,plain,
    ( spl6_7
  <=> ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))),k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f436,plain,
    ( ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))),sK1)
    | ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))),sK2)
    | ~ spl6_7 ),
    inference(resolution,[],[f253,f51])).

fof(f253,plain,
    ( ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))),k3_xboole_0(sK1,sK2))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f252])).

fof(f263,plain,
    ( spl6_4
    | spl6_6
    | spl6_8 ),
    inference(avatar_split_clause,[],[f244,f261,f255,f249])).

fof(f244,plain,
    ( r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))),sK0)
    | r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))),k3_xboole_0(sK1,sK2))
    | r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2] :
      ( k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)) != X2
      | r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),X2),sK0)
      | r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),X2),k3_xboole_0(sK1,sK2))
      | r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),X2),X2) ) ),
    inference(superposition,[],[f60,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
