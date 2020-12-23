%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : xboole_1__t24_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:23 EDT 2019

% Result     : Theorem 6.65s
% Output     : Refutation 6.65s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 136 expanded)
%              Number of leaves         :    8 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :  140 ( 346 expanded)
%              Number of equality atoms :   21 (  63 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11634,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f9254,f9944,f11532,f11630])).

fof(f11630,plain,
    ( ~ spl5_28
    | ~ spl5_30 ),
    inference(avatar_contradiction_clause,[],[f11609])).

fof(f11609,plain,
    ( $false
    | ~ spl5_28
    | ~ spl5_30 ),
    inference(unit_resulting_resolution,[],[f11387,f8921,f11418,f56])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t24_xboole_1.p',d3_xboole_0)).

fof(f11418,plain,
    ( ! [X0] : ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2),k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(X0,sK2))
    | ~ spl5_28
    | ~ spl5_30 ),
    inference(unit_resulting_resolution,[],[f11370,f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
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
    file('/export/starexec/sandbox2/benchmark/xboole_1__t24_xboole_1.p',d4_xboole_0)).

fof(f11370,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2),k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK2)
    | ~ spl5_28
    | ~ spl5_30 ),
    inference(unit_resulting_resolution,[],[f11296,f54])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f11296,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2),k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k2_xboole_0(sK0,sK2))
    | ~ spl5_28
    | ~ spl5_30 ),
    inference(unit_resulting_resolution,[],[f8921,f8918,f51])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f8918,plain,
    ( ! [X0] : ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2),k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(k2_xboole_0(sK0,sK2),X0))
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f8917])).

fof(f8917,plain,
    ( spl5_28
  <=> ! [X0] : ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2),k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(k2_xboole_0(sK0,sK2),X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f8921,plain,
    ( r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2),k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)))
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f8920])).

fof(f8920,plain,
    ( spl5_30
  <=> r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2),k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f11387,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2),k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK0)
    | ~ spl5_28
    | ~ spl5_30 ),
    inference(resolution,[],[f11296,f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f11532,plain,
    ( ~ spl5_30
    | ~ spl5_32 ),
    inference(avatar_contradiction_clause,[],[f11510])).

fof(f11510,plain,
    ( $false
    | ~ spl5_30
    | ~ spl5_32 ),
    inference(unit_resulting_resolution,[],[f11263,f11285,f53])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f11285,plain,
    ( r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2),k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK1,sK2))
    | ~ spl5_30
    | ~ spl5_32 ),
    inference(unit_resulting_resolution,[],[f8921,f11262,f56])).

fof(f11262,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2),k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK0)
    | ~ spl5_32 ),
    inference(unit_resulting_resolution,[],[f10745,f55])).

fof(f10745,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2),k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k2_xboole_0(sK0,sK1))
    | ~ spl5_32 ),
    inference(superposition,[],[f9253,f36])).

fof(f36,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t24_xboole_1.p',idempotence_k3_xboole_0)).

fof(f9253,plain,
    ( ! [X1] : ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2),k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(X1,k2_xboole_0(sK0,sK1)))
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f9252])).

fof(f9252,plain,
    ( spl5_32
  <=> ! [X1] : ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2),k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(X1,k2_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f11263,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2),k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK1)
    | ~ spl5_32 ),
    inference(unit_resulting_resolution,[],[f10745,f54])).

fof(f9944,plain,(
    spl5_31 ),
    inference(avatar_contradiction_clause,[],[f9930])).

fof(f9930,plain,
    ( $false
    | ~ spl5_31 ),
    inference(unit_resulting_resolution,[],[f9793,f9871,f9067,f51])).

fof(f9067,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2),k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK1,sK2))
    | ~ spl5_31 ),
    inference(unit_resulting_resolution,[],[f8924,f54])).

fof(f8924,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2),k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)))
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f8923])).

fof(f8923,plain,
    ( spl5_31
  <=> ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2),k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f9871,plain,
    ( r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2),k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK2)
    | ~ spl5_31 ),
    inference(unit_resulting_resolution,[],[f9066,f9065,f56])).

fof(f9065,plain,
    ( r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2),k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k2_xboole_0(sK0,sK2))
    | ~ spl5_31 ),
    inference(unit_resulting_resolution,[],[f28,f8924,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f28,plain,(
    k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)) != k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] : k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) != k2_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] : k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] : k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t24_xboole_1.p',t24_xboole_1)).

fof(f9066,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2),k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK0)
    | ~ spl5_31 ),
    inference(unit_resulting_resolution,[],[f8924,f55])).

fof(f9793,plain,
    ( r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2),k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK1)
    | ~ spl5_31 ),
    inference(unit_resulting_resolution,[],[f9066,f9064,f56])).

fof(f9064,plain,
    ( r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2),k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k2_xboole_0(sK0,sK1))
    | ~ spl5_31 ),
    inference(unit_resulting_resolution,[],[f28,f8924,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9254,plain,
    ( spl5_32
    | spl5_28
    | ~ spl5_31 ),
    inference(avatar_split_clause,[],[f201,f8923,f8917,f9252])).

fof(f201,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2),k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)))
      | ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2),k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(k2_xboole_0(sK0,sK2),X0))
      | ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2),k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(X1,k2_xboole_0(sK0,sK1))) ) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X14,X12,X13] :
      ( k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != X12
      | ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2),X12),X12)
      | ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2),X12),k3_xboole_0(k2_xboole_0(sK0,sK2),X13))
      | ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2),X12),k3_xboole_0(X14,k2_xboole_0(sK0,sK1))) ) ),
    inference(resolution,[],[f63,f52])).

fof(f63,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2),X4),k2_xboole_0(sK0,sK1))
      | ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2),X4),X4)
      | k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != X4
      | ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2),X4),k3_xboole_0(k2_xboole_0(sK0,sK2),X5)) ) ),
    inference(resolution,[],[f57,f53])).

fof(f57,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2),X0),k2_xboole_0(sK0,sK2))
      | k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != X0
      | ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2),X0),X0)
      | ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2),X0),k2_xboole_0(sK0,sK1)) ) ),
    inference(superposition,[],[f28,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
