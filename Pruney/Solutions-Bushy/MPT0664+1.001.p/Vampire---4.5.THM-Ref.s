%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0664+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:24 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 140 expanded)
%              Number of leaves         :   10 (  38 expanded)
%              Depth                    :   13
%              Number of atoms          :  218 ( 544 expanded)
%              Number of equality atoms :   31 ( 119 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f272,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f234,f255,f271])).

fof(f271,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f270])).

fof(f270,plain,
    ( $false
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f269,f23])).

fof(f23,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( k1_funct_1(k7_relat_1(sK2,sK1),sK0) != k1_funct_1(sK2,sK0)
    & r2_hidden(sK0,sK1)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0)
        & r2_hidden(X0,X1)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k1_funct_1(k7_relat_1(sK2,sK1),sK0) != k1_funct_1(sK2,sK0)
      & r2_hidden(sK0,sK1)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0)
      & r2_hidden(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0)
      & r2_hidden(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,X1)
         => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,X1)
       => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_funct_1)).

fof(f269,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f268,f24])).

fof(f24,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f268,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f261,f42])).

fof(f42,plain,(
    ~ sQ3_eqProxy(k1_funct_1(k7_relat_1(sK2,sK1),sK0),k1_funct_1(sK2,sK0)) ),
    inference(equality_proxy_replacement,[],[f26,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( sQ3_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).

fof(f26,plain,(
    k1_funct_1(k7_relat_1(sK2,sK1),sK0) != k1_funct_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f261,plain,
    ( sQ3_eqProxy(k1_funct_1(k7_relat_1(sK2,sK1),sK0),k1_funct_1(sK2,sK0))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_2 ),
    inference(resolution,[],[f233,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | sQ3_eqProxy(k1_funct_1(k7_relat_1(X2,X1),X0),k1_funct_1(X2,X0))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_proxy_replacement,[],[f37,f41])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
       => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_funct_1)).

fof(f233,plain,
    ( r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f231])).

fof(f231,plain,
    ( spl4_2
  <=> r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f255,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_contradiction_clause,[],[f254])).

fof(f254,plain,
    ( $false
    | spl4_1
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f25,f243,f232,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( sQ3_eqProxy(k1_funct_1(sK2,X0),k1_xboole_0)
      | r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,X1)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(subsumption_resolution,[],[f107,f23])).

fof(f107,plain,(
    ! [X0,X1] :
      ( sQ3_eqProxy(k1_funct_1(sK2,X0),k1_xboole_0)
      | r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,X1)))
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f99,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X2))
      | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

fof(f99,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_relat_1(sK2))
      | sQ3_eqProxy(k1_funct_1(sK2,X0),k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f96,f23])).

fof(f96,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_relat_1(sK2))
      | sQ3_eqProxy(k1_funct_1(sK2,X0),k1_xboole_0)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f43,f24])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(X1,k1_relat_1(X0))
      | sQ3_eqProxy(k1_funct_1(X0,X1),k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f38,f41])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,X1) = k1_xboole_0
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) = X2
      | k1_xboole_0 != X2
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( ( k1_funct_1(X0,X1) = X2
                | k1_xboole_0 != X2 )
              & ( k1_xboole_0 = X2
                | k1_funct_1(X0,X1) != X2 ) )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( ( k1_funct_1(X0,X1) = X2
                | ~ r2_hidden(k4_tarski(X1,X2),X0) )
              & ( r2_hidden(k4_tarski(X1,X2),X0)
                | k1_funct_1(X0,X1) != X2 ) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

fof(f232,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f231])).

fof(f243,plain,
    ( ~ sQ3_eqProxy(k1_funct_1(sK2,sK0),k1_xboole_0)
    | spl4_1 ),
    inference(resolution,[],[f229,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( sQ3_eqProxy(X1,X0)
      | ~ sQ3_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f41])).

fof(f229,plain,
    ( ~ sQ3_eqProxy(k1_xboole_0,k1_funct_1(sK2,sK0))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f227])).

fof(f227,plain,
    ( spl4_1
  <=> sQ3_eqProxy(k1_xboole_0,k1_funct_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f25,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f234,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f221,f231,f227])).

fof(f221,plain,
    ( r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ sQ3_eqProxy(k1_xboole_0,k1_funct_1(sK2,sK0)) ),
    inference(resolution,[],[f196,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ sQ3_eqProxy(k1_funct_1(k7_relat_1(sK2,sK1),sK0),X0)
      | ~ sQ3_eqProxy(X0,k1_funct_1(sK2,sK0)) ) ),
    inference(resolution,[],[f56,f42])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( sQ3_eqProxy(X0,X2)
      | ~ sQ3_eqProxy(X1,X2)
      | ~ sQ3_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f41])).

fof(f196,plain,(
    ! [X0,X1] :
      ( sQ3_eqProxy(k1_funct_1(k7_relat_1(sK2,X0),X1),k1_xboole_0)
      | r2_hidden(X1,k1_relat_1(k7_relat_1(sK2,X0))) ) ),
    inference(subsumption_resolution,[],[f193,f23])).

fof(f193,plain,(
    ! [X0,X1] :
      ( sQ3_eqProxy(k1_funct_1(k7_relat_1(sK2,X0),X1),k1_xboole_0)
      | r2_hidden(X1,k1_relat_1(k7_relat_1(sK2,X0)))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f100,f24])).

fof(f100,plain,(
    ! [X6,X4,X5] :
      ( ~ v1_funct_1(X5)
      | sQ3_eqProxy(k1_funct_1(k7_relat_1(X5,X6),X4),k1_xboole_0)
      | r2_hidden(X4,k1_relat_1(k7_relat_1(X5,X6)))
      | ~ v1_relat_1(X5) ) ),
    inference(subsumption_resolution,[],[f98,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f98,plain,(
    ! [X6,X4,X5] :
      ( r2_hidden(X4,k1_relat_1(k7_relat_1(X5,X6)))
      | sQ3_eqProxy(k1_funct_1(k7_relat_1(X5,X6),X4),k1_xboole_0)
      | ~ v1_relat_1(k7_relat_1(X5,X6))
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(X5) ) ),
    inference(resolution,[],[f43,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

%------------------------------------------------------------------------------
