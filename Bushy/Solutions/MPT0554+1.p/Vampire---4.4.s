%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t156_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:52 EDT 2019

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 116 expanded)
%              Number of leaves         :    8 (  31 expanded)
%              Depth                    :   17
%              Number of atoms          :  185 ( 357 expanded)
%              Number of equality atoms :    5 (   9 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f623,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f55,f62,f257,f622])).

fof(f622,plain,
    ( ~ spl7_0
    | ~ spl7_2
    | spl7_5 ),
    inference(avatar_contradiction_clause,[],[f621])).

fof(f621,plain,
    ( $false
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f620,f65])).

fof(f65,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f38,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t156_relat_1.p',d3_tarski)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f620,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f605,f47])).

fof(f47,plain,
    ( v1_relat_1(sK2)
    | ~ spl7_0 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl7_0
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_0])])).

fof(f605,plain,
    ( ~ v1_relat_1(sK2)
    | ~ r1_tarski(sK0,sK0)
    | ~ spl7_2
    | ~ spl7_5 ),
    inference(resolution,[],[f522,f61])).

fof(f61,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl7_5
  <=> ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f522,plain,
    ( ! [X24,X23] :
        ( r1_tarski(k9_relat_1(X23,X24),k9_relat_1(X23,sK1))
        | ~ v1_relat_1(X23)
        | ~ r1_tarski(X24,sK0) )
    | ~ spl7_2 ),
    inference(duplicate_literal_removal,[],[f520])).

fof(f520,plain,
    ( ! [X24,X23] :
        ( ~ v1_relat_1(X23)
        | r1_tarski(k9_relat_1(X23,X24),k9_relat_1(X23,sK1))
        | ~ r1_tarski(X24,sK0)
        | r1_tarski(k9_relat_1(X23,X24),k9_relat_1(X23,sK1)) )
    | ~ spl7_2 ),
    inference(resolution,[],[f490,f38])).

fof(f490,plain,
    ( ! [X10,X8,X9] :
        ( r2_hidden(sK6(k9_relat_1(X9,X8),X10),k9_relat_1(X9,sK1))
        | ~ v1_relat_1(X9)
        | r1_tarski(k9_relat_1(X9,X8),X10)
        | ~ r1_tarski(X8,sK0) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f487,f37])).

fof(f487,plain,
    ( ! [X10,X8,X9] :
        ( ~ r1_tarski(X8,sK0)
        | ~ v1_relat_1(X9)
        | r1_tarski(k9_relat_1(X9,X8),X10)
        | ~ r2_hidden(sK6(k9_relat_1(X9,X8),X10),k9_relat_1(X9,X8))
        | r2_hidden(sK6(k9_relat_1(X9,X8),X10),k9_relat_1(X9,sK1)) )
    | ~ spl7_2 ),
    inference(duplicate_literal_removal,[],[f486])).

fof(f486,plain,
    ( ! [X10,X8,X9] :
        ( ~ r1_tarski(X8,sK0)
        | ~ v1_relat_1(X9)
        | r1_tarski(k9_relat_1(X9,X8),X10)
        | ~ r2_hidden(sK6(k9_relat_1(X9,X8),X10),k9_relat_1(X9,X8))
        | ~ v1_relat_1(X9)
        | r2_hidden(sK6(k9_relat_1(X9,X8),X10),k9_relat_1(X9,sK1)) )
    | ~ spl7_2 ),
    inference(resolution,[],[f452,f70])).

fof(f70,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_hidden(sK4(X4,X6,X5),X7)
      | ~ r2_hidden(X5,k9_relat_1(X4,X6))
      | ~ v1_relat_1(X4)
      | r2_hidden(X5,k9_relat_1(X4,X7)) ) ),
    inference(duplicate_literal_removal,[],[f69])).

fof(f69,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ v1_relat_1(X4)
      | ~ r2_hidden(X5,k9_relat_1(X4,X6))
      | ~ v1_relat_1(X4)
      | ~ r2_hidden(sK4(X4,X6,X5),X7)
      | r2_hidden(X5,k9_relat_1(X4,X7)) ) ),
    inference(resolution,[],[f41,f39])).

fof(f39,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t156_relat_1.p',d13_relat_1)).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1,X3),X3),X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK4(X0,X1,X3),X3),X0)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f452,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(sK4(X1,X0,sK6(k9_relat_1(X1,X0),X2)),sK1)
        | ~ r1_tarski(X0,sK0)
        | ~ v1_relat_1(X1)
        | r1_tarski(k9_relat_1(X1,X0),X2) )
    | ~ spl7_2 ),
    inference(resolution,[],[f143,f54])).

fof(f54,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl7_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f143,plain,(
    ! [X94,X92,X95,X93,X96] :
      ( ~ r1_tarski(X94,X96)
      | ~ r1_tarski(X93,X94)
      | r2_hidden(sK4(X92,X93,sK6(k9_relat_1(X92,X93),X95)),X96)
      | ~ v1_relat_1(X92)
      | r1_tarski(k9_relat_1(X92,X93),X95) ) ),
    inference(resolution,[],[f83,f37])).

fof(f83,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X2,X3)
      | r2_hidden(sK4(X1,X2,X0),X4)
      | ~ r1_tarski(X3,X4) ) ),
    inference(resolution,[],[f67,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK4(X0,X2,X1),X3)
      | ~ r2_hidden(X1,k9_relat_1(X0,X2))
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f40,f36])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK4(X0,X1,X3),X1)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK4(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f257,plain,
    ( ~ spl7_7
    | spl7_8
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f220,f53,f255,f252])).

fof(f252,plain,
    ( spl7_7
  <=> ~ r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f255,plain,
    ( spl7_8
  <=> ! [X0] :
        ( r1_tarski(sK0,X0)
        | r2_hidden(sK6(sK0,X0),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f220,plain,
    ( ! [X0] :
        ( r1_tarski(sK0,X0)
        | r2_hidden(sK6(sK0,X0),sK1)
        | ~ r1_tarski(sK1,sK0) )
    | ~ spl7_2 ),
    inference(resolution,[],[f111,f54])).

fof(f111,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X1,X0)
        | r1_tarski(X1,X2)
        | r2_hidden(sK6(X1,X2),sK1)
        | ~ r1_tarski(X0,sK0) )
    | ~ spl7_2 ),
    inference(resolution,[],[f99,f76])).

fof(f76,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ r1_tarski(X3,X5)
      | r1_tarski(X2,X4)
      | r2_hidden(sK6(X2,X4),X5)
      | ~ r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f66,f36])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1),X2)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f36,f37])).

fof(f99,plain,
    ( ! [X0] :
        ( r1_tarski(X0,sK1)
        | ~ r1_tarski(X0,sK0) )
    | ~ spl7_2 ),
    inference(duplicate_literal_removal,[],[f97])).

fof(f97,plain,
    ( ! [X0] :
        ( r1_tarski(X0,sK1)
        | ~ r1_tarski(X0,sK0)
        | r1_tarski(X0,sK1) )
    | ~ spl7_2 ),
    inference(resolution,[],[f87,f38])).

fof(f87,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK6(X0,X1),sK1)
        | r1_tarski(X0,X1)
        | ~ r1_tarski(X0,sK0) )
    | ~ spl7_2 ),
    inference(resolution,[],[f76,f54])).

fof(f62,plain,(
    ~ spl7_5 ),
    inference(avatar_split_clause,[],[f27,f60])).

fof(f27,plain,(
    ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t156_relat_1.p',t156_relat_1)).

fof(f55,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f26,f53])).

fof(f26,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f48,plain,(
    spl7_0 ),
    inference(avatar_split_clause,[],[f25,f46])).

fof(f25,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
