%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : xboole_1__t65_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:30 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   37 (  41 expanded)
%              Number of leaves         :   11 (  14 expanded)
%              Depth                    :   10
%              Number of atoms          :   79 (  85 expanded)
%              Number of equality atoms :    3 (   5 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f66,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f49,f56,f65])).

fof(f65,plain,
    ( ~ spl2_0
    | spl2_3 ),
    inference(avatar_contradiction_clause,[],[f63])).

fof(f63,plain,
    ( $false
    | ~ spl2_0
    | ~ spl2_3 ),
    inference(resolution,[],[f62,f48])).

fof(f48,plain,
    ( ~ r1_xboole_0(sK0,k1_xboole_0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl2_3
  <=> ~ r1_xboole_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f62,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl2_0 ),
    inference(resolution,[],[f61,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t65_xboole_1.p',symmetry_r1_xboole_0)).

fof(f61,plain,
    ( ! [X0] : r1_xboole_0(k1_xboole_0,X0)
    | ~ spl2_0 ),
    inference(resolution,[],[f60,f41])).

fof(f41,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl2_0 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl2_0
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_0])])).

fof(f60,plain,(
    ! [X2,X3] :
      ( ~ v1_xboole_0(X2)
      | r1_xboole_0(X2,X3) ) ),
    inference(resolution,[],[f28,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t65_xboole_1.p',t7_boole)).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t65_xboole_1.p',t3_xboole_0)).

fof(f56,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f26,f54])).

fof(f54,plain,
    ( spl2_4
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f26,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t65_xboole_1.p',d2_xboole_0)).

fof(f49,plain,(
    ~ spl2_3 ),
    inference(avatar_split_clause,[],[f24,f47])).

fof(f24,plain,(
    ~ r1_xboole_0(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ~ r1_xboole_0(sK0,k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f20])).

fof(f20,plain,
    ( ? [X0] : ~ r1_xboole_0(X0,k1_xboole_0)
   => ~ r1_xboole_0(sK0,k1_xboole_0) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] : ~ r1_xboole_0(X0,k1_xboole_0) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t65_xboole_1.p',t65_xboole_1)).

fof(f42,plain,(
    spl2_0 ),
    inference(avatar_split_clause,[],[f35,f40])).

fof(f35,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f25,f26])).

fof(f25,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t65_xboole_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
