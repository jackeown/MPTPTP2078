%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:36 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 117 expanded)
%              Number of leaves         :   24 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :  206 ( 282 expanded)
%              Number of equality atoms :   33 (  47 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f116,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f62,f74,f91,f93,f107,f110,f115])).

fof(f115,plain,
    ( spl6_2
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f112,f105,f56])).

fof(f56,plain,
    ( spl6_2
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f105,plain,
    ( spl6_8
  <=> ! [X0] : ~ r2_hidden(X0,k2_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f112,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl6_8 ),
    inference(resolution,[],[f106,f42])).

fof(f42,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f106,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_relat_1(k1_xboole_0))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f105])).

fof(f110,plain,
    ( ~ spl6_3
    | spl6_7 ),
    inference(avatar_split_clause,[],[f108,f102,f60])).

fof(f60,plain,
    ( spl6_3
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f102,plain,
    ( spl6_7
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f108,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl6_7 ),
    inference(resolution,[],[f103,f38])).

fof(f38,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f103,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl6_7 ),
    inference(avatar_component_clause,[],[f102])).

fof(f107,plain,
    ( ~ spl6_7
    | spl6_8
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f96,f86,f105,f102])).

fof(f86,plain,
    ( spl6_4
  <=> ! [X0] : ~ r2_hidden(X0,k1_relat_1(k4_relat_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f96,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(k1_xboole_0))
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl6_4 ),
    inference(superposition,[],[f87,f40])).

fof(f40,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f87,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_relat_1(k4_relat_1(k1_xboole_0)))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f86])).

fof(f93,plain,(
    ~ spl6_5 ),
    inference(avatar_contradiction_clause,[],[f92])).

fof(f92,plain,
    ( $false
    | ~ spl6_5 ),
    inference(resolution,[],[f90,f64])).

fof(f64,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f63,f37])).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f63,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(resolution,[],[f44,f36])).

fof(f36,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f90,plain,
    ( r2_hidden(sK2(k4_relat_1(k1_xboole_0)),k1_xboole_0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl6_5
  <=> r2_hidden(sK2(k4_relat_1(k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f91,plain,
    ( spl6_4
    | spl6_5
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f84,f60,f53,f89,f86])).

fof(f53,plain,
    ( spl6_1
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f84,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(k4_relat_1(k1_xboole_0)),k1_xboole_0)
        | ~ r2_hidden(X0,k1_relat_1(k4_relat_1(k1_xboole_0))) )
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f83,f73])).

fof(f73,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f83,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(k4_relat_1(k1_xboole_0)),k1_relat_1(k1_xboole_0))
        | ~ r2_hidden(X0,k1_relat_1(k4_relat_1(k1_xboole_0))) )
    | ~ spl6_3 ),
    inference(resolution,[],[f81,f61])).

fof(f61,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | r2_hidden(sK2(k4_relat_1(X1)),k1_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(k4_relat_1(X1))) ) ),
    inference(resolution,[],[f68,f38])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(k4_relat_1(X0)))
      | r2_hidden(sK2(k4_relat_1(X0)),k1_relat_1(X0)) ) ),
    inference(global_subsumption,[],[f39,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(k4_relat_1(X0)),k1_relat_1(X0))
      | ~ r2_hidden(X1,k1_relat_1(k4_relat_1(X0)))
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f45,f41])).

fof(f41,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X1),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X1),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f26])).

fof(f26,plain,(
    ! [X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
     => r2_hidden(sK2(X1),k2_relat_1(X1)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k2_relat_1(X1))
          & r2_hidden(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_relat_1)).

fof(f39,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f74,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f72,f53])).

fof(f72,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f70,f42])).

fof(f70,plain,(
    ! [X2] : ~ r2_hidden(X2,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f51,f64])).

fof(f51,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f29,f32,f31,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f62,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f35,f60])).

fof(f35,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f58,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f34,f56,f53])).

fof(f34,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
      & k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:10:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.38  ipcrm: permission denied for id (819691521)
% 0.22/0.38  ipcrm: permission denied for id (819724290)
% 0.22/0.38  ipcrm: permission denied for id (823361539)
% 0.22/0.38  ipcrm: permission denied for id (826605572)
% 0.22/0.39  ipcrm: permission denied for id (819789829)
% 0.22/0.39  ipcrm: permission denied for id (819822598)
% 0.22/0.39  ipcrm: permission denied for id (823427079)
% 0.22/0.39  ipcrm: permission denied for id (819855368)
% 0.22/0.39  ipcrm: permission denied for id (825557001)
% 0.22/0.39  ipcrm: permission denied for id (819888138)
% 0.22/0.39  ipcrm: permission denied for id (819920907)
% 0.22/0.40  ipcrm: permission denied for id (826638348)
% 0.22/0.40  ipcrm: permission denied for id (819986445)
% 0.22/0.40  ipcrm: permission denied for id (820019214)
% 0.22/0.40  ipcrm: permission denied for id (826671119)
% 0.22/0.40  ipcrm: permission denied for id (820084752)
% 0.22/0.40  ipcrm: permission denied for id (823558161)
% 0.22/0.40  ipcrm: permission denied for id (823590930)
% 0.22/0.41  ipcrm: permission denied for id (820150292)
% 0.22/0.41  ipcrm: permission denied for id (820183061)
% 0.22/0.41  ipcrm: permission denied for id (823656470)
% 0.22/0.41  ipcrm: permission denied for id (820215831)
% 0.22/0.41  ipcrm: permission denied for id (820248600)
% 0.22/0.42  ipcrm: permission denied for id (820281369)
% 0.22/0.42  ipcrm: permission denied for id (820346907)
% 0.22/0.42  ipcrm: permission denied for id (825720860)
% 0.22/0.42  ipcrm: permission denied for id (820412445)
% 0.22/0.42  ipcrm: permission denied for id (825786399)
% 0.22/0.42  ipcrm: permission denied for id (820510752)
% 0.22/0.42  ipcrm: permission denied for id (820543521)
% 0.22/0.42  ipcrm: permission denied for id (823820322)
% 0.22/0.43  ipcrm: permission denied for id (820609059)
% 0.22/0.43  ipcrm: permission denied for id (820641828)
% 0.22/0.43  ipcrm: permission denied for id (823853093)
% 0.22/0.43  ipcrm: permission denied for id (820707366)
% 0.22/0.43  ipcrm: permission denied for id (826802215)
% 0.22/0.43  ipcrm: permission denied for id (820772904)
% 0.22/0.43  ipcrm: permission denied for id (820805673)
% 0.22/0.43  ipcrm: permission denied for id (826834986)
% 0.22/0.43  ipcrm: permission denied for id (823951403)
% 0.22/0.43  ipcrm: permission denied for id (820871212)
% 0.22/0.43  ipcrm: permission denied for id (823984173)
% 0.22/0.44  ipcrm: permission denied for id (820936750)
% 0.22/0.44  ipcrm: permission denied for id (825884719)
% 0.22/0.44  ipcrm: permission denied for id (821002288)
% 0.22/0.44  ipcrm: permission denied for id (824049713)
% 0.22/0.44  ipcrm: permission denied for id (821035058)
% 0.22/0.44  ipcrm: permission denied for id (821067827)
% 0.22/0.44  ipcrm: permission denied for id (821133364)
% 0.22/0.44  ipcrm: permission denied for id (821166133)
% 0.22/0.44  ipcrm: permission denied for id (825917494)
% 0.22/0.44  ipcrm: permission denied for id (821231671)
% 0.22/0.44  ipcrm: permission denied for id (821264440)
% 0.22/0.45  ipcrm: permission denied for id (821297209)
% 0.22/0.45  ipcrm: permission denied for id (821329978)
% 0.22/0.45  ipcrm: permission denied for id (825950267)
% 0.22/0.45  ipcrm: permission denied for id (821395516)
% 0.22/0.45  ipcrm: permission denied for id (824148029)
% 0.22/0.45  ipcrm: permission denied for id (824180798)
% 0.22/0.45  ipcrm: permission denied for id (824246336)
% 0.22/0.45  ipcrm: permission denied for id (824279105)
% 0.22/0.45  ipcrm: permission denied for id (824311874)
% 0.22/0.45  ipcrm: permission denied for id (821624899)
% 0.22/0.46  ipcrm: permission denied for id (821657668)
% 0.22/0.46  ipcrm: permission denied for id (824377413)
% 0.22/0.46  ipcrm: permission denied for id (821690438)
% 0.22/0.46  ipcrm: permission denied for id (824410183)
% 0.22/0.46  ipcrm: permission denied for id (821755976)
% 0.22/0.46  ipcrm: permission denied for id (821788745)
% 0.22/0.46  ipcrm: permission denied for id (821821514)
% 0.22/0.46  ipcrm: permission denied for id (826900555)
% 0.22/0.46  ipcrm: permission denied for id (824475724)
% 0.22/0.46  ipcrm: permission denied for id (826048589)
% 0.22/0.46  ipcrm: permission denied for id (824541262)
% 0.22/0.47  ipcrm: permission denied for id (826081359)
% 0.22/0.47  ipcrm: permission denied for id (821952592)
% 0.22/0.47  ipcrm: permission denied for id (821985361)
% 0.22/0.47  ipcrm: permission denied for id (822018130)
% 0.22/0.47  ipcrm: permission denied for id (824606803)
% 0.22/0.47  ipcrm: permission denied for id (826933332)
% 0.22/0.47  ipcrm: permission denied for id (824705109)
% 0.22/0.47  ipcrm: permission denied for id (824737878)
% 0.22/0.47  ipcrm: permission denied for id (822149207)
% 0.22/0.47  ipcrm: permission denied for id (822214744)
% 0.22/0.47  ipcrm: permission denied for id (822247513)
% 0.22/0.48  ipcrm: permission denied for id (822280282)
% 0.22/0.48  ipcrm: permission denied for id (826966107)
% 0.22/0.48  ipcrm: permission denied for id (822313052)
% 0.22/0.48  ipcrm: permission denied for id (822345821)
% 0.22/0.48  ipcrm: permission denied for id (826179678)
% 0.22/0.48  ipcrm: permission denied for id (824836191)
% 0.22/0.48  ipcrm: permission denied for id (824901729)
% 0.22/0.48  ipcrm: permission denied for id (826277986)
% 0.22/0.48  ipcrm: permission denied for id (822542435)
% 0.22/0.48  ipcrm: permission denied for id (826310756)
% 0.22/0.48  ipcrm: permission denied for id (822607973)
% 0.22/0.48  ipcrm: permission denied for id (822640742)
% 0.22/0.49  ipcrm: permission denied for id (825000039)
% 0.22/0.49  ipcrm: permission denied for id (822673512)
% 0.22/0.49  ipcrm: permission denied for id (825032809)
% 0.22/0.49  ipcrm: permission denied for id (826343530)
% 0.22/0.49  ipcrm: permission denied for id (826376299)
% 0.22/0.49  ipcrm: permission denied for id (822771820)
% 0.22/0.49  ipcrm: permission denied for id (825131117)
% 0.22/0.49  ipcrm: permission denied for id (822837358)
% 0.22/0.49  ipcrm: permission denied for id (826409071)
% 0.22/0.49  ipcrm: permission denied for id (822870128)
% 0.22/0.49  ipcrm: permission denied for id (822902897)
% 0.22/0.49  ipcrm: permission denied for id (825196658)
% 0.22/0.49  ipcrm: permission denied for id (822935667)
% 0.22/0.50  ipcrm: permission denied for id (823001205)
% 0.22/0.50  ipcrm: permission denied for id (825262198)
% 0.22/0.50  ipcrm: permission denied for id (823066743)
% 0.22/0.50  ipcrm: permission denied for id (825294968)
% 0.22/0.50  ipcrm: permission denied for id (823132281)
% 0.22/0.50  ipcrm: permission denied for id (825327738)
% 0.22/0.50  ipcrm: permission denied for id (825360507)
% 0.22/0.50  ipcrm: permission denied for id (826474620)
% 0.22/0.51  ipcrm: permission denied for id (827064445)
% 0.22/0.51  ipcrm: permission denied for id (826540158)
% 0.22/0.51  ipcrm: permission denied for id (823296127)
% 0.59/0.57  % (27124)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.59/0.57  % (27124)Refutation found. Thanks to Tanya!
% 0.59/0.57  % SZS status Theorem for theBenchmark
% 0.59/0.58  % (27132)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.59/0.58  % SZS output start Proof for theBenchmark
% 0.59/0.58  fof(f116,plain,(
% 0.59/0.58    $false),
% 0.59/0.58    inference(avatar_sat_refutation,[],[f58,f62,f74,f91,f93,f107,f110,f115])).
% 0.59/0.58  fof(f115,plain,(
% 0.59/0.58    spl6_2 | ~spl6_8),
% 0.59/0.58    inference(avatar_split_clause,[],[f112,f105,f56])).
% 0.59/0.58  fof(f56,plain,(
% 0.59/0.58    spl6_2 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.59/0.58  fof(f105,plain,(
% 0.59/0.58    spl6_8 <=> ! [X0] : ~r2_hidden(X0,k2_relat_1(k1_xboole_0))),
% 0.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.59/0.58  fof(f112,plain,(
% 0.59/0.58    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl6_8),
% 0.59/0.58    inference(resolution,[],[f106,f42])).
% 0.59/0.58  fof(f42,plain,(
% 0.59/0.58    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 0.59/0.58    inference(cnf_transformation,[],[f23])).
% 0.59/0.58  fof(f23,plain,(
% 0.59/0.58    ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0)),
% 0.59/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f22])).
% 0.59/0.58  fof(f22,plain,(
% 0.59/0.58    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 0.59/0.58    introduced(choice_axiom,[])).
% 0.59/0.58  fof(f18,plain,(
% 0.59/0.58    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.59/0.58    inference(ennf_transformation,[],[f3])).
% 0.59/0.58  fof(f3,axiom,(
% 0.59/0.58    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.59/0.58  fof(f106,plain,(
% 0.59/0.58    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(k1_xboole_0))) ) | ~spl6_8),
% 0.59/0.58    inference(avatar_component_clause,[],[f105])).
% 0.59/0.58  fof(f110,plain,(
% 0.59/0.58    ~spl6_3 | spl6_7),
% 0.59/0.58    inference(avatar_split_clause,[],[f108,f102,f60])).
% 0.59/0.58  fof(f60,plain,(
% 0.59/0.58    spl6_3 <=> v1_xboole_0(k1_xboole_0)),
% 0.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.59/0.58  fof(f102,plain,(
% 0.59/0.58    spl6_7 <=> v1_relat_1(k1_xboole_0)),
% 0.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.59/0.58  fof(f108,plain,(
% 0.59/0.58    ~v1_xboole_0(k1_xboole_0) | spl6_7),
% 0.59/0.58    inference(resolution,[],[f103,f38])).
% 0.59/0.58  fof(f38,plain,(
% 0.59/0.58    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.59/0.58    inference(cnf_transformation,[],[f15])).
% 0.59/0.58  fof(f15,plain,(
% 0.59/0.58    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.59/0.58    inference(ennf_transformation,[],[f6])).
% 0.59/0.58  fof(f6,axiom,(
% 0.59/0.58    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.59/0.58  fof(f103,plain,(
% 0.59/0.58    ~v1_relat_1(k1_xboole_0) | spl6_7),
% 0.59/0.58    inference(avatar_component_clause,[],[f102])).
% 0.59/0.58  fof(f107,plain,(
% 0.59/0.58    ~spl6_7 | spl6_8 | ~spl6_4),
% 0.59/0.58    inference(avatar_split_clause,[],[f96,f86,f105,f102])).
% 0.59/0.58  fof(f86,plain,(
% 0.59/0.58    spl6_4 <=> ! [X0] : ~r2_hidden(X0,k1_relat_1(k4_relat_1(k1_xboole_0)))),
% 0.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.59/0.58  fof(f96,plain,(
% 0.59/0.58    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)) ) | ~spl6_4),
% 0.59/0.58    inference(superposition,[],[f87,f40])).
% 0.59/0.58  fof(f40,plain,(
% 0.59/0.58    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.59/0.58    inference(cnf_transformation,[],[f17])).
% 0.59/0.58  fof(f17,plain,(
% 0.59/0.58    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.59/0.58    inference(ennf_transformation,[],[f10])).
% 0.59/0.58  fof(f10,axiom,(
% 0.59/0.58    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 0.59/0.58  fof(f87,plain,(
% 0.59/0.58    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k4_relat_1(k1_xboole_0)))) ) | ~spl6_4),
% 0.59/0.58    inference(avatar_component_clause,[],[f86])).
% 0.59/0.58  fof(f93,plain,(
% 0.59/0.58    ~spl6_5),
% 0.59/0.58    inference(avatar_contradiction_clause,[],[f92])).
% 0.59/0.58  fof(f92,plain,(
% 0.59/0.58    $false | ~spl6_5),
% 0.59/0.58    inference(resolution,[],[f90,f64])).
% 0.59/0.58  fof(f64,plain,(
% 0.59/0.58    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.59/0.58    inference(forward_demodulation,[],[f63,f37])).
% 0.59/0.58  fof(f37,plain,(
% 0.59/0.58    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.59/0.58    inference(cnf_transformation,[],[f4])).
% 0.59/0.58  fof(f4,axiom,(
% 0.59/0.58    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.59/0.58  fof(f63,plain,(
% 0.59/0.58    ( ! [X0,X1] : (~r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0))) )),
% 0.59/0.58    inference(resolution,[],[f44,f36])).
% 0.59/0.58  fof(f36,plain,(
% 0.59/0.58    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.59/0.58    inference(cnf_transformation,[],[f5])).
% 0.59/0.58  fof(f5,axiom,(
% 0.59/0.58    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.59/0.58  fof(f44,plain,(
% 0.59/0.58    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.59/0.58    inference(cnf_transformation,[],[f25])).
% 0.59/0.58  fof(f25,plain,(
% 0.59/0.58    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.59/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f24])).
% 0.59/0.58  fof(f24,plain,(
% 0.59/0.58    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 0.59/0.58    introduced(choice_axiom,[])).
% 0.59/0.58  fof(f19,plain,(
% 0.59/0.58    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.59/0.58    inference(ennf_transformation,[],[f13])).
% 0.59/0.58  fof(f13,plain,(
% 0.59/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.59/0.58    inference(rectify,[],[f2])).
% 0.59/0.58  fof(f2,axiom,(
% 0.59/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.59/0.58  fof(f90,plain,(
% 0.59/0.58    r2_hidden(sK2(k4_relat_1(k1_xboole_0)),k1_xboole_0) | ~spl6_5),
% 0.59/0.58    inference(avatar_component_clause,[],[f89])).
% 0.59/0.58  fof(f89,plain,(
% 0.59/0.58    spl6_5 <=> r2_hidden(sK2(k4_relat_1(k1_xboole_0)),k1_xboole_0)),
% 0.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.59/0.58  fof(f91,plain,(
% 0.59/0.58    spl6_4 | spl6_5 | ~spl6_1 | ~spl6_3),
% 0.59/0.58    inference(avatar_split_clause,[],[f84,f60,f53,f89,f86])).
% 0.59/0.58  fof(f53,plain,(
% 0.59/0.58    spl6_1 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.59/0.58  fof(f84,plain,(
% 0.59/0.58    ( ! [X0] : (r2_hidden(sK2(k4_relat_1(k1_xboole_0)),k1_xboole_0) | ~r2_hidden(X0,k1_relat_1(k4_relat_1(k1_xboole_0)))) ) | (~spl6_1 | ~spl6_3)),
% 0.59/0.58    inference(forward_demodulation,[],[f83,f73])).
% 0.59/0.58  fof(f73,plain,(
% 0.59/0.58    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl6_1),
% 0.59/0.58    inference(avatar_component_clause,[],[f53])).
% 0.59/0.58  fof(f83,plain,(
% 0.59/0.58    ( ! [X0] : (r2_hidden(sK2(k4_relat_1(k1_xboole_0)),k1_relat_1(k1_xboole_0)) | ~r2_hidden(X0,k1_relat_1(k4_relat_1(k1_xboole_0)))) ) | ~spl6_3),
% 0.59/0.58    inference(resolution,[],[f81,f61])).
% 0.59/0.58  fof(f61,plain,(
% 0.59/0.58    v1_xboole_0(k1_xboole_0) | ~spl6_3),
% 0.59/0.58    inference(avatar_component_clause,[],[f60])).
% 0.59/0.58  fof(f81,plain,(
% 0.59/0.58    ( ! [X0,X1] : (~v1_xboole_0(X1) | r2_hidden(sK2(k4_relat_1(X1)),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(k4_relat_1(X1)))) )),
% 0.59/0.58    inference(resolution,[],[f68,f38])).
% 0.59/0.58  fof(f68,plain,(
% 0.59/0.58    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r2_hidden(X1,k1_relat_1(k4_relat_1(X0))) | r2_hidden(sK2(k4_relat_1(X0)),k1_relat_1(X0))) )),
% 0.59/0.58    inference(global_subsumption,[],[f39,f67])).
% 0.59/0.58  fof(f67,plain,(
% 0.59/0.58    ( ! [X0,X1] : (r2_hidden(sK2(k4_relat_1(X0)),k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.59/0.58    inference(superposition,[],[f45,f41])).
% 0.59/0.58  fof(f41,plain,(
% 0.59/0.58    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.59/0.58    inference(cnf_transformation,[],[f17])).
% 0.59/0.58  fof(f45,plain,(
% 0.59/0.58    ( ! [X0,X1] : (r2_hidden(sK2(X1),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.59/0.58    inference(cnf_transformation,[],[f27])).
% 0.59/0.58  fof(f27,plain,(
% 0.59/0.58    ! [X0,X1] : (r2_hidden(sK2(X1),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.59/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f26])).
% 0.59/0.58  fof(f26,plain,(
% 0.59/0.58    ! [X1] : (? [X2] : r2_hidden(X2,k2_relat_1(X1)) => r2_hidden(sK2(X1),k2_relat_1(X1)))),
% 0.59/0.58    introduced(choice_axiom,[])).
% 0.59/0.58  fof(f21,plain,(
% 0.59/0.58    ! [X0,X1] : (? [X2] : r2_hidden(X2,k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.59/0.58    inference(flattening,[],[f20])).
% 0.59/0.58  fof(f20,plain,(
% 0.59/0.58    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.59/0.58    inference(ennf_transformation,[],[f9])).
% 0.59/0.58  fof(f9,axiom,(
% 0.59/0.58    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k2_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X1))))),
% 0.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_relat_1)).
% 0.59/0.58  fof(f39,plain,(
% 0.59/0.58    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.59/0.58    inference(cnf_transformation,[],[f16])).
% 0.59/0.58  fof(f16,plain,(
% 0.59/0.58    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.59/0.58    inference(ennf_transformation,[],[f8])).
% 0.59/0.58  fof(f8,axiom,(
% 0.59/0.58    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.59/0.58  fof(f74,plain,(
% 0.59/0.58    spl6_1),
% 0.59/0.58    inference(avatar_split_clause,[],[f72,f53])).
% 0.59/0.58  fof(f72,plain,(
% 0.59/0.58    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.59/0.58    inference(resolution,[],[f70,f42])).
% 0.59/0.58  fof(f70,plain,(
% 0.59/0.58    ( ! [X2] : (~r2_hidden(X2,k1_relat_1(k1_xboole_0))) )),
% 0.59/0.58    inference(resolution,[],[f51,f64])).
% 0.59/0.58  fof(f51,plain,(
% 0.59/0.58    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 0.59/0.58    inference(equality_resolution,[],[f46])).
% 0.59/0.58  fof(f46,plain,(
% 0.59/0.58    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 0.59/0.58    inference(cnf_transformation,[],[f33])).
% 0.59/0.58  fof(f33,plain,(
% 0.59/0.58    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.59/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f29,f32,f31,f30])).
% 0.59/0.58  fof(f30,plain,(
% 0.59/0.58    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 0.59/0.58    introduced(choice_axiom,[])).
% 0.59/0.58  fof(f31,plain,(
% 0.59/0.58    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0))),
% 0.59/0.58    introduced(choice_axiom,[])).
% 0.59/0.58  fof(f32,plain,(
% 0.59/0.58    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0))),
% 0.59/0.58    introduced(choice_axiom,[])).
% 0.59/0.58  fof(f29,plain,(
% 0.59/0.58    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.59/0.58    inference(rectify,[],[f28])).
% 0.59/0.58  fof(f28,plain,(
% 0.59/0.58    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 0.59/0.58    inference(nnf_transformation,[],[f7])).
% 0.59/0.58  fof(f7,axiom,(
% 0.59/0.58    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 0.59/0.58  fof(f62,plain,(
% 0.59/0.58    spl6_3),
% 0.59/0.58    inference(avatar_split_clause,[],[f35,f60])).
% 0.59/0.58  fof(f35,plain,(
% 0.59/0.58    v1_xboole_0(k1_xboole_0)),
% 0.59/0.58    inference(cnf_transformation,[],[f1])).
% 0.59/0.58  fof(f1,axiom,(
% 0.59/0.58    v1_xboole_0(k1_xboole_0)),
% 0.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.59/0.58  fof(f58,plain,(
% 0.59/0.58    ~spl6_1 | ~spl6_2),
% 0.59/0.58    inference(avatar_split_clause,[],[f34,f56,f53])).
% 0.59/0.58  fof(f34,plain,(
% 0.59/0.58    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 0.59/0.58    inference(cnf_transformation,[],[f14])).
% 0.59/0.58  fof(f14,plain,(
% 0.59/0.58    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 0.59/0.58    inference(ennf_transformation,[],[f12])).
% 0.59/0.58  fof(f12,negated_conjecture,(
% 0.59/0.58    ~(k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0))),
% 0.59/0.58    inference(negated_conjecture,[],[f11])).
% 0.59/0.58  fof(f11,conjecture,(
% 0.59/0.58    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.59/0.58  % SZS output end Proof for theBenchmark
% 0.59/0.58  % (27124)------------------------------
% 0.59/0.58  % (27124)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.59/0.58  % (27124)Termination reason: Refutation
% 0.59/0.58  
% 0.59/0.58  % (27124)Memory used [KB]: 10618
% 0.59/0.58  % (27124)Time elapsed: 0.029 s
% 0.59/0.58  % (27124)------------------------------
% 0.59/0.58  % (27124)------------------------------
% 0.59/0.59  % (26982)Success in time 0.213 s
%------------------------------------------------------------------------------
