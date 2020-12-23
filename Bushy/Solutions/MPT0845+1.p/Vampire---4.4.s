%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : mcart_1__t1_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:05 EDT 2019

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 140 expanded)
%              Number of leaves         :   11 (  40 expanded)
%              Depth                    :   12
%              Number of atoms          :  130 ( 417 expanded)
%              Number of equality atoms :   17 (  62 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f205,plain,(
    $false ),
    inference(subsumption_resolution,[],[f200,f98])).

fof(f98,plain,(
    r2_hidden(sK2(sK0,sK3(sK0)),sK0) ),
    inference(resolution,[],[f91,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(sK2(sK0,X0),sK0) ) ),
    inference(resolution,[],[f62,f39])).

fof(f39,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(X1,sK0)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(X1,sK0)
        | ~ r2_hidden(X1,sK0) )
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( ! [X1] :
            ( ~ r1_xboole_0(X1,X0)
            | ~ r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 )
   => ( ! [X1] :
          ( ~ r1_xboole_0(X1,sK0)
          | ~ r2_hidden(X1,sK0) )
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ r1_xboole_0(X1,X0)
          | ~ r2_hidden(X1,X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ~ ( ! [X1] :
              ~ ( r1_xboole_0(X1,X0)
                & r2_hidden(X1,X0) )
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( r1_xboole_0(X1,X0)
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t1_mcart_1.p',t1_mcart_1)).

fof(f62,plain,(
    ! [X2,X1] :
      ( r1_xboole_0(X2,X1)
      | r2_hidden(sK2(X1,X2),X1) ) ),
    inference(resolution,[],[f45,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t1_mcart_1.p',symmetry_r1_xboole_0)).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t1_mcart_1.p',t3_xboole_0)).

fof(f91,plain,(
    r2_hidden(sK3(sK0),sK0) ),
    inference(resolution,[],[f83,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(sK3(X1),X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK3(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK3(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f36])).

fof(f36,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK3(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK3(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t1_mcart_1.p',t7_tarski)).

fof(f83,plain,(
    r2_hidden(sK2(sK0,o_1_0_mcart_1(sK0)),sK0) ),
    inference(subsumption_resolution,[],[f79,f56])).

fof(f56,plain,(
    o_0_0_xboole_0 != sK0 ),
    inference(definition_unfolding,[],[f38,f41])).

fof(f41,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t1_mcart_1.p',d2_xboole_0)).

fof(f38,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f31])).

fof(f79,plain,
    ( o_0_0_xboole_0 = sK0
    | r2_hidden(sK2(sK0,o_1_0_mcart_1(sK0)),sK0) ),
    inference(resolution,[],[f71,f67])).

fof(f71,plain,(
    ! [X0] :
      ( r2_hidden(o_1_0_mcart_1(X0),X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(resolution,[],[f66,f42])).

fof(f42,plain,(
    ! [X0] : m1_subset_1(o_1_0_mcart_1(X0),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(o_1_0_mcart_1(X0),X0) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t1_mcart_1.p',dt_o_1_0_mcart_1)).

fof(f66,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X3,X4)
      | r2_hidden(X3,X4)
      | o_0_0_xboole_0 = X4 ) ),
    inference(resolution,[],[f49,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f43,f41])).

fof(f43,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t1_mcart_1.p',t6_boole)).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t1_mcart_1.p',t2_subset)).

fof(f200,plain,(
    ~ r2_hidden(sK2(sK0,sK3(sK0)),sK0) ),
    inference(resolution,[],[f97,f58])).

fof(f58,plain,(
    ! [X3,X1] :
      ( ~ r2_hidden(X3,sK3(X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(condensation,[],[f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,sK3(X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f97,plain,(
    r2_hidden(sK2(sK0,sK3(sK0)),sK3(sK0)) ),
    inference(resolution,[],[f91,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(sK2(sK0,X0),X0) ) ),
    inference(resolution,[],[f64,f39])).

fof(f64,plain,(
    ! [X2,X1] :
      ( r1_xboole_0(X2,X1)
      | r2_hidden(sK2(X1,X2),X2) ) ),
    inference(resolution,[],[f46,f48])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
