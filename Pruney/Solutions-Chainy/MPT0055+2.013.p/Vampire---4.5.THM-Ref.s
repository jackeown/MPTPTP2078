%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:06 EST 2020

% Result     : Theorem 3.27s
% Output     : Refutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 179 expanded)
%              Number of leaves         :   19 (  55 expanded)
%              Depth                    :   13
%              Number of atoms          :  204 ( 795 expanded)
%              Number of equality atoms :   61 ( 167 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3404,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f287,f2781,f3382,f3403])).

fof(f3403,plain,
    ( ~ spl4_4
    | spl4_7 ),
    inference(avatar_contradiction_clause,[],[f3402])).

fof(f3402,plain,
    ( $false
    | ~ spl4_4
    | spl4_7 ),
    inference(subsumption_resolution,[],[f3401,f2783])).

fof(f2783,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),o_0_0_xboole_0),sK0)
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f2780,f236])).

fof(f236,plain,(
    ! [X12,X13,X11] :
      ( ~ r2_hidden(X13,k3_xboole_0(X11,X12))
      | r2_hidden(X13,X11) ) ),
    inference(subsumption_resolution,[],[f228,f99])).

fof(f99,plain,(
    ! [X0] : ~ r2_hidden(X0,o_0_0_xboole_0) ),
    inference(condensation,[],[f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X1,o_0_0_xboole_0) ) ),
    inference(superposition,[],[f64,f58])).

fof(f58,plain,(
    ! [X0] : k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f35,f34])).

fof(f34,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f35,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f64,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f228,plain,(
    ! [X12,X13,X11] :
      ( r2_hidden(X13,o_0_0_xboole_0)
      | r2_hidden(X13,X11)
      | ~ r2_hidden(X13,k3_xboole_0(X11,X12)) ) ),
    inference(superposition,[],[f63,f80])).

fof(f80,plain,(
    ! [X0,X1] : o_0_0_xboole_0 = k4_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(unit_resulting_resolution,[],[f36,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | o_0_0_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f50,f34])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f63,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f2780,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),o_0_0_xboole_0),k3_xboole_0(sK0,sK1))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f2778])).

fof(f2778,plain,
    ( spl4_4
  <=> r2_hidden(sK3(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),o_0_0_xboole_0),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f3401,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),o_0_0_xboole_0),sK0)
    | ~ spl4_4
    | spl4_7 ),
    inference(subsumption_resolution,[],[f3391,f3204])).

fof(f3204,plain,
    ( ! [X0] : ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),o_0_0_xboole_0),k4_xboole_0(X0,sK1))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f2780,f556])).

fof(f556,plain,(
    ! [X14,X12,X15,X13] :
      ( ~ r2_hidden(X14,k4_xboole_0(X15,X12))
      | ~ r2_hidden(X14,k3_xboole_0(X13,X12)) ) ),
    inference(superposition,[],[f151,f74])).

fof(f74,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[],[f40,f39])).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f151,plain,(
    ! [X14,X17,X15,X16] :
      ( ~ r2_hidden(X17,k4_xboole_0(X14,k2_xboole_0(X15,X16)))
      | ~ r2_hidden(X17,X16) ) ),
    inference(superposition,[],[f64,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f3391,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),o_0_0_xboole_0),k4_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),o_0_0_xboole_0),sK0)
    | spl4_7 ),
    inference(resolution,[],[f3381,f63])).

fof(f3381,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),o_0_0_xboole_0),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f3379])).

fof(f3379,plain,
    ( spl4_7
  <=> r2_hidden(sK3(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),o_0_0_xboole_0),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f3382,plain,
    ( ~ spl4_7
    | spl4_2 ),
    inference(avatar_split_clause,[],[f290,f284,f3379])).

fof(f284,plain,
    ( spl4_2
  <=> o_0_0_xboole_0 = k4_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f290,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),o_0_0_xboole_0),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f99,f286,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X1)
      | k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f286,plain,
    ( o_0_0_xboole_0 != k4_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f284])).

fof(f2781,plain,
    ( spl4_4
    | spl4_2 ),
    inference(avatar_split_clause,[],[f291,f284,f2778])).

fof(f291,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),o_0_0_xboole_0),k3_xboole_0(sK0,sK1))
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f99,f286,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f287,plain,
    ( ~ spl4_2
    | spl4_1 ),
    inference(avatar_split_clause,[],[f160,f68,f284])).

fof(f68,plain,
    ( spl4_1
  <=> k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f160,plain,
    ( o_0_0_xboole_0 != k4_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl4_1 ),
    inference(backward_demodulation,[],[f156,f144])).

fof(f144,plain,(
    ! [X6,X5] : o_0_0_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6))) ),
    inference(superposition,[],[f51,f82])).

fof(f82,plain,(
    ! [X0] : o_0_0_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(unit_resulting_resolution,[],[f66,f61])).

fof(f66,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f37,f58])).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f156,plain,
    ( k4_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)))
    | spl4_1 ),
    inference(backward_demodulation,[],[f135,f155])).

fof(f155,plain,(
    ! [X6,X4,X5] : k4_xboole_0(X4,k2_xboole_0(k3_xboole_0(X4,X5),X6)) = k4_xboole_0(X4,k2_xboole_0(X5,X6)) ),
    inference(forward_demodulation,[],[f140,f51])).

fof(f140,plain,(
    ! [X6,X4,X5] : k4_xboole_0(X4,k2_xboole_0(k3_xboole_0(X4,X5),X6)) = k4_xboole_0(k4_xboole_0(X4,X5),X6) ),
    inference(superposition,[],[f51,f41])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f135,plain,
    ( k4_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k2_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)))
    | spl4_1 ),
    inference(forward_demodulation,[],[f134,f38])).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f134,plain,
    ( k4_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))
    | spl4_1 ),
    inference(forward_demodulation,[],[f126,f51])).

fof(f126,plain,
    ( k4_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f70,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).

fof(f70,plain,
    ( k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f71,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f33,f68])).

fof(f33,plain,(
    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f22])).

fof(f22,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:45:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.52  % (28007)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.52  % (27991)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (27991)Refutation not found, incomplete strategy% (27991)------------------------------
% 0.22/0.52  % (27991)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (27991)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (27991)Memory used [KB]: 1663
% 0.22/0.52  % (27991)Time elapsed: 0.102 s
% 0.22/0.52  % (27991)------------------------------
% 0.22/0.52  % (27991)------------------------------
% 0.22/0.52  % (27990)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.52  % (28002)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.52  % (28003)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.54  % (27999)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.54  % (27992)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (28007)Refutation not found, incomplete strategy% (28007)------------------------------
% 0.22/0.54  % (28007)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.54  % (28002)Refutation not found, incomplete strategy% (28002)------------------------------
% 1.31/0.54  % (28002)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.54  % (28002)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.54  
% 1.31/0.54  % (28002)Memory used [KB]: 10618
% 1.31/0.54  % (28002)Time elapsed: 0.127 s
% 1.31/0.54  % (28002)------------------------------
% 1.31/0.54  % (28002)------------------------------
% 1.31/0.54  % (28005)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.31/0.54  % (28007)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.54  
% 1.31/0.54  % (28007)Memory used [KB]: 1663
% 1.31/0.54  % (28007)Time elapsed: 0.127 s
% 1.31/0.54  % (28007)------------------------------
% 1.31/0.54  % (28007)------------------------------
% 1.31/0.54  % (27993)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.31/0.54  % (28014)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.31/0.54  % (27994)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.31/0.54  % (28015)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.31/0.54  % (28014)Refutation not found, incomplete strategy% (28014)------------------------------
% 1.31/0.54  % (28014)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.54  % (28014)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.54  
% 1.31/0.54  % (28014)Memory used [KB]: 10618
% 1.31/0.54  % (28014)Time elapsed: 0.127 s
% 1.31/0.54  % (28014)------------------------------
% 1.31/0.54  % (28014)------------------------------
% 1.31/0.55  % (28013)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.31/0.55  % (27995)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.31/0.55  % (27997)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.31/0.55  % (28018)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.31/0.55  % (28018)Refutation not found, incomplete strategy% (28018)------------------------------
% 1.31/0.55  % (28018)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.55  % (28018)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.55  
% 1.31/0.55  % (28018)Memory used [KB]: 6140
% 1.31/0.55  % (28018)Time elapsed: 0.140 s
% 1.31/0.55  % (28018)------------------------------
% 1.31/0.55  % (28018)------------------------------
% 1.31/0.55  % (28006)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.31/0.55  % (28008)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.31/0.55  % (28006)Refutation not found, incomplete strategy% (28006)------------------------------
% 1.31/0.55  % (28006)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.55  % (28006)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.55  
% 1.31/0.55  % (28006)Memory used [KB]: 10618
% 1.31/0.55  % (28006)Time elapsed: 0.140 s
% 1.31/0.55  % (28006)------------------------------
% 1.31/0.55  % (28006)------------------------------
% 1.31/0.55  % (28008)Refutation not found, incomplete strategy% (28008)------------------------------
% 1.31/0.55  % (28008)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.55  % (28008)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.55  
% 1.31/0.55  % (28008)Memory used [KB]: 1663
% 1.31/0.55  % (28008)Time elapsed: 0.138 s
% 1.31/0.55  % (28008)------------------------------
% 1.31/0.55  % (28008)------------------------------
% 1.31/0.55  % (28012)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.31/0.55  % (27998)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.31/0.55  % (28019)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.31/0.56  % (28000)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.31/0.56  % (28001)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.31/0.56  % (28010)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.31/0.56  % (28020)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.31/0.56  % (28016)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.56/0.56  % (28009)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.56/0.56  % (28000)Refutation not found, incomplete strategy% (28000)------------------------------
% 1.56/0.56  % (28000)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.56  % (28000)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.56  
% 1.56/0.56  % (28000)Memory used [KB]: 10746
% 1.56/0.56  % (28000)Time elapsed: 0.149 s
% 1.56/0.56  % (28000)------------------------------
% 1.56/0.56  % (28000)------------------------------
% 1.56/0.56  % (28019)Refutation not found, incomplete strategy% (28019)------------------------------
% 1.56/0.56  % (28019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.56  % (28019)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.56  
% 1.56/0.56  % (28019)Memory used [KB]: 10746
% 1.56/0.56  % (28019)Time elapsed: 0.160 s
% 1.56/0.56  % (28019)------------------------------
% 1.56/0.56  % (28019)------------------------------
% 1.56/0.57  % (28016)Refutation not found, incomplete strategy% (28016)------------------------------
% 1.56/0.57  % (28016)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.57  % (28016)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.57  
% 1.56/0.57  % (28016)Memory used [KB]: 6140
% 1.56/0.57  % (28016)Time elapsed: 0.156 s
% 1.56/0.57  % (28016)------------------------------
% 1.56/0.57  % (28016)------------------------------
% 1.56/0.57  % (27996)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.56/0.58  % (28011)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.56/0.59  % (28004)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.56/0.61  % (28004)Refutation not found, incomplete strategy% (28004)------------------------------
% 1.56/0.61  % (28004)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.61  % (28004)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.61  
% 1.56/0.61  % (28004)Memory used [KB]: 1663
% 1.56/0.61  % (28004)Time elapsed: 0.173 s
% 1.56/0.61  % (28004)------------------------------
% 1.56/0.61  % (28004)------------------------------
% 2.17/0.69  % (28024)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.17/0.69  % (27990)Refutation not found, incomplete strategy% (27990)------------------------------
% 2.17/0.69  % (27990)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.69  % (27990)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.69  
% 2.17/0.69  % (27990)Memory used [KB]: 1663
% 2.17/0.69  % (27990)Time elapsed: 0.275 s
% 2.17/0.69  % (27990)------------------------------
% 2.17/0.69  % (27990)------------------------------
% 2.17/0.69  % (28026)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.17/0.70  % (28025)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.17/0.70  % (28031)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.17/0.70  % (28026)Refutation not found, incomplete strategy% (28026)------------------------------
% 2.17/0.70  % (28026)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.70  % (28026)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.70  
% 2.17/0.70  % (28026)Memory used [KB]: 6140
% 2.17/0.70  % (28026)Time elapsed: 0.105 s
% 2.17/0.70  % (28026)------------------------------
% 2.17/0.70  % (28026)------------------------------
% 2.17/0.70  % (28027)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.17/0.71  % (28030)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.17/0.72  % (28028)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.17/0.72  % (28005)Refutation not found, incomplete strategy% (28005)------------------------------
% 2.17/0.72  % (28005)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.73  % (27993)Refutation not found, incomplete strategy% (27993)------------------------------
% 2.17/0.73  % (27993)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.73  % (27993)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.73  
% 2.17/0.73  % (27993)Memory used [KB]: 6140
% 2.17/0.73  % (27993)Time elapsed: 0.315 s
% 2.17/0.73  % (27993)------------------------------
% 2.17/0.73  % (27993)------------------------------
% 2.17/0.73  % (28028)Refutation not found, incomplete strategy% (28028)------------------------------
% 2.17/0.73  % (28028)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.73  % (28028)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.73  
% 2.17/0.73  % (28028)Memory used [KB]: 10618
% 2.17/0.73  % (28028)Time elapsed: 0.147 s
% 2.17/0.73  % (28028)------------------------------
% 2.17/0.73  % (28028)------------------------------
% 2.63/0.74  % (28005)Termination reason: Refutation not found, incomplete strategy
% 2.63/0.74  
% 2.63/0.74  % (28005)Memory used [KB]: 6140
% 2.63/0.74  % (28005)Time elapsed: 0.273 s
% 2.63/0.74  % (28005)------------------------------
% 2.63/0.74  % (28005)------------------------------
% 2.63/0.74  % (28029)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.63/0.75  % (28033)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 2.63/0.75  % (28033)Refutation not found, incomplete strategy% (28033)------------------------------
% 2.63/0.75  % (28033)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.63/0.75  % (28033)Termination reason: Refutation not found, incomplete strategy
% 2.63/0.75  
% 2.63/0.75  % (28033)Memory used [KB]: 10618
% 2.63/0.75  % (28033)Time elapsed: 0.138 s
% 2.63/0.75  % (28033)------------------------------
% 2.63/0.75  % (28033)------------------------------
% 2.63/0.75  % (28032)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.83/0.80  % (28047)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 2.83/0.81  % (27992)Time limit reached!
% 2.83/0.81  % (27992)------------------------------
% 2.83/0.81  % (27992)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.83/0.81  % (27992)Termination reason: Time limit
% 2.83/0.82  % (27992)Termination phase: Saturation
% 2.83/0.82  
% 2.83/0.82  % (27992)Memory used [KB]: 6396
% 2.83/0.82  % (27992)Time elapsed: 0.400 s
% 2.83/0.82  % (27992)------------------------------
% 2.83/0.82  % (27992)------------------------------
% 3.13/0.84  % (28063)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 3.13/0.84  % (28064)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 3.13/0.85  % (28068)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 3.27/0.86  % (28069)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 3.27/0.87  % (28066)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 3.27/0.88  % (28065)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 3.27/0.88  % (28065)Refutation not found, incomplete strategy% (28065)------------------------------
% 3.27/0.88  % (28065)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.27/0.88  % (28065)Termination reason: Refutation not found, incomplete strategy
% 3.27/0.88  
% 3.27/0.88  % (28065)Memory used [KB]: 10618
% 3.27/0.88  % (28065)Time elapsed: 0.108 s
% 3.27/0.88  % (28065)------------------------------
% 3.27/0.88  % (28065)------------------------------
% 3.27/0.92  % (28010)Refutation found. Thanks to Tanya!
% 3.27/0.92  % SZS status Theorem for theBenchmark
% 3.27/0.92  % SZS output start Proof for theBenchmark
% 3.27/0.92  fof(f3404,plain,(
% 3.27/0.92    $false),
% 3.27/0.92    inference(avatar_sat_refutation,[],[f71,f287,f2781,f3382,f3403])).
% 3.27/0.92  fof(f3403,plain,(
% 3.27/0.92    ~spl4_4 | spl4_7),
% 3.27/0.92    inference(avatar_contradiction_clause,[],[f3402])).
% 3.27/0.92  fof(f3402,plain,(
% 3.27/0.92    $false | (~spl4_4 | spl4_7)),
% 3.27/0.92    inference(subsumption_resolution,[],[f3401,f2783])).
% 3.27/0.92  fof(f2783,plain,(
% 3.27/0.92    r2_hidden(sK3(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),o_0_0_xboole_0),sK0) | ~spl4_4),
% 3.27/0.92    inference(unit_resulting_resolution,[],[f2780,f236])).
% 3.27/0.92  fof(f236,plain,(
% 3.27/0.92    ( ! [X12,X13,X11] : (~r2_hidden(X13,k3_xboole_0(X11,X12)) | r2_hidden(X13,X11)) )),
% 3.27/0.92    inference(subsumption_resolution,[],[f228,f99])).
% 3.27/0.92  fof(f99,plain,(
% 3.27/0.92    ( ! [X0] : (~r2_hidden(X0,o_0_0_xboole_0)) )),
% 3.27/0.92    inference(condensation,[],[f96])).
% 3.27/0.92  fof(f96,plain,(
% 3.27/0.92    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X1,o_0_0_xboole_0)) )),
% 3.27/0.92    inference(superposition,[],[f64,f58])).
% 3.27/0.92  fof(f58,plain,(
% 3.27/0.92    ( ! [X0] : (k4_xboole_0(X0,o_0_0_xboole_0) = X0) )),
% 3.27/0.92    inference(definition_unfolding,[],[f35,f34])).
% 3.27/0.92  fof(f34,plain,(
% 3.27/0.92    k1_xboole_0 = o_0_0_xboole_0),
% 3.27/0.92    inference(cnf_transformation,[],[f3])).
% 3.27/0.92  fof(f3,axiom,(
% 3.27/0.92    k1_xboole_0 = o_0_0_xboole_0),
% 3.27/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).
% 3.27/0.92  fof(f35,plain,(
% 3.27/0.92    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.27/0.92    inference(cnf_transformation,[],[f12])).
% 3.27/0.92  fof(f12,axiom,(
% 3.27/0.92    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.27/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 3.27/0.92  fof(f64,plain,(
% 3.27/0.92    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 3.27/0.92    inference(equality_resolution,[],[f53])).
% 3.27/0.92  fof(f53,plain,(
% 3.27/0.92    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.27/0.92    inference(cnf_transformation,[],[f32])).
% 3.27/0.92  fof(f32,plain,(
% 3.27/0.92    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.27/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).
% 3.27/0.92  fof(f31,plain,(
% 3.27/0.92    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 3.27/0.92    introduced(choice_axiom,[])).
% 3.27/0.92  fof(f30,plain,(
% 3.27/0.92    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.27/0.92    inference(rectify,[],[f29])).
% 3.27/0.92  fof(f29,plain,(
% 3.27/0.92    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.27/0.92    inference(flattening,[],[f28])).
% 3.27/0.92  fof(f28,plain,(
% 3.27/0.92    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.27/0.92    inference(nnf_transformation,[],[f4])).
% 3.27/0.92  fof(f4,axiom,(
% 3.27/0.92    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.27/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 3.27/0.92  fof(f228,plain,(
% 3.27/0.92    ( ! [X12,X13,X11] : (r2_hidden(X13,o_0_0_xboole_0) | r2_hidden(X13,X11) | ~r2_hidden(X13,k3_xboole_0(X11,X12))) )),
% 3.27/0.92    inference(superposition,[],[f63,f80])).
% 3.27/0.92  fof(f80,plain,(
% 3.27/0.92    ( ! [X0,X1] : (o_0_0_xboole_0 = k4_xboole_0(k3_xboole_0(X0,X1),X0)) )),
% 3.27/0.92    inference(unit_resulting_resolution,[],[f36,f61])).
% 3.27/0.92  fof(f61,plain,(
% 3.27/0.92    ( ! [X0,X1] : (~r1_tarski(X0,X1) | o_0_0_xboole_0 = k4_xboole_0(X0,X1)) )),
% 3.27/0.92    inference(definition_unfolding,[],[f50,f34])).
% 3.27/0.92  fof(f50,plain,(
% 3.27/0.92    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 3.27/0.92    inference(cnf_transformation,[],[f27])).
% 3.27/0.92  fof(f27,plain,(
% 3.27/0.92    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 3.27/0.92    inference(nnf_transformation,[],[f7])).
% 3.27/0.92  fof(f7,axiom,(
% 3.27/0.92    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 3.27/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 3.27/0.92  fof(f36,plain,(
% 3.27/0.92    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.27/0.92    inference(cnf_transformation,[],[f8])).
% 3.27/0.92  fof(f8,axiom,(
% 3.27/0.92    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.27/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 3.27/0.92  fof(f63,plain,(
% 3.27/0.92    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 3.27/0.92    inference(equality_resolution,[],[f54])).
% 3.27/0.92  fof(f54,plain,(
% 3.27/0.92    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 3.27/0.92    inference(cnf_transformation,[],[f32])).
% 3.27/0.92  fof(f2780,plain,(
% 3.27/0.92    r2_hidden(sK3(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),o_0_0_xboole_0),k3_xboole_0(sK0,sK1)) | ~spl4_4),
% 3.27/0.92    inference(avatar_component_clause,[],[f2778])).
% 3.27/0.92  fof(f2778,plain,(
% 3.27/0.92    spl4_4 <=> r2_hidden(sK3(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),o_0_0_xboole_0),k3_xboole_0(sK0,sK1))),
% 3.27/0.92    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 3.27/0.92  fof(f3401,plain,(
% 3.27/0.92    ~r2_hidden(sK3(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),o_0_0_xboole_0),sK0) | (~spl4_4 | spl4_7)),
% 3.27/0.92    inference(subsumption_resolution,[],[f3391,f3204])).
% 3.27/0.92  fof(f3204,plain,(
% 3.27/0.92    ( ! [X0] : (~r2_hidden(sK3(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),o_0_0_xboole_0),k4_xboole_0(X0,sK1))) ) | ~spl4_4),
% 3.27/0.92    inference(unit_resulting_resolution,[],[f2780,f556])).
% 3.27/0.92  fof(f556,plain,(
% 3.27/0.92    ( ! [X14,X12,X15,X13] : (~r2_hidden(X14,k4_xboole_0(X15,X12)) | ~r2_hidden(X14,k3_xboole_0(X13,X12))) )),
% 3.27/0.92    inference(superposition,[],[f151,f74])).
% 3.27/0.92  fof(f74,plain,(
% 3.27/0.92    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0) )),
% 3.27/0.92    inference(superposition,[],[f40,f39])).
% 3.27/0.92  fof(f39,plain,(
% 3.27/0.92    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.27/0.92    inference(cnf_transformation,[],[f2])).
% 3.27/0.92  fof(f2,axiom,(
% 3.27/0.92    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.27/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 3.27/0.92  fof(f40,plain,(
% 3.27/0.92    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 3.27/0.92    inference(cnf_transformation,[],[f9])).
% 3.27/0.92  fof(f9,axiom,(
% 3.27/0.92    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 3.27/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 3.27/0.92  fof(f151,plain,(
% 3.27/0.92    ( ! [X14,X17,X15,X16] : (~r2_hidden(X17,k4_xboole_0(X14,k2_xboole_0(X15,X16))) | ~r2_hidden(X17,X16)) )),
% 3.27/0.92    inference(superposition,[],[f64,f51])).
% 3.27/0.92  fof(f51,plain,(
% 3.27/0.92    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 3.27/0.92    inference(cnf_transformation,[],[f14])).
% 3.27/0.92  fof(f14,axiom,(
% 3.27/0.92    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 3.27/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 3.27/0.92  fof(f3391,plain,(
% 3.27/0.92    r2_hidden(sK3(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),o_0_0_xboole_0),k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK3(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),o_0_0_xboole_0),sK0) | spl4_7),
% 3.27/0.92    inference(resolution,[],[f3381,f63])).
% 3.27/0.92  fof(f3381,plain,(
% 3.27/0.92    ~r2_hidden(sK3(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),o_0_0_xboole_0),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl4_7),
% 3.27/0.92    inference(avatar_component_clause,[],[f3379])).
% 3.27/0.92  fof(f3379,plain,(
% 3.27/0.92    spl4_7 <=> r2_hidden(sK3(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),o_0_0_xboole_0),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 3.27/0.92    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 3.27/0.92  fof(f3382,plain,(
% 3.27/0.92    ~spl4_7 | spl4_2),
% 3.27/0.92    inference(avatar_split_clause,[],[f290,f284,f3379])).
% 3.27/0.92  fof(f284,plain,(
% 3.27/0.92    spl4_2 <=> o_0_0_xboole_0 = k4_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 3.27/0.92    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 3.27/0.92  fof(f290,plain,(
% 3.27/0.92    ~r2_hidden(sK3(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),o_0_0_xboole_0),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl4_2),
% 3.27/0.92    inference(unit_resulting_resolution,[],[f99,f286,f56])).
% 3.27/0.92  fof(f56,plain,(
% 3.27/0.92    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X1) | k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 3.27/0.92    inference(cnf_transformation,[],[f32])).
% 3.27/0.92  fof(f286,plain,(
% 3.27/0.92    o_0_0_xboole_0 != k4_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl4_2),
% 3.27/0.92    inference(avatar_component_clause,[],[f284])).
% 3.27/0.92  fof(f2781,plain,(
% 3.27/0.92    spl4_4 | spl4_2),
% 3.27/0.92    inference(avatar_split_clause,[],[f291,f284,f2778])).
% 3.27/0.92  fof(f291,plain,(
% 3.27/0.92    r2_hidden(sK3(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),o_0_0_xboole_0),k3_xboole_0(sK0,sK1)) | spl4_2),
% 3.27/0.92    inference(unit_resulting_resolution,[],[f99,f286,f55])).
% 3.27/0.92  fof(f55,plain,(
% 3.27/0.92    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 3.27/0.92    inference(cnf_transformation,[],[f32])).
% 3.27/0.92  fof(f287,plain,(
% 3.27/0.92    ~spl4_2 | spl4_1),
% 3.27/0.92    inference(avatar_split_clause,[],[f160,f68,f284])).
% 3.27/0.92  fof(f68,plain,(
% 3.27/0.92    spl4_1 <=> k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 3.27/0.92    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 3.27/0.92  fof(f160,plain,(
% 3.27/0.92    o_0_0_xboole_0 != k4_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl4_1),
% 3.27/0.92    inference(backward_demodulation,[],[f156,f144])).
% 3.27/0.92  fof(f144,plain,(
% 3.27/0.92    ( ! [X6,X5] : (o_0_0_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6)))) )),
% 3.27/0.92    inference(superposition,[],[f51,f82])).
% 3.27/0.92  fof(f82,plain,(
% 3.27/0.92    ( ! [X0] : (o_0_0_xboole_0 = k4_xboole_0(X0,X0)) )),
% 3.27/0.92    inference(unit_resulting_resolution,[],[f66,f61])).
% 3.27/0.92  fof(f66,plain,(
% 3.27/0.92    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 3.27/0.92    inference(superposition,[],[f37,f58])).
% 3.27/0.92  fof(f37,plain,(
% 3.27/0.92    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.27/0.92    inference(cnf_transformation,[],[f11])).
% 3.27/0.92  fof(f11,axiom,(
% 3.27/0.92    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.27/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 3.27/0.92  fof(f156,plain,(
% 3.27/0.92    k4_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))) | spl4_1),
% 3.27/0.92    inference(backward_demodulation,[],[f135,f155])).
% 3.27/0.92  fof(f155,plain,(
% 3.27/0.92    ( ! [X6,X4,X5] : (k4_xboole_0(X4,k2_xboole_0(k3_xboole_0(X4,X5),X6)) = k4_xboole_0(X4,k2_xboole_0(X5,X6))) )),
% 3.27/0.92    inference(forward_demodulation,[],[f140,f51])).
% 3.27/0.92  fof(f140,plain,(
% 3.27/0.92    ( ! [X6,X4,X5] : (k4_xboole_0(X4,k2_xboole_0(k3_xboole_0(X4,X5),X6)) = k4_xboole_0(k4_xboole_0(X4,X5),X6)) )),
% 3.27/0.92    inference(superposition,[],[f51,f41])).
% 3.27/0.92  fof(f41,plain,(
% 3.27/0.92    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.27/0.92    inference(cnf_transformation,[],[f15])).
% 3.27/0.92  fof(f15,axiom,(
% 3.27/0.92    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.27/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 3.27/0.92  fof(f135,plain,(
% 3.27/0.92    k4_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k2_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))) | spl4_1),
% 3.27/0.92    inference(forward_demodulation,[],[f134,f38])).
% 3.27/0.92  fof(f38,plain,(
% 3.27/0.92    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.27/0.92    inference(cnf_transformation,[],[f1])).
% 3.27/0.92  fof(f1,axiom,(
% 3.27/0.92    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.27/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 3.27/0.92  fof(f134,plain,(
% 3.27/0.92    k4_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))) | spl4_1),
% 3.27/0.92    inference(forward_demodulation,[],[f126,f51])).
% 3.27/0.92  fof(f126,plain,(
% 3.27/0.92    k4_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | spl4_1),
% 3.27/0.92    inference(unit_resulting_resolution,[],[f70,f46])).
% 3.27/0.92  fof(f46,plain,(
% 3.27/0.92    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) | X0 = X1) )),
% 3.27/0.92    inference(cnf_transformation,[],[f21])).
% 3.27/0.92  fof(f21,plain,(
% 3.27/0.92    ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0))),
% 3.27/0.92    inference(ennf_transformation,[],[f10])).
% 3.27/0.92  fof(f10,axiom,(
% 3.27/0.92    ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 3.27/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).
% 3.27/0.92  fof(f70,plain,(
% 3.27/0.92    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | spl4_1),
% 3.27/0.92    inference(avatar_component_clause,[],[f68])).
% 3.27/0.92  fof(f71,plain,(
% 3.27/0.92    ~spl4_1),
% 3.27/0.92    inference(avatar_split_clause,[],[f33,f68])).
% 3.27/0.92  fof(f33,plain,(
% 3.27/0.92    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 3.27/0.92    inference(cnf_transformation,[],[f23])).
% 3.27/0.92  fof(f23,plain,(
% 3.27/0.92    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 3.27/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f22])).
% 3.27/0.92  fof(f22,plain,(
% 3.27/0.92    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 3.27/0.92    introduced(choice_axiom,[])).
% 3.27/0.92  fof(f19,plain,(
% 3.27/0.92    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.27/0.92    inference(ennf_transformation,[],[f17])).
% 3.27/0.92  fof(f17,negated_conjecture,(
% 3.27/0.92    ~! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.27/0.92    inference(negated_conjecture,[],[f16])).
% 3.27/0.92  fof(f16,conjecture,(
% 3.27/0.92    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.27/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 3.27/0.92  % SZS output end Proof for theBenchmark
% 3.27/0.92  % (28010)------------------------------
% 3.27/0.92  % (28010)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.27/0.92  % (28010)Termination reason: Refutation
% 3.27/0.92  
% 3.27/0.92  % (28010)Memory used [KB]: 13432
% 3.27/0.92  % (28010)Time elapsed: 0.514 s
% 3.27/0.92  % (28010)------------------------------
% 3.27/0.92  % (28010)------------------------------
% 3.27/0.92  % (27989)Success in time 0.565 s
%------------------------------------------------------------------------------
