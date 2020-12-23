%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:24 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 149 expanded)
%              Number of leaves         :   16 (  55 expanded)
%              Depth                    :   11
%              Number of atoms          :  198 ( 332 expanded)
%              Number of equality atoms :  119 ( 225 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f349,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f65,f112,f208,f246,f329,f348])).

fof(f348,plain,
    ( spl5_2
    | ~ spl5_10 ),
    inference(avatar_contradiction_clause,[],[f347])).

fof(f347,plain,
    ( $false
    | spl5_2
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f59,f315])).

fof(f315,plain,
    ( sK3 = k2_mcart_1(sK0)
    | ~ spl5_10 ),
    inference(superposition,[],[f25,f207])).

fof(f207,plain,
    ( sK0 = k4_tarski(sK1,sK3)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl5_10
  <=> sK0 = k4_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f25,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f59,plain,
    ( sK3 != k2_mcart_1(sK0)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl5_2
  <=> sK3 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f329,plain,
    ( spl5_1
    | ~ spl5_10 ),
    inference(avatar_contradiction_clause,[],[f328])).

fof(f328,plain,
    ( $false
    | spl5_1
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f314,f55])).

fof(f55,plain,
    ( sK1 != k1_mcart_1(sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl5_1
  <=> sK1 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f314,plain,
    ( sK1 = k1_mcart_1(sK0)
    | ~ spl5_10 ),
    inference(superposition,[],[f24,f207])).

fof(f24,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f246,plain,(
    ~ spl5_9 ),
    inference(avatar_contradiction_clause,[],[f245])).

fof(f245,plain,
    ( $false
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f244,f220])).

fof(f220,plain,
    ( sK2 = k1_mcart_1(sK0)
    | ~ spl5_9 ),
    inference(superposition,[],[f24,f203])).

fof(f203,plain,
    ( sK0 = k4_tarski(sK2,sK3)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl5_9
  <=> sK0 = k4_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f244,plain,
    ( sK2 != k1_mcart_1(sK0)
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f20,f221])).

fof(f221,plain,
    ( sK3 = k2_mcart_1(sK0)
    | ~ spl5_9 ),
    inference(superposition,[],[f25,f203])).

fof(f20,plain,
    ( sK3 != k2_mcart_1(sK0)
    | sK2 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ( sK3 != k2_mcart_1(sK0)
      | ( sK2 != k1_mcart_1(sK0)
        & sK1 != k1_mcart_1(sK0) ) )
    & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k1_tarski(sK3))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( k2_mcart_1(X0) != X3
          | ( k1_mcart_1(X0) != X2
            & k1_mcart_1(X0) != X1 ) )
        & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))) )
   => ( ( sK3 != k2_mcart_1(sK0)
        | ( sK2 != k1_mcart_1(sK0)
          & sK1 != k1_mcart_1(sK0) ) )
      & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k1_tarski(sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ( k2_mcart_1(X0) != X3
        | ( k1_mcart_1(X0) != X2
          & k1_mcart_1(X0) != X1 ) )
      & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)))
       => ( k2_mcart_1(X0) = X3
          & ( k1_mcart_1(X0) = X2
            | k1_mcart_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)))
     => ( k2_mcart_1(X0) = X3
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_mcart_1)).

fof(f208,plain,
    ( spl5_9
    | spl5_10
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f162,f109,f205,f201])).

fof(f109,plain,
    ( spl5_6
  <=> r2_hidden(sK0,k2_enumset1(k4_tarski(sK1,sK3),k4_tarski(sK1,sK3),k4_tarski(sK2,sK3),k4_tarski(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f162,plain,
    ( sK0 = k4_tarski(sK1,sK3)
    | sK0 = k4_tarski(sK2,sK3)
    | ~ spl5_6 ),
    inference(resolution,[],[f120,f111])).

fof(f111,plain,
    ( r2_hidden(sK0,k2_enumset1(k4_tarski(sK1,sK3),k4_tarski(sK1,sK3),k4_tarski(sK2,sK3),k4_tarski(sK2,sK3)))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f109])).

fof(f120,plain,(
    ! [X14,X12,X15,X13] :
      ( ~ r2_hidden(X15,k2_enumset1(k4_tarski(X12,X13),k4_tarski(X12,X13),k4_tarski(X14,X13),k4_tarski(X14,X13)))
      | k4_tarski(X12,X13) = X15
      | k4_tarski(X14,X13) = X15 ) ),
    inference(superposition,[],[f51,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] : k3_relat_1(k2_enumset1(k4_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)),k4_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)),k4_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)),k4_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)))) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2),k4_tarski(X1,X2)) ),
    inference(backward_demodulation,[],[f38,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] : k2_enumset1(k4_tarski(X1,X0),k4_tarski(X1,X0),k4_tarski(X2,X0),k4_tarski(X2,X0)) = k2_zfmisc_1(k3_relat_1(k2_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2))),k2_enumset1(X0,X0,X0,X0)) ),
    inference(superposition,[],[f46,f37])).

fof(f37,plain,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k3_relat_1(k2_enumset1(k4_tarski(X0,X0),k4_tarski(X0,X0),k4_tarski(X0,X0),k4_tarski(X0,X0))) ),
    inference(definition_unfolding,[],[f21,f22,f22])).

fof(f22,plain,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_enumset1)).

fof(f21,plain,(
    ! [X0] : k1_tarski(X0) = k3_relat_1(k1_tarski(k4_tarski(X0,X0))) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_tarski(X0) = k3_relat_1(k1_tarski(k4_tarski(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t208_relat_1)).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k3_relat_1(k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1))),k3_relat_1(k2_enumset1(k4_tarski(X2,X3),k4_tarski(X2,X3),k4_tarski(X2,X3),k4_tarski(X2,X3)))) ),
    inference(definition_unfolding,[],[f34,f35,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_relat_1(k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f23,f22])).

fof(f23,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_relat_1)).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k3_relat_1(k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1))),k2_enumset1(X2,X2,X2,X2)) = k3_relat_1(k2_enumset1(k4_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)),k4_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)),k4_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)),k4_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)))) ),
    inference(definition_unfolding,[],[f27,f35,f22,f35])).

fof(f27,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f51,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_relat_1(k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1))))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k3_relat_1(k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f28,f35])).

fof(f28,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK4(X0,X1,X2) != X1
              & sK4(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( sK4(X0,X1,X2) = X1
            | sK4(X0,X1,X2) = X0
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f16])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK4(X0,X1,X2) != X1
            & sK4(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( sK4(X0,X1,X2) = X1
          | sK4(X0,X1,X2) = X0
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f112,plain,
    ( spl5_6
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f102,f62,f109])).

fof(f62,plain,
    ( spl5_3
  <=> r2_hidden(sK0,k2_zfmisc_1(k3_relat_1(k2_enumset1(k4_tarski(sK1,sK2),k4_tarski(sK1,sK2),k4_tarski(sK1,sK2),k4_tarski(sK1,sK2))),k2_enumset1(sK3,sK3,sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f102,plain,
    ( r2_hidden(sK0,k2_enumset1(k4_tarski(sK1,sK3),k4_tarski(sK1,sK3),k4_tarski(sK2,sK3),k4_tarski(sK2,sK3)))
    | ~ spl5_3 ),
    inference(backward_demodulation,[],[f64,f99])).

fof(f64,plain,
    ( r2_hidden(sK0,k2_zfmisc_1(k3_relat_1(k2_enumset1(k4_tarski(sK1,sK2),k4_tarski(sK1,sK2),k4_tarski(sK1,sK2),k4_tarski(sK1,sK2))),k2_enumset1(sK3,sK3,sK3,sK3)))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f65,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f36,f62])).

fof(f36,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k3_relat_1(k2_enumset1(k4_tarski(sK1,sK2),k4_tarski(sK1,sK2),k4_tarski(sK1,sK2),k4_tarski(sK1,sK2))),k2_enumset1(sK3,sK3,sK3,sK3))) ),
    inference(definition_unfolding,[],[f18,f35,f22])).

fof(f18,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f12])).

fof(f60,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f19,f57,f53])).

fof(f19,plain,
    ( sK3 != k2_mcart_1(sK0)
    | sK1 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 21:13:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.49  % (21011)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.49  % (21019)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.50  % (21019)Refutation not found, incomplete strategy% (21019)------------------------------
% 0.22/0.50  % (21019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (21003)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.50  % (21019)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (21019)Memory used [KB]: 10746
% 0.22/0.50  % (21019)Time elapsed: 0.086 s
% 0.22/0.50  % (21019)------------------------------
% 0.22/0.50  % (21019)------------------------------
% 0.22/0.51  % (21011)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f349,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f60,f65,f112,f208,f246,f329,f348])).
% 0.22/0.51  fof(f348,plain,(
% 0.22/0.51    spl5_2 | ~spl5_10),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f347])).
% 0.22/0.51  fof(f347,plain,(
% 0.22/0.51    $false | (spl5_2 | ~spl5_10)),
% 0.22/0.51    inference(subsumption_resolution,[],[f59,f315])).
% 0.22/0.51  fof(f315,plain,(
% 0.22/0.51    sK3 = k2_mcart_1(sK0) | ~spl5_10),
% 0.22/0.51    inference(superposition,[],[f25,f207])).
% 0.22/0.51  fof(f207,plain,(
% 0.22/0.51    sK0 = k4_tarski(sK1,sK3) | ~spl5_10),
% 0.22/0.51    inference(avatar_component_clause,[],[f205])).
% 0.22/0.51  fof(f205,plain,(
% 0.22/0.51    spl5_10 <=> sK0 = k4_tarski(sK1,sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    sK3 != k2_mcart_1(sK0) | spl5_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f57])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    spl5_2 <=> sK3 = k2_mcart_1(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.51  fof(f329,plain,(
% 0.22/0.51    spl5_1 | ~spl5_10),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f328])).
% 0.22/0.51  fof(f328,plain,(
% 0.22/0.51    $false | (spl5_1 | ~spl5_10)),
% 0.22/0.51    inference(subsumption_resolution,[],[f314,f55])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    sK1 != k1_mcart_1(sK0) | spl5_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f53])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    spl5_1 <=> sK1 = k1_mcart_1(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.51  fof(f314,plain,(
% 0.22/0.51    sK1 = k1_mcart_1(sK0) | ~spl5_10),
% 0.22/0.51    inference(superposition,[],[f24,f207])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f7])).
% 0.22/0.51  fof(f246,plain,(
% 0.22/0.51    ~spl5_9),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f245])).
% 0.22/0.51  fof(f245,plain,(
% 0.22/0.51    $false | ~spl5_9),
% 0.22/0.51    inference(subsumption_resolution,[],[f244,f220])).
% 0.22/0.51  fof(f220,plain,(
% 0.22/0.51    sK2 = k1_mcart_1(sK0) | ~spl5_9),
% 0.22/0.51    inference(superposition,[],[f24,f203])).
% 0.22/0.51  fof(f203,plain,(
% 0.22/0.51    sK0 = k4_tarski(sK2,sK3) | ~spl5_9),
% 0.22/0.51    inference(avatar_component_clause,[],[f201])).
% 0.22/0.51  fof(f201,plain,(
% 0.22/0.51    spl5_9 <=> sK0 = k4_tarski(sK2,sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.22/0.51  fof(f244,plain,(
% 0.22/0.51    sK2 != k1_mcart_1(sK0) | ~spl5_9),
% 0.22/0.51    inference(subsumption_resolution,[],[f20,f221])).
% 0.22/0.51  fof(f221,plain,(
% 0.22/0.51    sK3 = k2_mcart_1(sK0) | ~spl5_9),
% 0.22/0.51    inference(superposition,[],[f25,f203])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    sK3 != k2_mcart_1(sK0) | sK2 != k1_mcart_1(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    (sK3 != k2_mcart_1(sK0) | (sK2 != k1_mcart_1(sK0) & sK1 != k1_mcart_1(sK0))) & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k1_tarski(sK3)))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ? [X0,X1,X2,X3] : ((k2_mcart_1(X0) != X3 | (k1_mcart_1(X0) != X2 & k1_mcart_1(X0) != X1)) & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)))) => ((sK3 != k2_mcart_1(sK0) | (sK2 != k1_mcart_1(sK0) & sK1 != k1_mcart_1(sK0))) & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k1_tarski(sK3))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ? [X0,X1,X2,X3] : ((k2_mcart_1(X0) != X3 | (k1_mcart_1(X0) != X2 & k1_mcart_1(X0) != X1)) & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))) => (k2_mcart_1(X0) = X3 & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 0.22/0.51    inference(negated_conjecture,[],[f8])).
% 0.22/0.51  fof(f8,conjecture,(
% 0.22/0.51    ! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))) => (k2_mcart_1(X0) = X3 & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_mcart_1)).
% 0.22/0.51  fof(f208,plain,(
% 0.22/0.51    spl5_9 | spl5_10 | ~spl5_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f162,f109,f205,f201])).
% 0.22/0.51  fof(f109,plain,(
% 0.22/0.51    spl5_6 <=> r2_hidden(sK0,k2_enumset1(k4_tarski(sK1,sK3),k4_tarski(sK1,sK3),k4_tarski(sK2,sK3),k4_tarski(sK2,sK3)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.51  fof(f162,plain,(
% 0.22/0.51    sK0 = k4_tarski(sK1,sK3) | sK0 = k4_tarski(sK2,sK3) | ~spl5_6),
% 0.22/0.51    inference(resolution,[],[f120,f111])).
% 0.22/0.51  fof(f111,plain,(
% 0.22/0.51    r2_hidden(sK0,k2_enumset1(k4_tarski(sK1,sK3),k4_tarski(sK1,sK3),k4_tarski(sK2,sK3),k4_tarski(sK2,sK3))) | ~spl5_6),
% 0.22/0.51    inference(avatar_component_clause,[],[f109])).
% 0.22/0.51  fof(f120,plain,(
% 0.22/0.51    ( ! [X14,X12,X15,X13] : (~r2_hidden(X15,k2_enumset1(k4_tarski(X12,X13),k4_tarski(X12,X13),k4_tarski(X14,X13),k4_tarski(X14,X13))) | k4_tarski(X12,X13) = X15 | k4_tarski(X14,X13) = X15) )),
% 0.22/0.51    inference(superposition,[],[f51,f101])).
% 0.22/0.51  fof(f101,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k3_relat_1(k2_enumset1(k4_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)),k4_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)),k4_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)),k4_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)))) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2),k4_tarski(X1,X2))) )),
% 0.22/0.51    inference(backward_demodulation,[],[f38,f99])).
% 0.22/0.51  fof(f99,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k2_enumset1(k4_tarski(X1,X0),k4_tarski(X1,X0),k4_tarski(X2,X0),k4_tarski(X2,X0)) = k2_zfmisc_1(k3_relat_1(k2_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2))),k2_enumset1(X0,X0,X0,X0))) )),
% 0.22/0.51    inference(superposition,[],[f46,f37])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) = k3_relat_1(k2_enumset1(k4_tarski(X0,X0),k4_tarski(X0,X0),k4_tarski(X0,X0),k4_tarski(X0,X0)))) )),
% 0.22/0.51    inference(definition_unfolding,[],[f21,f22,f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_enumset1)).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ( ! [X0] : (k1_tarski(X0) = k3_relat_1(k1_tarski(k4_tarski(X0,X0)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0] : k1_tarski(X0) = k3_relat_1(k1_tarski(k4_tarski(X0,X0)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t208_relat_1)).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k3_relat_1(k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1))),k3_relat_1(k2_enumset1(k4_tarski(X2,X3),k4_tarski(X2,X3),k4_tarski(X2,X3),k4_tarski(X2,X3))))) )),
% 0.22/0.51    inference(definition_unfolding,[],[f34,f35,f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_relat_1(k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1)))) )),
% 0.22/0.51    inference(definition_unfolding,[],[f23,f22])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_relat_1(k1_tarski(k4_tarski(X0,X1)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0,X1] : k2_tarski(X0,X1) = k3_relat_1(k1_tarski(k4_tarski(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_relat_1)).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k2_zfmisc_1(k3_relat_1(k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1))),k2_enumset1(X2,X2,X2,X2)) = k3_relat_1(k2_enumset1(k4_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)),k4_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)),k4_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)),k4_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))))) )),
% 0.22/0.51    inference(definition_unfolding,[],[f27,f35,f22,f35])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_relat_1(k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1)))) | X0 = X4 | X1 = X4) )),
% 0.22/0.52    inference(equality_resolution,[],[f45])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k3_relat_1(k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1))) != X2) )),
% 0.22/0.52    inference(definition_unfolding,[],[f28,f35])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.22/0.52    inference(rectify,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.22/0.52    inference(flattening,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.22/0.52    inference(nnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 0.22/0.52  fof(f112,plain,(
% 0.22/0.52    spl5_6 | ~spl5_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f102,f62,f109])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    spl5_3 <=> r2_hidden(sK0,k2_zfmisc_1(k3_relat_1(k2_enumset1(k4_tarski(sK1,sK2),k4_tarski(sK1,sK2),k4_tarski(sK1,sK2),k4_tarski(sK1,sK2))),k2_enumset1(sK3,sK3,sK3,sK3)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.52  fof(f102,plain,(
% 0.22/0.52    r2_hidden(sK0,k2_enumset1(k4_tarski(sK1,sK3),k4_tarski(sK1,sK3),k4_tarski(sK2,sK3),k4_tarski(sK2,sK3))) | ~spl5_3),
% 0.22/0.52    inference(backward_demodulation,[],[f64,f99])).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    r2_hidden(sK0,k2_zfmisc_1(k3_relat_1(k2_enumset1(k4_tarski(sK1,sK2),k4_tarski(sK1,sK2),k4_tarski(sK1,sK2),k4_tarski(sK1,sK2))),k2_enumset1(sK3,sK3,sK3,sK3))) | ~spl5_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f62])).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    spl5_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f36,f62])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    r2_hidden(sK0,k2_zfmisc_1(k3_relat_1(k2_enumset1(k4_tarski(sK1,sK2),k4_tarski(sK1,sK2),k4_tarski(sK1,sK2),k4_tarski(sK1,sK2))),k2_enumset1(sK3,sK3,sK3,sK3)))),
% 0.22/0.52    inference(definition_unfolding,[],[f18,f35,f22])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k1_tarski(sK3)))),
% 0.22/0.52    inference(cnf_transformation,[],[f12])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    ~spl5_1 | ~spl5_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f19,f57,f53])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    sK3 != k2_mcart_1(sK0) | sK1 != k1_mcart_1(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f12])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (21011)------------------------------
% 0.22/0.52  % (21011)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (21011)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (21011)Memory used [KB]: 11129
% 0.22/0.52  % (21011)Time elapsed: 0.102 s
% 0.22/0.52  % (21011)------------------------------
% 0.22/0.52  % (21011)------------------------------
% 0.22/0.52  % (21002)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.52  % (21002)Refutation not found, incomplete strategy% (21002)------------------------------
% 0.22/0.52  % (21002)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (21002)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (21002)Memory used [KB]: 6268
% 0.22/0.52  % (21002)Time elapsed: 0.107 s
% 0.22/0.52  % (21002)------------------------------
% 0.22/0.52  % (21002)------------------------------
% 0.22/0.52  % (20990)Success in time 0.159 s
%------------------------------------------------------------------------------
