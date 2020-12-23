%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0235+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:35 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   53 (  96 expanded)
%              Number of leaves         :   10 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :  212 ( 499 expanded)
%              Number of equality atoms :  103 ( 253 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f185,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f85,f169,f184])).

fof(f184,plain,
    ( spl3_1
    | spl3_3
    | spl3_5 ),
    inference(avatar_contradiction_clause,[],[f183])).

fof(f183,plain,
    ( $false
    | spl3_1
    | spl3_3
    | spl3_5 ),
    inference(subsumption_resolution,[],[f170,f177])).

fof(f177,plain,
    ( r1_tarski(sK2(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0))),k1_tarski(sK0))
    | spl3_1
    | spl3_3
    | spl3_5 ),
    inference(unit_resulting_resolution,[],[f48,f84,f168,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK2(X0,X1,k1_zfmisc_1(X2)),X2)
      | sK2(X0,X1,k1_zfmisc_1(X2)) = X0
      | k2_tarski(X0,X1) = k1_zfmisc_1(X2)
      | sK2(X0,X1,k1_zfmisc_1(X2)) = X1 ) ),
    inference(resolution,[],[f31,f35])).

fof(f35,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK1(X0,X1),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r1_tarski(sK1(X0,X1),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f10,f11])).

fof(f11,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK1(X0,X1),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( r1_tarski(sK1(X0,X1),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X2)
      | sK2(X0,X1,X2) = X1
      | sK2(X0,X1,X2) = X0
      | k2_tarski(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK2(X0,X1,X2) != X1
              & sK2(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( sK2(X0,X1,X2) = X1
            | sK2(X0,X1,X2) = X0
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f18])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK2(X0,X1,X2) != X1
            & sK2(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( sK2(X0,X1,X2) = X1
          | sK2(X0,X1,X2) = X0
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f168,plain,
    ( k1_tarski(sK0) != sK2(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0)))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl3_5
  <=> k1_tarski(sK0) = sK2(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f84,plain,
    ( k1_xboole_0 != sK2(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl3_3
  <=> k1_xboole_0 = sK2(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f48,plain,
    ( k1_zfmisc_1(k1_tarski(sK0)) != k2_tarski(k1_xboole_0,k1_tarski(sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl3_1
  <=> k1_zfmisc_1(k1_tarski(sK0)) = k2_tarski(k1_xboole_0,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f170,plain,
    ( ~ r1_tarski(sK2(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0))),k1_tarski(sK0))
    | spl3_3
    | spl3_5 ),
    inference(unit_resulting_resolution,[],[f84,f168,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f169,plain,
    ( ~ spl3_5
    | spl3_1 ),
    inference(avatar_split_clause,[],[f74,f46,f166])).

fof(f74,plain,
    ( k1_tarski(sK0) != sK2(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0)))
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f48,f51,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( sK2(X0,X1,X2) != X1
      | k2_tarski(X0,X1) = X2
      | ~ r2_hidden(X1,X2) ) ),
    inference(inner_rewriting,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK2(X0,X1,X2) != X1
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f51,plain,(
    ! [X0] : r2_hidden(k1_tarski(X0),k1_zfmisc_1(k1_tarski(X0))) ),
    inference(unit_resulting_resolution,[],[f36,f34])).

fof(f34,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X1] : r1_tarski(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f85,plain,
    ( ~ spl3_3
    | spl3_1 ),
    inference(avatar_split_clause,[],[f70,f46,f82])).

fof(f70,plain,
    ( k1_xboole_0 != sK2(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0)))
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f50,f48,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( sK2(X0,X1,X2) != X0
      | k2_tarski(X0,X1) = X2
      | ~ r2_hidden(X0,X2) ) ),
    inference(inner_rewriting,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK2(X0,X1,X2) != X0
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f50,plain,(
    ! [X0] : r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_tarski(X0))) ),
    inference(unit_resulting_resolution,[],[f37,f34])).

fof(f37,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k1_tarski(X1)) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f49,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f20,f46])).

fof(f20,plain,(
    k1_zfmisc_1(k1_tarski(sK0)) != k2_tarski(k1_xboole_0,k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    k1_zfmisc_1(k1_tarski(sK0)) != k2_tarski(k1_xboole_0,k1_tarski(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f7])).

fof(f7,plain,
    ( ? [X0] : k1_zfmisc_1(k1_tarski(X0)) != k2_tarski(k1_xboole_0,k1_tarski(X0))
   => k1_zfmisc_1(k1_tarski(sK0)) != k2_tarski(k1_xboole_0,k1_tarski(sK0)) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] : k1_zfmisc_1(k1_tarski(X0)) != k2_tarski(k1_xboole_0,k1_tarski(X0)) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] : k1_zfmisc_1(k1_tarski(X0)) = k2_tarski(k1_xboole_0,k1_tarski(X0)) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] : k1_zfmisc_1(k1_tarski(X0)) = k2_tarski(k1_xboole_0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_zfmisc_1)).

%------------------------------------------------------------------------------
