%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:38 EST 2020

% Result     : Theorem 1.70s
% Output     : Refutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 168 expanded)
%              Number of leaves         :   23 (  75 expanded)
%              Depth                    :    8
%              Number of atoms          :  345 ( 834 expanded)
%              Number of equality atoms :  109 ( 293 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f502,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f50,f58,f66,f70,f79,f85,f89,f95,f126,f140,f149,f154,f302,f455,f501])).

fof(f501,plain,
    ( ~ spl8_18
    | spl8_20
    | ~ spl8_37
    | ~ spl8_49 ),
    inference(avatar_contradiction_clause,[],[f500])).

fof(f500,plain,
    ( $false
    | ~ spl8_18
    | spl8_20
    | ~ spl8_37
    | ~ spl8_49 ),
    inference(subsumption_resolution,[],[f153,f499])).

fof(f499,plain,
    ( k4_tarski(sK0,sK1) = sK2(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)))
    | ~ spl8_18
    | ~ spl8_37
    | ~ spl8_49 ),
    inference(forward_demodulation,[],[f472,f476])).

fof(f476,plain,
    ( sK1 = sK7(k1_tarski(sK0),k1_tarski(sK1),sK2(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))))
    | ~ spl8_18
    | ~ spl8_49 ),
    inference(unit_resulting_resolution,[],[f454,f139])).

fof(f139,plain,
    ( ! [X2,X0,X1] :
        ( sK7(X1,k1_tarski(X2),X0) = X2
        | ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) )
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl8_18
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2)))
        | sK7(X1,k1_tarski(X2),X0) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f454,plain,
    ( r2_hidden(sK2(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)))
    | ~ spl8_49 ),
    inference(avatar_component_clause,[],[f452])).

fof(f452,plain,
    ( spl8_49
  <=> r2_hidden(sK2(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).

fof(f472,plain,
    ( sK2(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))) = k4_tarski(sK0,sK7(k1_tarski(sK0),k1_tarski(sK1),sK2(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)))))
    | ~ spl8_37
    | ~ spl8_49 ),
    inference(unit_resulting_resolution,[],[f454,f301])).

fof(f301,plain,
    ( ! [X2,X0,X1] :
        ( k4_tarski(X0,sK7(k1_tarski(X0),X1,X2)) = X2
        | ~ r2_hidden(X2,k2_zfmisc_1(k1_tarski(X0),X1)) )
    | ~ spl8_37 ),
    inference(avatar_component_clause,[],[f300])).

fof(f300,plain,
    ( spl8_37
  <=> ! [X1,X0,X2] :
        ( k4_tarski(X0,sK7(k1_tarski(X0),X1,X2)) = X2
        | ~ r2_hidden(X2,k2_zfmisc_1(k1_tarski(X0),X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f153,plain,
    ( k4_tarski(sK0,sK1) != sK2(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)))
    | spl8_20 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl8_20
  <=> k4_tarski(sK0,sK1) = sK2(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f455,plain,
    ( spl8_49
    | spl8_1
    | ~ spl8_10
    | spl8_20 ),
    inference(avatar_split_clause,[],[f184,f151,f87,f43,f452])).

fof(f43,plain,
    ( spl8_1
  <=> k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)) = k1_tarski(k4_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f87,plain,
    ( spl8_10
  <=> ! [X1,X0] :
        ( k1_tarski(X0) = X1
        | sK2(X0,X1) = X0
        | r2_hidden(sK2(X0,X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f184,plain,
    ( r2_hidden(sK2(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)))
    | spl8_1
    | ~ spl8_10
    | spl8_20 ),
    inference(unit_resulting_resolution,[],[f45,f153,f88])).

fof(f88,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2(X0,X1),X1)
        | sK2(X0,X1) = X0
        | k1_tarski(X0) = X1 )
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f87])).

fof(f45,plain,
    ( k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)) != k1_tarski(k4_tarski(sK0,sK1))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f302,plain,
    ( spl8_37
    | ~ spl8_11
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f159,f147,f93,f300])).

fof(f93,plain,
    ( spl8_11
  <=> ! [X1,X8,X0] :
        ( k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8
        | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f147,plain,
    ( spl8_19
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
        | sK6(k1_tarski(X1),X2,X0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f159,plain,
    ( ! [X2,X0,X1] :
        ( k4_tarski(X0,sK7(k1_tarski(X0),X1,X2)) = X2
        | ~ r2_hidden(X2,k2_zfmisc_1(k1_tarski(X0),X1)) )
    | ~ spl8_11
    | ~ spl8_19 ),
    inference(duplicate_literal_removal,[],[f156])).

fof(f156,plain,
    ( ! [X2,X0,X1] :
        ( k4_tarski(X0,sK7(k1_tarski(X0),X1,X2)) = X2
        | ~ r2_hidden(X2,k2_zfmisc_1(k1_tarski(X0),X1))
        | ~ r2_hidden(X2,k2_zfmisc_1(k1_tarski(X0),X1)) )
    | ~ spl8_11
    | ~ spl8_19 ),
    inference(superposition,[],[f94,f148])).

fof(f148,plain,
    ( ! [X2,X0,X1] :
        ( sK6(k1_tarski(X1),X2,X0) = X1
        | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) )
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f147])).

fof(f94,plain,
    ( ! [X0,X8,X1] :
        ( k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8
        | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) )
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f93])).

fof(f154,plain,
    ( ~ spl8_20
    | spl8_1
    | ~ spl8_8
    | ~ spl8_17 ),
    inference(avatar_split_clause,[],[f134,f124,f77,f43,f151])).

fof(f77,plain,
    ( spl8_8
  <=> ! [X1,X0] :
        ( k1_tarski(X0) = X1
        | sK2(X0,X1) != X0
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f124,plain,
    ( spl8_17
  <=> ! [X1,X0] : r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f134,plain,
    ( k4_tarski(sK0,sK1) != sK2(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)))
    | spl8_1
    | ~ spl8_8
    | ~ spl8_17 ),
    inference(unit_resulting_resolution,[],[f45,f125,f78])).

fof(f78,plain,
    ( ! [X0,X1] :
        ( sK2(X0,X1) != X0
        | k1_tarski(X0) = X1
        | ~ r2_hidden(X0,X1) )
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f77])).

fof(f125,plain,
    ( ! [X0,X1] : r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)))
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f124])).

fof(f149,plain,
    ( spl8_19
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f81,f68,f56,f147])).

fof(f56,plain,
    ( spl8_4
  <=> ! [X3,X0] :
        ( X0 = X3
        | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f68,plain,
    ( spl8_6
  <=> ! [X1,X8,X0] :
        ( r2_hidden(sK6(X0,X1,X8),X0)
        | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f81,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
        | sK6(k1_tarski(X1),X2,X0) = X1 )
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(resolution,[],[f69,f57])).

fof(f57,plain,
    ( ! [X0,X3] :
        ( ~ r2_hidden(X3,k1_tarski(X0))
        | X0 = X3 )
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f56])).

fof(f69,plain,
    ( ! [X0,X8,X1] :
        ( r2_hidden(sK6(X0,X1,X8),X0)
        | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) )
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f68])).

fof(f140,plain,
    ( spl8_18
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f80,f64,f56,f138])).

fof(f64,plain,
    ( spl8_5
  <=> ! [X1,X8,X0] :
        ( r2_hidden(sK7(X0,X1,X8),X1)
        | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f80,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2)))
        | sK7(X1,k1_tarski(X2),X0) = X2 )
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(resolution,[],[f65,f57])).

fof(f65,plain,
    ( ! [X0,X8,X1] :
        ( r2_hidden(sK7(X0,X1,X8),X1)
        | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) )
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f64])).

fof(f126,plain,
    ( spl8_17
    | ~ spl8_2
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f90,f83,f48,f124])).

fof(f48,plain,
    ( spl8_2
  <=> ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

% (19958)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
fof(f83,plain,
    ( spl8_9
  <=> ! [X9,X1,X10,X0] :
        ( r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1))
        | ~ r2_hidden(X10,X1)
        | ~ r2_hidden(X9,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f90,plain,
    ( ! [X0,X1] : r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)))
    | ~ spl8_2
    | ~ spl8_9 ),
    inference(unit_resulting_resolution,[],[f49,f49,f84])).

fof(f84,plain,
    ( ! [X0,X10,X1,X9] :
        ( r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1))
        | ~ r2_hidden(X10,X1)
        | ~ r2_hidden(X9,X0) )
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f83])).

fof(f49,plain,
    ( ! [X3] : r2_hidden(X3,k1_tarski(X3))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f48])).

% (19940)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
fof(f95,plain,(
    spl8_11 ),
    inference(avatar_split_clause,[],[f38,f93])).

fof(f38,plain,(
    ! [X0,X8,X1] :
      ( k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X8,X1] :
      ( k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK3(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( sK3(X0,X1,X2) = k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2))
              & r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8
                & r2_hidden(sK7(X0,X1,X8),X1)
                & r2_hidden(sK6(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f14,f17,f16,f15])).

fof(f15,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != X3
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X6,X7] :
                ( k4_tarski(X6,X7) = X3
                & r2_hidden(X7,X1)
                & r2_hidden(X6,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X5,X4] :
              ( k4_tarski(X4,X5) != sK3(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK3(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

% (19930)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK3(X0,X1,X2)
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( sK3(X0,X1,X2) = k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2))
        & r2_hidden(sK5(X0,X1,X2),X1)
        & r2_hidden(sK4(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8
        & r2_hidden(sK7(X0,X1,X8),X1)
        & r2_hidden(sK6(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X6,X7] :
                  ( k4_tarski(X6,X7) = X3
                  & r2_hidden(X7,X1)
                  & r2_hidden(X6,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ? [X11,X12] :
                  ( k4_tarski(X11,X12) = X8
                  & r2_hidden(X12,X1)
                  & r2_hidden(X11,X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) ) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f89,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f23,f87])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK2(X0,X1) = X0
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f11])).

fof(f11,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

% (19930)Refutation not found, incomplete strategy% (19930)------------------------------
% (19930)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (19930)Termination reason: Refutation not found, incomplete strategy

% (19930)Memory used [KB]: 1663
% (19930)Time elapsed: 0.197 s
% (19930)------------------------------
% (19930)------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f85,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f37,f83])).

fof(f37,plain,(
    ! [X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),X2)
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f79,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f41,f77])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK2(X0,X1) != X0
      | ~ r2_hidden(X0,X1) ) ),
    inference(inner_rewriting,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK2(X0,X1) != X0
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f70,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f40,f68])).

fof(f40,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK6(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK6(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f66,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f39,f64])).

fof(f39,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK7(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK7(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f58,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f35,f56])).

% (19940)Refutation not found, incomplete strategy% (19940)------------------------------
% (19940)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (19940)Termination reason: Refutation not found, incomplete strategy

% (19940)Memory used [KB]: 10746
% (19940)Time elapsed: 0.196 s
% (19940)------------------------------
% (19940)------------------------------
fof(f35,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f50,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f34,f48])).

fof(f34,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f46,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f19,f43])).

fof(f19,plain,(
    k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)) != k1_tarski(k4_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)) != k1_tarski(k4_tarski(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f7])).

fof(f7,plain,
    ( ? [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(k4_tarski(X0,X1))
   => k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)) != k1_tarski(k4_tarski(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(k4_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:45:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (19944)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.47  % (19952)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.47  % (19944)Refutation not found, incomplete strategy% (19944)------------------------------
% 0.21/0.47  % (19944)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (19944)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (19944)Memory used [KB]: 1663
% 0.21/0.47  % (19944)Time elapsed: 0.057 s
% 0.21/0.47  % (19944)------------------------------
% 0.21/0.47  % (19944)------------------------------
% 1.70/0.58  % (19934)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.70/0.58  % (19943)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.70/0.59  % (19951)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.70/0.60  % (19969)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 1.70/0.63  % (19939)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.70/0.63  % (19953)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.70/0.63  % (19956)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.70/0.63  % (19942)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.70/0.63  % (19931)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.70/0.63  % (19933)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.70/0.63  % (19936)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.70/0.63  % (19955)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.70/0.63  % (19969)Refutation found. Thanks to Tanya!
% 1.70/0.63  % SZS status Theorem for theBenchmark
% 1.70/0.63  % SZS output start Proof for theBenchmark
% 1.70/0.63  fof(f502,plain,(
% 1.70/0.63    $false),
% 1.70/0.63    inference(avatar_sat_refutation,[],[f46,f50,f58,f66,f70,f79,f85,f89,f95,f126,f140,f149,f154,f302,f455,f501])).
% 1.70/0.63  fof(f501,plain,(
% 1.70/0.63    ~spl8_18 | spl8_20 | ~spl8_37 | ~spl8_49),
% 1.70/0.63    inference(avatar_contradiction_clause,[],[f500])).
% 1.70/0.63  fof(f500,plain,(
% 1.70/0.63    $false | (~spl8_18 | spl8_20 | ~spl8_37 | ~spl8_49)),
% 1.70/0.63    inference(subsumption_resolution,[],[f153,f499])).
% 1.70/0.63  fof(f499,plain,(
% 1.70/0.63    k4_tarski(sK0,sK1) = sK2(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))) | (~spl8_18 | ~spl8_37 | ~spl8_49)),
% 1.70/0.63    inference(forward_demodulation,[],[f472,f476])).
% 1.70/0.63  fof(f476,plain,(
% 1.70/0.63    sK1 = sK7(k1_tarski(sK0),k1_tarski(sK1),sK2(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)))) | (~spl8_18 | ~spl8_49)),
% 1.70/0.63    inference(unit_resulting_resolution,[],[f454,f139])).
% 1.70/0.63  fof(f139,plain,(
% 1.70/0.63    ( ! [X2,X0,X1] : (sK7(X1,k1_tarski(X2),X0) = X2 | ~r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2)))) ) | ~spl8_18),
% 1.70/0.63    inference(avatar_component_clause,[],[f138])).
% 1.70/0.63  fof(f138,plain,(
% 1.70/0.63    spl8_18 <=> ! [X1,X0,X2] : (~r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) | sK7(X1,k1_tarski(X2),X0) = X2)),
% 1.70/0.63    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 1.70/0.63  fof(f454,plain,(
% 1.70/0.63    r2_hidden(sK2(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))) | ~spl8_49),
% 1.70/0.63    inference(avatar_component_clause,[],[f452])).
% 1.70/0.63  fof(f452,plain,(
% 1.70/0.63    spl8_49 <=> r2_hidden(sK2(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)))),
% 1.70/0.63    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).
% 1.70/0.63  fof(f472,plain,(
% 1.70/0.63    sK2(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))) = k4_tarski(sK0,sK7(k1_tarski(sK0),k1_tarski(sK1),sK2(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))))) | (~spl8_37 | ~spl8_49)),
% 1.70/0.63    inference(unit_resulting_resolution,[],[f454,f301])).
% 1.70/0.63  fof(f301,plain,(
% 1.70/0.63    ( ! [X2,X0,X1] : (k4_tarski(X0,sK7(k1_tarski(X0),X1,X2)) = X2 | ~r2_hidden(X2,k2_zfmisc_1(k1_tarski(X0),X1))) ) | ~spl8_37),
% 1.70/0.63    inference(avatar_component_clause,[],[f300])).
% 1.70/0.63  fof(f300,plain,(
% 1.70/0.63    spl8_37 <=> ! [X1,X0,X2] : (k4_tarski(X0,sK7(k1_tarski(X0),X1,X2)) = X2 | ~r2_hidden(X2,k2_zfmisc_1(k1_tarski(X0),X1)))),
% 1.70/0.63    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).
% 1.70/0.63  fof(f153,plain,(
% 1.70/0.63    k4_tarski(sK0,sK1) != sK2(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))) | spl8_20),
% 1.70/0.63    inference(avatar_component_clause,[],[f151])).
% 1.70/0.63  fof(f151,plain,(
% 1.70/0.63    spl8_20 <=> k4_tarski(sK0,sK1) = sK2(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)))),
% 1.70/0.63    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 1.70/0.63  fof(f455,plain,(
% 1.70/0.63    spl8_49 | spl8_1 | ~spl8_10 | spl8_20),
% 1.70/0.63    inference(avatar_split_clause,[],[f184,f151,f87,f43,f452])).
% 1.70/0.63  fof(f43,plain,(
% 1.70/0.63    spl8_1 <=> k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)) = k1_tarski(k4_tarski(sK0,sK1))),
% 1.70/0.63    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.70/0.63  fof(f87,plain,(
% 1.70/0.63    spl8_10 <=> ! [X1,X0] : (k1_tarski(X0) = X1 | sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))),
% 1.70/0.63    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 1.70/0.64  fof(f184,plain,(
% 1.70/0.64    r2_hidden(sK2(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))) | (spl8_1 | ~spl8_10 | spl8_20)),
% 1.70/0.64    inference(unit_resulting_resolution,[],[f45,f153,f88])).
% 1.70/0.64  fof(f88,plain,(
% 1.70/0.64    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | sK2(X0,X1) = X0 | k1_tarski(X0) = X1) ) | ~spl8_10),
% 1.70/0.64    inference(avatar_component_clause,[],[f87])).
% 1.70/0.64  fof(f45,plain,(
% 1.70/0.64    k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)) != k1_tarski(k4_tarski(sK0,sK1)) | spl8_1),
% 1.70/0.64    inference(avatar_component_clause,[],[f43])).
% 1.70/0.64  fof(f302,plain,(
% 1.70/0.64    spl8_37 | ~spl8_11 | ~spl8_19),
% 1.70/0.64    inference(avatar_split_clause,[],[f159,f147,f93,f300])).
% 1.70/0.64  fof(f93,plain,(
% 1.70/0.64    spl8_11 <=> ! [X1,X8,X0] : (k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8 | ~r2_hidden(X8,k2_zfmisc_1(X0,X1)))),
% 1.70/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 1.70/0.64  fof(f147,plain,(
% 1.70/0.64    spl8_19 <=> ! [X1,X0,X2] : (~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) | sK6(k1_tarski(X1),X2,X0) = X1)),
% 1.70/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 1.70/0.64  fof(f159,plain,(
% 1.70/0.64    ( ! [X2,X0,X1] : (k4_tarski(X0,sK7(k1_tarski(X0),X1,X2)) = X2 | ~r2_hidden(X2,k2_zfmisc_1(k1_tarski(X0),X1))) ) | (~spl8_11 | ~spl8_19)),
% 1.70/0.64    inference(duplicate_literal_removal,[],[f156])).
% 1.70/0.64  fof(f156,plain,(
% 1.70/0.64    ( ! [X2,X0,X1] : (k4_tarski(X0,sK7(k1_tarski(X0),X1,X2)) = X2 | ~r2_hidden(X2,k2_zfmisc_1(k1_tarski(X0),X1)) | ~r2_hidden(X2,k2_zfmisc_1(k1_tarski(X0),X1))) ) | (~spl8_11 | ~spl8_19)),
% 1.70/0.64    inference(superposition,[],[f94,f148])).
% 1.70/0.64  fof(f148,plain,(
% 1.70/0.64    ( ! [X2,X0,X1] : (sK6(k1_tarski(X1),X2,X0) = X1 | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))) ) | ~spl8_19),
% 1.70/0.64    inference(avatar_component_clause,[],[f147])).
% 1.70/0.64  fof(f94,plain,(
% 1.70/0.64    ( ! [X0,X8,X1] : (k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8 | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) ) | ~spl8_11),
% 1.70/0.64    inference(avatar_component_clause,[],[f93])).
% 1.70/0.64  fof(f154,plain,(
% 1.70/0.64    ~spl8_20 | spl8_1 | ~spl8_8 | ~spl8_17),
% 1.70/0.64    inference(avatar_split_clause,[],[f134,f124,f77,f43,f151])).
% 1.70/0.64  fof(f77,plain,(
% 1.70/0.64    spl8_8 <=> ! [X1,X0] : (k1_tarski(X0) = X1 | sK2(X0,X1) != X0 | ~r2_hidden(X0,X1))),
% 1.70/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 1.70/0.64  fof(f124,plain,(
% 1.70/0.64    spl8_17 <=> ! [X1,X0] : r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)))),
% 1.70/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 1.70/0.64  fof(f134,plain,(
% 1.70/0.64    k4_tarski(sK0,sK1) != sK2(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))) | (spl8_1 | ~spl8_8 | ~spl8_17)),
% 1.70/0.64    inference(unit_resulting_resolution,[],[f45,f125,f78])).
% 1.70/0.64  fof(f78,plain,(
% 1.70/0.64    ( ! [X0,X1] : (sK2(X0,X1) != X0 | k1_tarski(X0) = X1 | ~r2_hidden(X0,X1)) ) | ~spl8_8),
% 1.70/0.64    inference(avatar_component_clause,[],[f77])).
% 1.70/0.64  fof(f125,plain,(
% 1.70/0.64    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)))) ) | ~spl8_17),
% 1.70/0.64    inference(avatar_component_clause,[],[f124])).
% 1.70/0.64  fof(f149,plain,(
% 1.70/0.64    spl8_19 | ~spl8_4 | ~spl8_6),
% 1.70/0.64    inference(avatar_split_clause,[],[f81,f68,f56,f147])).
% 1.70/0.64  fof(f56,plain,(
% 1.70/0.64    spl8_4 <=> ! [X3,X0] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0)))),
% 1.70/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.70/0.64  fof(f68,plain,(
% 1.70/0.64    spl8_6 <=> ! [X1,X8,X0] : (r2_hidden(sK6(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1)))),
% 1.70/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 1.70/0.64  fof(f81,plain,(
% 1.70/0.64    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) | sK6(k1_tarski(X1),X2,X0) = X1) ) | (~spl8_4 | ~spl8_6)),
% 1.70/0.64    inference(resolution,[],[f69,f57])).
% 1.70/0.64  fof(f57,plain,(
% 1.70/0.64    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) ) | ~spl8_4),
% 1.70/0.64    inference(avatar_component_clause,[],[f56])).
% 1.70/0.64  fof(f69,plain,(
% 1.70/0.64    ( ! [X0,X8,X1] : (r2_hidden(sK6(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) ) | ~spl8_6),
% 1.70/0.64    inference(avatar_component_clause,[],[f68])).
% 1.70/0.64  fof(f140,plain,(
% 1.70/0.64    spl8_18 | ~spl8_4 | ~spl8_5),
% 1.70/0.64    inference(avatar_split_clause,[],[f80,f64,f56,f138])).
% 1.70/0.64  fof(f64,plain,(
% 1.70/0.64    spl8_5 <=> ! [X1,X8,X0] : (r2_hidden(sK7(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1)))),
% 1.70/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.70/0.64  fof(f80,plain,(
% 1.70/0.64    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) | sK7(X1,k1_tarski(X2),X0) = X2) ) | (~spl8_4 | ~spl8_5)),
% 1.70/0.64    inference(resolution,[],[f65,f57])).
% 1.70/0.64  fof(f65,plain,(
% 1.70/0.64    ( ! [X0,X8,X1] : (r2_hidden(sK7(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) ) | ~spl8_5),
% 1.70/0.64    inference(avatar_component_clause,[],[f64])).
% 1.70/0.64  fof(f126,plain,(
% 1.70/0.64    spl8_17 | ~spl8_2 | ~spl8_9),
% 1.70/0.64    inference(avatar_split_clause,[],[f90,f83,f48,f124])).
% 1.70/0.64  fof(f48,plain,(
% 1.70/0.64    spl8_2 <=> ! [X3] : r2_hidden(X3,k1_tarski(X3))),
% 1.70/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.70/0.64  % (19958)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.70/0.64  fof(f83,plain,(
% 1.70/0.64    spl8_9 <=> ! [X9,X1,X10,X0] : (r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))),
% 1.70/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 1.70/0.64  fof(f90,plain,(
% 1.70/0.64    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)))) ) | (~spl8_2 | ~spl8_9)),
% 1.70/0.64    inference(unit_resulting_resolution,[],[f49,f49,f84])).
% 1.70/0.64  fof(f84,plain,(
% 1.70/0.64    ( ! [X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0)) ) | ~spl8_9),
% 1.70/0.64    inference(avatar_component_clause,[],[f83])).
% 1.70/0.64  fof(f49,plain,(
% 1.70/0.64    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) ) | ~spl8_2),
% 1.70/0.64    inference(avatar_component_clause,[],[f48])).
% 1.70/0.64  % (19940)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.70/0.64  fof(f95,plain,(
% 1.70/0.64    spl8_11),
% 1.70/0.64    inference(avatar_split_clause,[],[f38,f93])).
% 1.70/0.64  fof(f38,plain,(
% 1.70/0.64    ( ! [X0,X8,X1] : (k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8 | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 1.70/0.64    inference(equality_resolution,[],[f27])).
% 1.70/0.64  fof(f27,plain,(
% 1.70/0.64    ( ! [X2,X0,X8,X1] : (k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8 | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.70/0.64    inference(cnf_transformation,[],[f18])).
% 1.70/0.64  fof(f18,plain,(
% 1.70/0.64    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK3(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((sK3(X0,X1,X2) = k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) & r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8 & r2_hidden(sK7(X0,X1,X8),X1) & r2_hidden(sK6(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 1.70/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f14,f17,f16,f15])).
% 1.70/0.64  fof(f15,plain,(
% 1.70/0.64    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK3(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK3(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.70/0.64    introduced(choice_axiom,[])).
% 1.70/0.64  % (19930)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.70/0.64  fof(f16,plain,(
% 1.70/0.64    ! [X2,X1,X0] : (? [X7,X6] : (k4_tarski(X6,X7) = sK3(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (sK3(X0,X1,X2) = k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) & r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)))),
% 1.70/0.64    introduced(choice_axiom,[])).
% 1.70/0.64  fof(f17,plain,(
% 1.70/0.64    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8 & r2_hidden(sK7(X0,X1,X8),X1) & r2_hidden(sK6(X0,X1,X8),X0)))),
% 1.70/0.64    introduced(choice_axiom,[])).
% 1.70/0.64  fof(f14,plain,(
% 1.70/0.64    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 1.70/0.64    inference(rectify,[],[f13])).
% 1.70/0.64  fof(f13,plain,(
% 1.70/0.64    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 1.70/0.64    inference(nnf_transformation,[],[f3])).
% 1.70/0.64  fof(f3,axiom,(
% 1.70/0.64    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 1.70/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 1.70/0.64  fof(f89,plain,(
% 1.70/0.64    spl8_10),
% 1.70/0.64    inference(avatar_split_clause,[],[f23,f87])).
% 1.70/0.64  fof(f23,plain,(
% 1.70/0.64    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)) )),
% 1.70/0.64    inference(cnf_transformation,[],[f12])).
% 1.70/0.64  fof(f12,plain,(
% 1.70/0.64    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.70/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f11])).
% 1.70/0.64  fof(f11,plain,(
% 1.70/0.64    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 1.70/0.64    introduced(choice_axiom,[])).
% 1.70/0.64  fof(f10,plain,(
% 1.70/0.64    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.70/0.64    inference(rectify,[],[f9])).
% 1.70/0.64  fof(f9,plain,(
% 1.70/0.64    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.70/0.64    inference(nnf_transformation,[],[f1])).
% 1.70/0.64  % (19930)Refutation not found, incomplete strategy% (19930)------------------------------
% 1.70/0.64  % (19930)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.64  % (19930)Termination reason: Refutation not found, incomplete strategy
% 1.70/0.64  
% 1.70/0.64  % (19930)Memory used [KB]: 1663
% 1.70/0.64  % (19930)Time elapsed: 0.197 s
% 1.70/0.64  % (19930)------------------------------
% 1.70/0.64  % (19930)------------------------------
% 1.70/0.64  fof(f1,axiom,(
% 1.70/0.64    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.70/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.70/0.64  fof(f85,plain,(
% 1.70/0.64    spl8_9),
% 1.70/0.64    inference(avatar_split_clause,[],[f37,f83])).
% 1.70/0.64  fof(f37,plain,(
% 1.70/0.64    ( ! [X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0)) )),
% 1.70/0.64    inference(equality_resolution,[],[f36])).
% 1.70/0.64  fof(f36,plain,(
% 1.70/0.64    ( ! [X2,X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),X2) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.70/0.64    inference(equality_resolution,[],[f28])).
% 1.70/0.64  fof(f28,plain,(
% 1.70/0.64    ( ! [X2,X0,X10,X8,X1,X9] : (r2_hidden(X8,X2) | k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.70/0.64    inference(cnf_transformation,[],[f18])).
% 1.70/0.64  fof(f79,plain,(
% 1.70/0.64    spl8_8),
% 1.70/0.64    inference(avatar_split_clause,[],[f41,f77])).
% 1.70/0.64  fof(f41,plain,(
% 1.70/0.64    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK2(X0,X1) != X0 | ~r2_hidden(X0,X1)) )),
% 1.70/0.64    inference(inner_rewriting,[],[f24])).
% 1.70/0.64  fof(f24,plain,(
% 1.70/0.64    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) )),
% 1.70/0.64    inference(cnf_transformation,[],[f12])).
% 1.70/0.64  fof(f70,plain,(
% 1.70/0.64    spl8_6),
% 1.70/0.64    inference(avatar_split_clause,[],[f40,f68])).
% 1.70/0.64  fof(f40,plain,(
% 1.70/0.64    ( ! [X0,X8,X1] : (r2_hidden(sK6(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 1.70/0.64    inference(equality_resolution,[],[f25])).
% 1.70/0.64  fof(f25,plain,(
% 1.70/0.64    ( ! [X2,X0,X8,X1] : (r2_hidden(sK6(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.70/0.64    inference(cnf_transformation,[],[f18])).
% 1.70/0.64  fof(f66,plain,(
% 1.70/0.64    spl8_5),
% 1.70/0.64    inference(avatar_split_clause,[],[f39,f64])).
% 1.70/0.64  fof(f39,plain,(
% 1.70/0.64    ( ! [X0,X8,X1] : (r2_hidden(sK7(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 1.70/0.64    inference(equality_resolution,[],[f26])).
% 1.70/0.64  fof(f26,plain,(
% 1.70/0.64    ( ! [X2,X0,X8,X1] : (r2_hidden(sK7(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.70/0.64    inference(cnf_transformation,[],[f18])).
% 1.70/0.64  fof(f58,plain,(
% 1.70/0.64    spl8_4),
% 1.70/0.64    inference(avatar_split_clause,[],[f35,f56])).
% 1.70/0.64  % (19940)Refutation not found, incomplete strategy% (19940)------------------------------
% 1.70/0.64  % (19940)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.64  % (19940)Termination reason: Refutation not found, incomplete strategy
% 1.70/0.64  
% 1.70/0.64  % (19940)Memory used [KB]: 10746
% 1.70/0.64  % (19940)Time elapsed: 0.196 s
% 1.70/0.64  % (19940)------------------------------
% 1.70/0.64  % (19940)------------------------------
% 1.70/0.64  fof(f35,plain,(
% 1.70/0.64    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 1.70/0.64    inference(equality_resolution,[],[f21])).
% 1.70/0.64  fof(f21,plain,(
% 1.70/0.64    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.70/0.64    inference(cnf_transformation,[],[f12])).
% 1.70/0.64  fof(f50,plain,(
% 1.70/0.64    spl8_2),
% 1.70/0.64    inference(avatar_split_clause,[],[f34,f48])).
% 1.70/0.64  fof(f34,plain,(
% 1.70/0.64    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 1.70/0.64    inference(equality_resolution,[],[f33])).
% 1.70/0.64  fof(f33,plain,(
% 1.70/0.64    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 1.70/0.64    inference(equality_resolution,[],[f22])).
% 1.70/0.64  fof(f22,plain,(
% 1.70/0.64    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.70/0.64    inference(cnf_transformation,[],[f12])).
% 1.70/0.64  fof(f46,plain,(
% 1.70/0.64    ~spl8_1),
% 1.70/0.64    inference(avatar_split_clause,[],[f19,f43])).
% 1.70/0.64  fof(f19,plain,(
% 1.70/0.64    k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)) != k1_tarski(k4_tarski(sK0,sK1))),
% 1.70/0.64    inference(cnf_transformation,[],[f8])).
% 1.70/0.64  fof(f8,plain,(
% 1.70/0.64    k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)) != k1_tarski(k4_tarski(sK0,sK1))),
% 1.70/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f7])).
% 1.70/0.64  fof(f7,plain,(
% 1.70/0.64    ? [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(k4_tarski(X0,X1)) => k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)) != k1_tarski(k4_tarski(sK0,sK1))),
% 1.70/0.64    introduced(choice_axiom,[])).
% 1.70/0.64  fof(f6,plain,(
% 1.70/0.64    ? [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(k4_tarski(X0,X1))),
% 1.70/0.64    inference(ennf_transformation,[],[f5])).
% 1.70/0.64  fof(f5,negated_conjecture,(
% 1.70/0.64    ~! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1))),
% 1.70/0.64    inference(negated_conjecture,[],[f4])).
% 1.70/0.64  fof(f4,conjecture,(
% 1.70/0.64    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1))),
% 1.70/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_zfmisc_1)).
% 1.70/0.64  % SZS output end Proof for theBenchmark
% 1.70/0.64  % (19969)------------------------------
% 1.70/0.64  % (19969)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.64  % (19969)Termination reason: Refutation
% 1.70/0.64  
% 1.70/0.64  % (19969)Memory used [KB]: 6780
% 1.70/0.64  % (19969)Time elapsed: 0.045 s
% 1.70/0.64  % (19969)------------------------------
% 1.70/0.64  % (19969)------------------------------
% 1.70/0.64  % (19945)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.70/0.64  % (19946)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.70/0.64  % (19937)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.70/0.64  % (19924)Success in time 0.284 s
%------------------------------------------------------------------------------
