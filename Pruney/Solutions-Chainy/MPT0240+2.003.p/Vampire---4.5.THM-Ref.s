%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:39 EST 2020

% Result     : Theorem 3.01s
% Output     : Refutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 166 expanded)
%              Number of leaves         :   16 (  62 expanded)
%              Depth                    :   14
%              Number of atoms          :  319 (1022 expanded)
%              Number of equality atoms :  137 ( 515 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f951,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f643,f759,f798,f824,f863,f913,f950])).

fof(f950,plain,
    ( spl8_3
    | spl8_1
    | spl8_2
    | ~ spl8_5
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f942,f860,f795,f640,f54,f752])).

fof(f752,plain,
    ( spl8_3
  <=> r2_hidden(sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f54,plain,
    ( spl8_1
  <=> k2_zfmisc_1(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1)) = k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f640,plain,
    ( spl8_2
  <=> k4_tarski(sK0,sK1) = sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f795,plain,
    ( spl8_5
  <=> sK0 = sK3(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f860,plain,
    ( spl8_7
  <=> sK1 = sK4(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f942,plain,
    ( r2_hidden(sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)))
    | spl8_1
    | spl8_2
    | ~ spl8_5
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f941,f642])).

fof(f642,plain,
    ( k4_tarski(sK0,sK1) != sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)))
    | spl8_2 ),
    inference(avatar_component_clause,[],[f640])).

fof(f941,plain,
    ( k4_tarski(sK0,sK1) = sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)))
    | r2_hidden(sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)))
    | spl8_1
    | ~ spl8_5
    | ~ spl8_7 ),
    inference(forward_demodulation,[],[f940,f797])).

fof(f797,plain,
    ( sK0 = sK3(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f795])).

fof(f940,plain,
    ( sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))) = k4_tarski(sK3(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))),sK1)
    | r2_hidden(sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)))
    | spl8_1
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f930,f56])).

fof(f56,plain,
    ( k2_zfmisc_1(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1)) != k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f930,plain,
    ( sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))) = k4_tarski(sK3(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))),sK1)
    | k2_zfmisc_1(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1)) = k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))
    | r2_hidden(sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)))
    | ~ spl8_7 ),
    inference(superposition,[],[f33,f862])).

fof(f862,plain,
    ( sK1 = sK4(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)))
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f860])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X2
      | sK2(X0,X1,X2) = k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2))
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK2(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( sK2(X0,X1,X2) = k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2))
              & r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8
                & r2_hidden(sK6(X0,X1,X8),X1)
                & r2_hidden(sK5(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f16,f19,f18,f17])).

fof(f17,plain,(
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
              ( k4_tarski(X4,X5) != sK2(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK2(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK2(X0,X1,X2)
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( sK2(X0,X1,X2) = k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2))
        & r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(sK3(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8
        & r2_hidden(sK6(X0,X1,X8),X1)
        & r2_hidden(sK5(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
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
    inference(rectify,[],[f15])).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f913,plain,
    ( spl8_2
    | ~ spl8_3 ),
    inference(avatar_contradiction_clause,[],[f912])).

fof(f912,plain,
    ( $false
    | spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f910,f642])).

fof(f910,plain,
    ( k4_tarski(sK0,sK1) = sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)))
    | ~ spl8_3 ),
    inference(duplicate_literal_removal,[],[f885])).

fof(f885,plain,
    ( k4_tarski(sK0,sK1) = sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)))
    | k4_tarski(sK0,sK1) = sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)))
    | ~ spl8_3 ),
    inference(resolution,[],[f754,f52])).

fof(f52,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_tarski(X0,X1)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK7(X0,X1,X2) != X1
              & sK7(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( sK7(X0,X1,X2) = X1
            | sK7(X0,X1,X2) = X0
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f23,f24])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK7(X0,X1,X2) != X1
            & sK7(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( sK7(X0,X1,X2) = X1
          | sK7(X0,X1,X2) = X0
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f754,plain,
    ( r2_hidden(sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f752])).

fof(f863,plain,
    ( spl8_7
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f851,f821,f860])).

fof(f821,plain,
    ( spl8_6
  <=> r2_hidden(sK4(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))),k2_tarski(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f851,plain,
    ( sK1 = sK4(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)))
    | ~ spl8_6 ),
    inference(duplicate_literal_removal,[],[f826])).

fof(f826,plain,
    ( sK1 = sK4(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)))
    | sK1 = sK4(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)))
    | ~ spl8_6 ),
    inference(resolution,[],[f823,f52])).

fof(f823,plain,
    ( r2_hidden(sK4(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))),k2_tarski(sK1,sK1))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f821])).

fof(f824,plain,
    ( spl8_3
    | spl8_6
    | spl8_1 ),
    inference(avatar_split_clause,[],[f210,f54,f821,f752])).

fof(f210,plain,
    ( r2_hidden(sK4(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))),k2_tarski(sK1,sK1))
    | r2_hidden(sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)))
    | spl8_1 ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,
    ( ! [X1] :
        ( k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)) != X1
        | r2_hidden(sK4(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),X1),k2_tarski(sK1,sK1))
        | r2_hidden(sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),X1),X1) )
    | spl8_1 ),
    inference(superposition,[],[f56,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f798,plain,
    ( spl8_5
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f786,f756,f795])).

fof(f756,plain,
    ( spl8_4
  <=> r2_hidden(sK3(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))),k2_tarski(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f786,plain,
    ( sK0 = sK3(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)))
    | ~ spl8_4 ),
    inference(duplicate_literal_removal,[],[f761])).

fof(f761,plain,
    ( sK0 = sK3(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)))
    | sK0 = sK3(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)))
    | ~ spl8_4 ),
    inference(resolution,[],[f758,f52])).

fof(f758,plain,
    ( r2_hidden(sK3(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))),k2_tarski(sK0,sK0))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f756])).

fof(f759,plain,
    ( spl8_3
    | spl8_4
    | spl8_1 ),
    inference(avatar_split_clause,[],[f161,f54,f756,f752])).

fof(f161,plain,
    ( r2_hidden(sK3(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))),k2_tarski(sK0,sK0))
    | r2_hidden(sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)))
    | spl8_1 ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,
    ( ! [X0] :
        ( k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)) != X0
        | r2_hidden(sK3(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),X0),k2_tarski(sK0,sK0))
        | r2_hidden(sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),X0),X0) )
    | spl8_1 ),
    inference(superposition,[],[f56,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f643,plain,
    ( ~ spl8_2
    | spl8_1 ),
    inference(avatar_split_clause,[],[f633,f54,f640])).

fof(f633,plain,
    ( k4_tarski(sK0,sK1) != sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)))
    | spl8_1 ),
    inference(equality_resolution,[],[f608])).

fof(f608,plain,
    ( ! [X2] :
        ( k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)) != k2_tarski(X2,k4_tarski(sK0,sK1))
        | k4_tarski(sK0,sK1) != sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(X2,k4_tarski(sK0,sK1))) )
    | spl8_1 ),
    inference(resolution,[],[f603,f49])).

fof(f49,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f603,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK0,sK1),X0)
        | k4_tarski(sK0,sK1) != sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),X0)
        | k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)) != X0 )
    | spl8_1 ),
    inference(inner_rewriting,[],[f587])).

fof(f587,plain,
    ( ! [X0] :
        ( k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)) != X0
        | k4_tarski(sK0,sK1) != sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),X0)
        | ~ r2_hidden(sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),X0),X0) )
    | spl8_1 ),
    inference(resolution,[],[f241,f49])).

fof(f241,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k2_tarski(sK0,sK0))
        | k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)) != X1
        | sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),X1) != k4_tarski(X0,sK1)
        | ~ r2_hidden(sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),X1),X1) )
    | spl8_1 ),
    inference(resolution,[],[f67,f49])).

fof(f67,plain,
    ( ! [X4,X5,X3] :
        ( ~ r2_hidden(X5,k2_tarski(sK1,sK1))
        | k4_tarski(X4,X5) != sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),X3)
        | k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)) != X3
        | ~ r2_hidden(X4,k2_tarski(sK0,sK0))
        | ~ r2_hidden(sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),X3),X3) )
    | spl8_1 ),
    inference(superposition,[],[f56,f34])).

fof(f34,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( k2_zfmisc_1(X0,X1) = X2
      | k4_tarski(X4,X5) != sK2(X0,X1,X2)
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f57,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f42,f54])).

fof(f42,plain,(
    k2_zfmisc_1(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1)) != k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)) ),
    inference(definition_unfolding,[],[f26,f35,f35,f35])).

fof(f35,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f26,plain,(
    k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)) != k1_tarski(k4_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)) != k1_tarski(k4_tarski(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(k4_tarski(X0,X1))
   => k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)) != k1_tarski(k4_tarski(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(k4_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:21:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (31258)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.52  % (31249)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (31247)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.52  % (31246)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.52  % (31266)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.52  % (31257)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.53  % (31274)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (31274)Refutation not found, incomplete strategy% (31274)------------------------------
% 0.22/0.53  % (31274)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (31274)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (31274)Memory used [KB]: 1663
% 0.22/0.53  % (31274)Time elapsed: 0.117 s
% 0.22/0.53  % (31274)------------------------------
% 0.22/0.53  % (31274)------------------------------
% 0.22/0.53  % (31273)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.53  % (31245)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.53  % (31244)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.53  % (31245)Refutation not found, incomplete strategy% (31245)------------------------------
% 0.22/0.53  % (31245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (31245)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (31245)Memory used [KB]: 1663
% 0.22/0.53  % (31245)Time elapsed: 0.118 s
% 0.22/0.53  % (31245)------------------------------
% 0.22/0.53  % (31245)------------------------------
% 0.22/0.53  % (31250)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.54  % (31256)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.54  % (31270)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.54  % (31261)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.54  % (31270)Refutation not found, incomplete strategy% (31270)------------------------------
% 0.22/0.54  % (31270)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (31270)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (31270)Memory used [KB]: 6140
% 0.22/0.54  % (31270)Time elapsed: 0.130 s
% 0.22/0.54  % (31270)------------------------------
% 0.22/0.54  % (31270)------------------------------
% 0.22/0.54  % (31252)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.55  % (31269)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.55  % (31259)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.55  % (31263)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.55  % (31259)Refutation not found, incomplete strategy% (31259)------------------------------
% 0.22/0.55  % (31259)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (31259)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (31259)Memory used [KB]: 1663
% 0.22/0.55  % (31259)Time elapsed: 0.144 s
% 0.22/0.55  % (31259)------------------------------
% 0.22/0.55  % (31259)------------------------------
% 0.22/0.55  % (31271)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (31271)Refutation not found, incomplete strategy% (31271)------------------------------
% 0.22/0.55  % (31271)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (31271)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (31271)Memory used [KB]: 6140
% 0.22/0.55  % (31271)Time elapsed: 0.140 s
% 0.22/0.55  % (31271)------------------------------
% 0.22/0.55  % (31271)------------------------------
% 0.22/0.55  % (31272)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.55  % (31262)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.55  % (31267)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.55  % (31272)Refutation not found, incomplete strategy% (31272)------------------------------
% 0.22/0.55  % (31272)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (31272)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (31272)Memory used [KB]: 6140
% 0.22/0.55  % (31272)Time elapsed: 0.140 s
% 0.22/0.55  % (31272)------------------------------
% 0.22/0.55  % (31272)------------------------------
% 0.22/0.55  % (31262)Refutation not found, incomplete strategy% (31262)------------------------------
% 0.22/0.55  % (31262)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (31262)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (31262)Memory used [KB]: 1663
% 0.22/0.55  % (31262)Time elapsed: 0.140 s
% 0.22/0.55  % (31262)------------------------------
% 0.22/0.55  % (31262)------------------------------
% 0.22/0.55  % (31268)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.55  % (31264)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.55  % (31265)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.55  % (31255)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.55  % (31253)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.55  % (31254)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.55  % (31269)Refutation not found, incomplete strategy% (31269)------------------------------
% 0.22/0.55  % (31269)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (31269)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (31269)Memory used [KB]: 10618
% 0.22/0.55  % (31269)Time elapsed: 0.140 s
% 0.22/0.55  % (31269)------------------------------
% 0.22/0.55  % (31269)------------------------------
% 0.22/0.56  % (31261)Refutation not found, incomplete strategy% (31261)------------------------------
% 0.22/0.56  % (31261)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (31261)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (31261)Memory used [KB]: 10618
% 0.22/0.56  % (31261)Time elapsed: 0.150 s
% 0.22/0.56  % (31261)------------------------------
% 0.22/0.56  % (31261)------------------------------
% 0.22/0.56  % (31256)Refutation not found, incomplete strategy% (31256)------------------------------
% 0.22/0.56  % (31256)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (31256)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (31256)Memory used [KB]: 6268
% 0.22/0.56  % (31256)Time elapsed: 0.153 s
% 0.22/0.56  % (31256)------------------------------
% 0.22/0.56  % (31256)------------------------------
% 0.22/0.56  % (31263)Refutation not found, incomplete strategy% (31263)------------------------------
% 0.22/0.56  % (31263)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (31263)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (31263)Memory used [KB]: 1663
% 0.22/0.56  % (31263)Time elapsed: 0.152 s
% 0.22/0.56  % (31263)------------------------------
% 0.22/0.56  % (31263)------------------------------
% 0.22/0.56  % (31260)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.57  % (31251)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 2.28/0.67  % (31300)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.28/0.67  % (31296)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.28/0.68  % (31247)Refutation not found, incomplete strategy% (31247)------------------------------
% 2.28/0.68  % (31247)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.28/0.68  % (31298)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.28/0.68  % (31297)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.28/0.68  % (31299)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.28/0.68  % (31299)Refutation not found, incomplete strategy% (31299)------------------------------
% 2.28/0.68  % (31299)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.28/0.68  % (31299)Termination reason: Refutation not found, incomplete strategy
% 2.28/0.68  
% 2.28/0.68  % (31299)Memory used [KB]: 10618
% 2.28/0.68  % (31299)Time elapsed: 0.107 s
% 2.28/0.68  % (31299)------------------------------
% 2.28/0.68  % (31299)------------------------------
% 2.28/0.68  % (31247)Termination reason: Refutation not found, incomplete strategy
% 2.28/0.68  
% 2.28/0.68  % (31247)Memory used [KB]: 6140
% 2.28/0.68  % (31247)Time elapsed: 0.270 s
% 2.28/0.68  % (31247)------------------------------
% 2.28/0.68  % (31247)------------------------------
% 2.28/0.69  % (31246)Refutation not found, incomplete strategy% (31246)------------------------------
% 2.28/0.69  % (31246)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.28/0.69  % (31298)Refutation not found, incomplete strategy% (31298)------------------------------
% 2.28/0.69  % (31298)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.28/0.69  % (31298)Termination reason: Refutation not found, incomplete strategy
% 2.28/0.69  
% 2.28/0.69  % (31298)Memory used [KB]: 10746
% 2.28/0.69  % (31298)Time elapsed: 0.116 s
% 2.28/0.69  % (31298)------------------------------
% 2.28/0.69  % (31298)------------------------------
% 2.28/0.69  % (31304)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 2.28/0.69  % (31304)Refutation not found, incomplete strategy% (31304)------------------------------
% 2.28/0.69  % (31304)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.28/0.69  % (31304)Termination reason: Refutation not found, incomplete strategy
% 2.28/0.69  
% 2.28/0.69  % (31304)Memory used [KB]: 10746
% 2.28/0.69  % (31304)Time elapsed: 0.109 s
% 2.28/0.69  % (31304)------------------------------
% 2.28/0.69  % (31304)------------------------------
% 2.28/0.70  % (31246)Termination reason: Refutation not found, incomplete strategy
% 2.28/0.70  
% 2.28/0.70  % (31246)Memory used [KB]: 6268
% 2.28/0.70  % (31246)Time elapsed: 0.267 s
% 2.28/0.70  % (31246)------------------------------
% 2.28/0.70  % (31246)------------------------------
% 2.28/0.71  % (31302)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.77/0.72  % (31303)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.77/0.72  % (31295)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.77/0.72  % (31301)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.77/0.73  % (31301)Refutation not found, incomplete strategy% (31301)------------------------------
% 2.77/0.73  % (31301)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.77/0.73  % (31301)Termination reason: Refutation not found, incomplete strategy
% 2.77/0.73  
% 2.77/0.73  % (31301)Memory used [KB]: 10746
% 2.77/0.73  % (31301)Time elapsed: 0.126 s
% 2.77/0.73  % (31301)------------------------------
% 2.77/0.73  % (31301)------------------------------
% 2.77/0.73  % (31305)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 3.01/0.81  % (31260)Refutation found. Thanks to Tanya!
% 3.01/0.81  % SZS status Theorem for theBenchmark
% 3.01/0.81  % SZS output start Proof for theBenchmark
% 3.01/0.81  fof(f951,plain,(
% 3.01/0.81    $false),
% 3.01/0.81    inference(avatar_sat_refutation,[],[f57,f643,f759,f798,f824,f863,f913,f950])).
% 3.01/0.81  fof(f950,plain,(
% 3.01/0.81    spl8_3 | spl8_1 | spl8_2 | ~spl8_5 | ~spl8_7),
% 3.01/0.81    inference(avatar_split_clause,[],[f942,f860,f795,f640,f54,f752])).
% 3.01/0.81  fof(f752,plain,(
% 3.01/0.81    spl8_3 <=> r2_hidden(sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)))),
% 3.01/0.81    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 3.01/0.81  fof(f54,plain,(
% 3.01/0.81    spl8_1 <=> k2_zfmisc_1(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1)) = k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))),
% 3.01/0.81    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 3.01/0.81  fof(f640,plain,(
% 3.01/0.81    spl8_2 <=> k4_tarski(sK0,sK1) = sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)))),
% 3.01/0.81    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 3.01/0.81  fof(f795,plain,(
% 3.01/0.81    spl8_5 <=> sK0 = sK3(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)))),
% 3.01/0.81    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 3.01/0.81  fof(f860,plain,(
% 3.01/0.81    spl8_7 <=> sK1 = sK4(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)))),
% 3.01/0.81    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 3.01/0.81  fof(f942,plain,(
% 3.01/0.81    r2_hidden(sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))) | (spl8_1 | spl8_2 | ~spl8_5 | ~spl8_7)),
% 3.01/0.81    inference(subsumption_resolution,[],[f941,f642])).
% 3.01/0.81  fof(f642,plain,(
% 3.01/0.81    k4_tarski(sK0,sK1) != sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))) | spl8_2),
% 3.01/0.81    inference(avatar_component_clause,[],[f640])).
% 3.01/0.81  fof(f941,plain,(
% 3.01/0.81    k4_tarski(sK0,sK1) = sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))) | r2_hidden(sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))) | (spl8_1 | ~spl8_5 | ~spl8_7)),
% 3.01/0.81    inference(forward_demodulation,[],[f940,f797])).
% 3.01/0.81  fof(f797,plain,(
% 3.01/0.81    sK0 = sK3(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))) | ~spl8_5),
% 3.01/0.81    inference(avatar_component_clause,[],[f795])).
% 3.01/0.81  fof(f940,plain,(
% 3.01/0.81    sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))) = k4_tarski(sK3(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))),sK1) | r2_hidden(sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))) | (spl8_1 | ~spl8_7)),
% 3.01/0.81    inference(subsumption_resolution,[],[f930,f56])).
% 3.01/0.81  fof(f56,plain,(
% 3.01/0.81    k2_zfmisc_1(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1)) != k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)) | spl8_1),
% 3.01/0.81    inference(avatar_component_clause,[],[f54])).
% 3.01/0.81  fof(f930,plain,(
% 3.01/0.81    sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))) = k4_tarski(sK3(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))),sK1) | k2_zfmisc_1(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1)) = k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)) | r2_hidden(sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))) | ~spl8_7),
% 3.01/0.81    inference(superposition,[],[f33,f862])).
% 3.01/0.81  fof(f862,plain,(
% 3.01/0.81    sK1 = sK4(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))) | ~spl8_7),
% 3.01/0.81    inference(avatar_component_clause,[],[f860])).
% 3.01/0.81  fof(f33,plain,(
% 3.01/0.81    ( ! [X2,X0,X1] : (k2_zfmisc_1(X0,X1) = X2 | sK2(X0,X1,X2) = k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 3.01/0.81    inference(cnf_transformation,[],[f20])).
% 3.01/0.81  fof(f20,plain,(
% 3.01/0.81    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK2(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((sK2(X0,X1,X2) = k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) & r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8 & r2_hidden(sK6(X0,X1,X8),X1) & r2_hidden(sK5(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.01/0.81    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f16,f19,f18,f17])).
% 3.01/0.81  fof(f17,plain,(
% 3.01/0.81    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK2(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK2(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 3.01/0.81    introduced(choice_axiom,[])).
% 3.01/0.81  fof(f18,plain,(
% 3.01/0.81    ! [X2,X1,X0] : (? [X7,X6] : (k4_tarski(X6,X7) = sK2(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (sK2(X0,X1,X2) = k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) & r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)))),
% 3.01/0.81    introduced(choice_axiom,[])).
% 3.01/0.81  fof(f19,plain,(
% 3.01/0.81    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8 & r2_hidden(sK6(X0,X1,X8),X1) & r2_hidden(sK5(X0,X1,X8),X0)))),
% 3.01/0.81    introduced(choice_axiom,[])).
% 3.01/0.81  fof(f16,plain,(
% 3.01/0.81    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.01/0.81    inference(rectify,[],[f15])).
% 3.01/0.81  fof(f15,plain,(
% 3.01/0.81    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.01/0.81    inference(nnf_transformation,[],[f9])).
% 3.01/0.81  fof(f9,axiom,(
% 3.01/0.81    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 3.01/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 3.01/0.81  fof(f913,plain,(
% 3.01/0.81    spl8_2 | ~spl8_3),
% 3.01/0.81    inference(avatar_contradiction_clause,[],[f912])).
% 3.01/0.81  fof(f912,plain,(
% 3.01/0.81    $false | (spl8_2 | ~spl8_3)),
% 3.01/0.81    inference(subsumption_resolution,[],[f910,f642])).
% 3.01/0.81  fof(f910,plain,(
% 3.01/0.81    k4_tarski(sK0,sK1) = sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))) | ~spl8_3),
% 3.01/0.81    inference(duplicate_literal_removal,[],[f885])).
% 3.01/0.81  fof(f885,plain,(
% 3.01/0.81    k4_tarski(sK0,sK1) = sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))) | k4_tarski(sK0,sK1) = sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))) | ~spl8_3),
% 3.01/0.81    inference(resolution,[],[f754,f52])).
% 3.01/0.81  fof(f52,plain,(
% 3.01/0.81    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_tarski(X0,X1))) )),
% 3.01/0.81    inference(equality_resolution,[],[f36])).
% 3.01/0.81  fof(f36,plain,(
% 3.01/0.81    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 3.01/0.81    inference(cnf_transformation,[],[f25])).
% 3.01/0.81  fof(f25,plain,(
% 3.01/0.81    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK7(X0,X1,X2) != X1 & sK7(X0,X1,X2) != X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (sK7(X0,X1,X2) = X1 | sK7(X0,X1,X2) = X0 | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.01/0.81    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f23,f24])).
% 3.01/0.81  fof(f24,plain,(
% 3.01/0.81    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK7(X0,X1,X2) != X1 & sK7(X0,X1,X2) != X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (sK7(X0,X1,X2) = X1 | sK7(X0,X1,X2) = X0 | r2_hidden(sK7(X0,X1,X2),X2))))),
% 3.01/0.81    introduced(choice_axiom,[])).
% 3.01/0.81  fof(f23,plain,(
% 3.01/0.81    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.01/0.81    inference(rectify,[],[f22])).
% 3.01/0.81  fof(f22,plain,(
% 3.01/0.81    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.01/0.81    inference(flattening,[],[f21])).
% 3.01/0.81  fof(f21,plain,(
% 3.01/0.81    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.01/0.81    inference(nnf_transformation,[],[f1])).
% 3.01/0.81  fof(f1,axiom,(
% 3.01/0.81    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 3.01/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 3.01/0.81  fof(f754,plain,(
% 3.01/0.81    r2_hidden(sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))) | ~spl8_3),
% 3.01/0.81    inference(avatar_component_clause,[],[f752])).
% 3.01/0.81  fof(f863,plain,(
% 3.01/0.81    spl8_7 | ~spl8_6),
% 3.01/0.81    inference(avatar_split_clause,[],[f851,f821,f860])).
% 3.01/0.81  fof(f821,plain,(
% 3.01/0.81    spl8_6 <=> r2_hidden(sK4(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))),k2_tarski(sK1,sK1))),
% 3.01/0.81    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 3.01/0.81  fof(f851,plain,(
% 3.01/0.81    sK1 = sK4(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))) | ~spl8_6),
% 3.01/0.81    inference(duplicate_literal_removal,[],[f826])).
% 3.01/0.81  fof(f826,plain,(
% 3.01/0.81    sK1 = sK4(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))) | sK1 = sK4(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))) | ~spl8_6),
% 3.01/0.81    inference(resolution,[],[f823,f52])).
% 3.01/0.81  fof(f823,plain,(
% 3.01/0.81    r2_hidden(sK4(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))),k2_tarski(sK1,sK1)) | ~spl8_6),
% 3.01/0.81    inference(avatar_component_clause,[],[f821])).
% 3.01/0.81  fof(f824,plain,(
% 3.01/0.81    spl8_3 | spl8_6 | spl8_1),
% 3.01/0.81    inference(avatar_split_clause,[],[f210,f54,f821,f752])).
% 3.01/0.81  fof(f210,plain,(
% 3.01/0.81    r2_hidden(sK4(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))),k2_tarski(sK1,sK1)) | r2_hidden(sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))) | spl8_1),
% 3.01/0.81    inference(equality_resolution,[],[f65])).
% 3.01/0.81  fof(f65,plain,(
% 3.01/0.81    ( ! [X1] : (k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)) != X1 | r2_hidden(sK4(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),X1),k2_tarski(sK1,sK1)) | r2_hidden(sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),X1),X1)) ) | spl8_1),
% 3.01/0.81    inference(superposition,[],[f56,f32])).
% 3.01/0.81  fof(f32,plain,(
% 3.01/0.81    ( ! [X2,X0,X1] : (k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 3.01/0.81    inference(cnf_transformation,[],[f20])).
% 3.01/0.81  fof(f798,plain,(
% 3.01/0.81    spl8_5 | ~spl8_4),
% 3.01/0.81    inference(avatar_split_clause,[],[f786,f756,f795])).
% 3.01/0.81  fof(f756,plain,(
% 3.01/0.81    spl8_4 <=> r2_hidden(sK3(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))),k2_tarski(sK0,sK0))),
% 3.01/0.81    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 3.01/0.81  fof(f786,plain,(
% 3.01/0.81    sK0 = sK3(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))) | ~spl8_4),
% 3.01/0.81    inference(duplicate_literal_removal,[],[f761])).
% 3.01/0.81  fof(f761,plain,(
% 3.01/0.81    sK0 = sK3(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))) | sK0 = sK3(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))) | ~spl8_4),
% 3.01/0.81    inference(resolution,[],[f758,f52])).
% 3.01/0.81  fof(f758,plain,(
% 3.01/0.81    r2_hidden(sK3(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))),k2_tarski(sK0,sK0)) | ~spl8_4),
% 3.01/0.81    inference(avatar_component_clause,[],[f756])).
% 3.01/0.81  fof(f759,plain,(
% 3.01/0.81    spl8_3 | spl8_4 | spl8_1),
% 3.01/0.81    inference(avatar_split_clause,[],[f161,f54,f756,f752])).
% 3.01/0.81  fof(f161,plain,(
% 3.01/0.81    r2_hidden(sK3(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))),k2_tarski(sK0,sK0)) | r2_hidden(sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))) | spl8_1),
% 3.01/0.81    inference(equality_resolution,[],[f64])).
% 3.01/0.81  fof(f64,plain,(
% 3.01/0.81    ( ! [X0] : (k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)) != X0 | r2_hidden(sK3(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),X0),k2_tarski(sK0,sK0)) | r2_hidden(sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),X0),X0)) ) | spl8_1),
% 3.01/0.81    inference(superposition,[],[f56,f31])).
% 3.01/0.81  fof(f31,plain,(
% 3.01/0.81    ( ! [X2,X0,X1] : (k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 3.01/0.81    inference(cnf_transformation,[],[f20])).
% 3.01/0.81  fof(f643,plain,(
% 3.01/0.81    ~spl8_2 | spl8_1),
% 3.01/0.81    inference(avatar_split_clause,[],[f633,f54,f640])).
% 3.01/0.81  fof(f633,plain,(
% 3.01/0.81    k4_tarski(sK0,sK1) != sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))) | spl8_1),
% 3.01/0.81    inference(equality_resolution,[],[f608])).
% 3.01/0.81  fof(f608,plain,(
% 3.01/0.81    ( ! [X2] : (k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)) != k2_tarski(X2,k4_tarski(sK0,sK1)) | k4_tarski(sK0,sK1) != sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),k2_tarski(X2,k4_tarski(sK0,sK1)))) ) | spl8_1),
% 3.01/0.81    inference(resolution,[],[f603,f49])).
% 3.01/0.81  fof(f49,plain,(
% 3.01/0.81    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 3.01/0.81    inference(equality_resolution,[],[f48])).
% 3.01/0.81  fof(f48,plain,(
% 3.01/0.81    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 3.01/0.81    inference(equality_resolution,[],[f38])).
% 3.01/0.81  fof(f38,plain,(
% 3.01/0.81    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 3.01/0.81    inference(cnf_transformation,[],[f25])).
% 3.01/0.81  fof(f603,plain,(
% 3.01/0.81    ( ! [X0] : (~r2_hidden(k4_tarski(sK0,sK1),X0) | k4_tarski(sK0,sK1) != sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),X0) | k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)) != X0) ) | spl8_1),
% 3.01/0.81    inference(inner_rewriting,[],[f587])).
% 3.01/0.81  fof(f587,plain,(
% 3.01/0.81    ( ! [X0] : (k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)) != X0 | k4_tarski(sK0,sK1) != sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),X0) | ~r2_hidden(sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),X0),X0)) ) | spl8_1),
% 3.01/0.81    inference(resolution,[],[f241,f49])).
% 3.01/0.81  fof(f241,plain,(
% 3.01/0.81    ( ! [X0,X1] : (~r2_hidden(X0,k2_tarski(sK0,sK0)) | k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)) != X1 | sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),X1) != k4_tarski(X0,sK1) | ~r2_hidden(sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),X1),X1)) ) | spl8_1),
% 3.01/0.81    inference(resolution,[],[f67,f49])).
% 3.01/0.81  fof(f67,plain,(
% 3.01/0.81    ( ! [X4,X5,X3] : (~r2_hidden(X5,k2_tarski(sK1,sK1)) | k4_tarski(X4,X5) != sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),X3) | k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)) != X3 | ~r2_hidden(X4,k2_tarski(sK0,sK0)) | ~r2_hidden(sK2(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1),X3),X3)) ) | spl8_1),
% 3.01/0.81    inference(superposition,[],[f56,f34])).
% 3.01/0.81  fof(f34,plain,(
% 3.01/0.81    ( ! [X4,X2,X0,X5,X1] : (k2_zfmisc_1(X0,X1) = X2 | k4_tarski(X4,X5) != sK2(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 3.01/0.81    inference(cnf_transformation,[],[f20])).
% 3.01/0.81  fof(f57,plain,(
% 3.01/0.81    ~spl8_1),
% 3.01/0.81    inference(avatar_split_clause,[],[f42,f54])).
% 3.01/0.81  fof(f42,plain,(
% 3.01/0.81    k2_zfmisc_1(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1)) != k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))),
% 3.01/0.81    inference(definition_unfolding,[],[f26,f35,f35,f35])).
% 3.01/0.81  fof(f35,plain,(
% 3.01/0.81    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.01/0.81    inference(cnf_transformation,[],[f2])).
% 3.01/0.81  fof(f2,axiom,(
% 3.01/0.81    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.01/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 3.01/0.81  fof(f26,plain,(
% 3.01/0.81    k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)) != k1_tarski(k4_tarski(sK0,sK1))),
% 3.01/0.81    inference(cnf_transformation,[],[f14])).
% 3.01/0.81  fof(f14,plain,(
% 3.01/0.81    k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)) != k1_tarski(k4_tarski(sK0,sK1))),
% 3.01/0.81    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).
% 3.01/0.81  fof(f13,plain,(
% 3.01/0.81    ? [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(k4_tarski(X0,X1)) => k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)) != k1_tarski(k4_tarski(sK0,sK1))),
% 3.01/0.81    introduced(choice_axiom,[])).
% 3.01/0.81  fof(f12,plain,(
% 3.01/0.81    ? [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(k4_tarski(X0,X1))),
% 3.01/0.81    inference(ennf_transformation,[],[f11])).
% 3.01/0.81  fof(f11,negated_conjecture,(
% 3.01/0.81    ~! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1))),
% 3.01/0.81    inference(negated_conjecture,[],[f10])).
% 3.01/0.81  fof(f10,conjecture,(
% 3.01/0.81    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1))),
% 3.01/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_zfmisc_1)).
% 3.01/0.81  % SZS output end Proof for theBenchmark
% 3.01/0.81  % (31260)------------------------------
% 3.01/0.81  % (31260)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.01/0.81  % (31260)Termination reason: Refutation
% 3.01/0.81  
% 3.01/0.81  % (31260)Memory used [KB]: 7291
% 3.01/0.81  % (31260)Time elapsed: 0.314 s
% 3.01/0.81  % (31260)------------------------------
% 3.01/0.81  % (31260)------------------------------
% 3.01/0.83  % (31307)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 3.01/0.83  % (31306)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 3.55/0.83  % (31309)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 3.55/0.84  % (31242)Success in time 0.464 s
%------------------------------------------------------------------------------
