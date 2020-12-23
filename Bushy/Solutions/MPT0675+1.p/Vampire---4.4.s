%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t118_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:13 EDT 2019

% Result     : Theorem 76.75s
% Output     : Refutation 76.75s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 474 expanded)
%              Number of leaves         :   23 ( 175 expanded)
%              Depth                    :   18
%              Number of atoms          :  542 (3356 expanded)
%              Number of equality atoms :  163 (1190 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12914,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f86,f93,f100,f107,f556,f599,f860,f3544,f3555,f12909,f12912,f12913])).

fof(f12913,plain,
    ( sK1 != sK4(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1)))
    | k1_funct_1(sK2,sK4(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1)))) != sK3(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1)))
    | k1_funct_1(sK2,sK1) = sK3(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1))) ),
    introduced(theory_axiom,[])).

fof(f12912,plain,
    ( sK0 != sK4(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1)))
    | k1_funct_1(sK2,sK4(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1)))) != sK3(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1)))
    | k1_funct_1(sK2,sK0) = sK3(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1))) ),
    introduced(theory_axiom,[])).

fof(f12909,plain,
    ( spl7_172
    | spl7_174
    | ~ spl7_98 ),
    inference(avatar_split_clause,[],[f12881,f3542,f12907,f12901])).

fof(f12901,plain,
    ( spl7_172
  <=> sK1 = sK4(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_172])])).

fof(f12907,plain,
    ( spl7_174
  <=> sK0 = sK4(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_174])])).

fof(f3542,plain,
    ( spl7_98
  <=> r2_hidden(sK4(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1))),k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_98])])).

fof(f12881,plain,
    ( sK0 = sK4(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1)))
    | sK1 = sK4(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1)))
    | ~ spl7_98 ),
    inference(resolution,[],[f3543,f72])).

fof(f72,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_tarski(X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK6(X0,X1,X2) != X1
              & sK6(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( sK6(X0,X1,X2) = X1
            | sK6(X0,X1,X2) = X0
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f37,f38])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK6(X0,X1,X2) != X1
            & sK6(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( sK6(X0,X1,X2) = X1
          | sK6(X0,X1,X2) = X0
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t118_funct_1.p',d2_tarski)).

fof(f3543,plain,
    ( r2_hidden(sK4(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1))),k2_tarski(sK0,sK1))
    | ~ spl7_98 ),
    inference(avatar_component_clause,[],[f3542])).

fof(f3555,plain,
    ( spl7_96
    | spl7_1
    | ~ spl7_6
    | ~ spl7_8
    | spl7_55 ),
    inference(avatar_split_clause,[],[f3554,f855,f105,f98,f77,f3535])).

fof(f3535,plain,
    ( spl7_96
  <=> k1_funct_1(sK2,sK4(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1)))) = sK3(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_96])])).

fof(f77,plain,
    ( spl7_1
  <=> k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1)) != k9_relat_1(sK2,k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f98,plain,
    ( spl7_6
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f105,plain,
    ( spl7_8
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f855,plain,
    ( spl7_55
  <=> ~ r2_hidden(sK3(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1))),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_55])])).

fof(f3554,plain,
    ( k1_funct_1(sK2,sK4(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1)))) = sK3(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1)))
    | ~ spl7_1
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_55 ),
    inference(subsumption_resolution,[],[f3553,f106])).

fof(f106,plain,
    ( v1_relat_1(sK2)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f105])).

fof(f3553,plain,
    ( k1_funct_1(sK2,sK4(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1)))) = sK3(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1)))
    | ~ v1_relat_1(sK2)
    | ~ spl7_1
    | ~ spl7_6
    | ~ spl7_55 ),
    inference(subsumption_resolution,[],[f3552,f99])).

fof(f99,plain,
    ( v1_funct_1(sK2)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f98])).

fof(f3552,plain,
    ( k1_funct_1(sK2,sK4(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1)))) = sK3(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_1
    | ~ spl7_55 ),
    inference(subsumption_resolution,[],[f3530,f78])).

fof(f78,plain,
    ( k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1)) != k9_relat_1(sK2,k2_tarski(sK0,sK1))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f3530,plain,
    ( k1_funct_1(sK2,sK4(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1)))) = sK3(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1)))
    | k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1)) = k9_relat_1(sK2,k2_tarski(sK0,sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_55 ),
    inference(resolution,[],[f856,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | k1_funct_1(X0,sK4(X0,X1,X2)) = sK3(X0,X1,X2)
      | k9_relat_1(X0,X1) = X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( k1_funct_1(X0,X4) != sK3(X0,X1,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                | ~ r2_hidden(sK3(X0,X1,X2),X2) )
              & ( ( k1_funct_1(X0,sK4(X0,X1,X2)) = sK3(X0,X1,X2)
                  & r2_hidden(sK4(X0,X1,X2),X1)
                  & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK5(X0,X1,X6)) = X6
                    & r2_hidden(sK5(X0,X1,X6),X1)
                    & r2_hidden(sK5(X0,X1,X6),k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f30,f33,f32,f31])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( k1_funct_1(X0,X4) != X3
                | ~ r2_hidden(X4,X1)
                | ~ r2_hidden(X4,k1_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( k1_funct_1(X0,X5) = X3
                & r2_hidden(X5,X1)
                & r2_hidden(X5,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( k1_funct_1(X0,X4) != sK3(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK3(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1,X2)) = X3
        & r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK5(X0,X1,X6)) = X6
        & r2_hidden(sK5(X0,X1,X6),X1)
        & r2_hidden(sK5(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( k1_funct_1(X0,X5) = X3
                      & r2_hidden(X5,X1)
                      & r2_hidden(X5,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ? [X8] :
                      ( k1_funct_1(X0,X8) = X6
                      & r2_hidden(X8,X1)
                      & r2_hidden(X8,k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) ) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t118_funct_1.p',d12_funct_1)).

fof(f856,plain,
    ( ~ r2_hidden(sK3(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1))),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1)))
    | ~ spl7_55 ),
    inference(avatar_component_clause,[],[f855])).

fof(f3544,plain,
    ( spl7_98
    | spl7_1
    | ~ spl7_6
    | ~ spl7_8
    | spl7_55 ),
    inference(avatar_split_clause,[],[f3528,f855,f105,f98,f77,f3542])).

fof(f3528,plain,
    ( r2_hidden(sK4(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1))),k2_tarski(sK0,sK1))
    | ~ spl7_1
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_55 ),
    inference(unit_resulting_resolution,[],[f106,f99,f78,f856,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | k9_relat_1(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f860,plain,
    ( ~ spl7_55
    | spl7_43
    | spl7_45 ),
    inference(avatar_split_clause,[],[f859,f597,f554,f855])).

fof(f554,plain,
    ( spl7_43
  <=> k1_funct_1(sK2,sK1) != sK3(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).

fof(f597,plain,
    ( spl7_45
  <=> k1_funct_1(sK2,sK0) != sK3(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f859,plain,
    ( ~ r2_hidden(sK3(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1))),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1)))
    | ~ spl7_43
    | ~ spl7_45 ),
    inference(forward_demodulation,[],[f826,f60])).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t118_funct_1.p',commutativity_k2_tarski)).

fof(f826,plain,
    ( ~ r2_hidden(sK3(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1))),k2_tarski(k1_funct_1(sK2,sK1),k1_funct_1(sK2,sK0)))
    | ~ spl7_43
    | ~ spl7_45 ),
    inference(unit_resulting_resolution,[],[f555,f598,f72])).

fof(f598,plain,
    ( k1_funct_1(sK2,sK0) != sK3(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1)))
    | ~ spl7_45 ),
    inference(avatar_component_clause,[],[f597])).

fof(f555,plain,
    ( k1_funct_1(sK2,sK1) != sK3(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1)))
    | ~ spl7_43 ),
    inference(avatar_component_clause,[],[f554])).

fof(f599,plain,
    ( ~ spl7_45
    | spl7_1
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f592,f105,f98,f91,f77,f597])).

fof(f91,plain,
    ( spl7_4
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f592,plain,
    ( k1_funct_1(sK2,sK0) != sK3(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1)))
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f71,f78,f317,f591])).

fof(f591,plain,
    ( ! [X4,X2,X3] :
        ( k1_funct_1(sK2,sK0) != sK3(sK2,X3,X4)
        | k9_relat_1(sK2,X3) = X4
        | ~ r2_hidden(sK5(sK2,k2_tarski(sK0,X2),k1_funct_1(sK2,sK0)),X3)
        | ~ r2_hidden(k1_funct_1(sK2,sK0),X4) )
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(inner_rewriting,[],[f590])).

fof(f590,plain,
    ( ! [X4,X2,X3] :
        ( k1_funct_1(sK2,sK0) != sK3(sK2,X3,X4)
        | k9_relat_1(sK2,X3) = X4
        | ~ r2_hidden(sK5(sK2,k2_tarski(sK0,X2),k1_funct_1(sK2,sK0)),X3)
        | ~ r2_hidden(sK3(sK2,X3,X4),X4) )
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f589,f106])).

fof(f589,plain,
    ( ! [X4,X2,X3] :
        ( k1_funct_1(sK2,sK0) != sK3(sK2,X3,X4)
        | k9_relat_1(sK2,X3) = X4
        | ~ r2_hidden(sK5(sK2,k2_tarski(sK0,X2),k1_funct_1(sK2,sK0)),X3)
        | ~ r2_hidden(sK3(sK2,X3,X4),X4)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f588,f99])).

fof(f588,plain,
    ( ! [X4,X2,X3] :
        ( k1_funct_1(sK2,sK0) != sK3(sK2,X3,X4)
        | k9_relat_1(sK2,X3) = X4
        | ~ r2_hidden(sK5(sK2,k2_tarski(sK0,X2),k1_funct_1(sK2,sK0)),X3)
        | ~ r2_hidden(sK3(sK2,X3,X4),X4)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f584,f316])).

fof(f316,plain,
    ( ! [X0] : r2_hidden(sK5(sK2,k2_tarski(sK0,X0),k1_funct_1(sK2,sK0)),k1_relat_1(sK2))
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f106,f99,f145,f67])).

fof(f67,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f145,plain,
    ( ! [X0] : r2_hidden(k1_funct_1(sK2,sK0),k9_relat_1(sK2,k2_tarski(sK0,X0)))
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f106,f99,f71,f92,f64])).

fof(f64,plain,(
    ! [X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | k1_funct_1(X0,X7) != X6
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f92,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f91])).

fof(f584,plain,
    ( ! [X4,X2,X3] :
        ( k1_funct_1(sK2,sK0) != sK3(sK2,X3,X4)
        | k9_relat_1(sK2,X3) = X4
        | ~ r2_hidden(sK5(sK2,k2_tarski(sK0,X2),k1_funct_1(sK2,sK0)),X3)
        | ~ r2_hidden(sK5(sK2,k2_tarski(sK0,X2),k1_funct_1(sK2,sK0)),k1_relat_1(sK2))
        | ~ r2_hidden(sK3(sK2,X3,X4),X4)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(superposition,[],[f53,f318])).

fof(f318,plain,
    ( ! [X0] : k1_funct_1(sK2,sK0) = k1_funct_1(sK2,sK5(sK2,k2_tarski(sK0,X0),k1_funct_1(sK2,sK0)))
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f106,f99,f145,f65])).

fof(f65,plain,(
    ! [X6,X0,X1] :
      ( ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | k1_funct_1(X0,sK5(X0,X1,X6)) = X6
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_funct_1(X0,sK5(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( k1_funct_1(X0,X4) != sK3(X0,X1,X2)
      | k9_relat_1(X0,X1) = X2
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f317,plain,
    ( ! [X0] : r2_hidden(sK5(sK2,k2_tarski(sK0,X0),k1_funct_1(sK2,sK0)),k2_tarski(sK0,X0))
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f106,f99,f145,f66])).

fof(f66,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f71,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f556,plain,
    ( ~ spl7_43
    | spl7_1
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f549,f105,f98,f84,f77,f554])).

fof(f84,plain,
    ( spl7_2
  <=> r2_hidden(sK1,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f549,plain,
    ( k1_funct_1(sK2,sK1) != sK3(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1)))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f69,f78,f281,f546])).

fof(f546,plain,
    ( ! [X4,X2,X3] :
        ( k1_funct_1(sK2,sK1) != sK3(sK2,X3,X4)
        | k9_relat_1(sK2,X3) = X4
        | ~ r2_hidden(sK5(sK2,k2_tarski(X2,sK1),k1_funct_1(sK2,sK1)),X3)
        | ~ r2_hidden(k1_funct_1(sK2,sK1),X4) )
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(inner_rewriting,[],[f545])).

fof(f545,plain,
    ( ! [X4,X2,X3] :
        ( k1_funct_1(sK2,sK1) != sK3(sK2,X3,X4)
        | k9_relat_1(sK2,X3) = X4
        | ~ r2_hidden(sK5(sK2,k2_tarski(X2,sK1),k1_funct_1(sK2,sK1)),X3)
        | ~ r2_hidden(sK3(sK2,X3,X4),X4) )
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f544,f106])).

fof(f544,plain,
    ( ! [X4,X2,X3] :
        ( k1_funct_1(sK2,sK1) != sK3(sK2,X3,X4)
        | k9_relat_1(sK2,X3) = X4
        | ~ r2_hidden(sK5(sK2,k2_tarski(X2,sK1),k1_funct_1(sK2,sK1)),X3)
        | ~ r2_hidden(sK3(sK2,X3,X4),X4)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f543,f99])).

fof(f543,plain,
    ( ! [X4,X2,X3] :
        ( k1_funct_1(sK2,sK1) != sK3(sK2,X3,X4)
        | k9_relat_1(sK2,X3) = X4
        | ~ r2_hidden(sK5(sK2,k2_tarski(X2,sK1),k1_funct_1(sK2,sK1)),X3)
        | ~ r2_hidden(sK3(sK2,X3,X4),X4)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f539,f280])).

fof(f280,plain,
    ( ! [X0] : r2_hidden(sK5(sK2,k2_tarski(X0,sK1),k1_funct_1(sK2,sK1)),k1_relat_1(sK2))
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f106,f99,f108,f67])).

fof(f108,plain,
    ( ! [X0] : r2_hidden(k1_funct_1(sK2,sK1),k9_relat_1(sK2,k2_tarski(X0,sK1)))
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f106,f99,f69,f85,f64])).

fof(f85,plain,
    ( r2_hidden(sK1,k1_relat_1(sK2))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f539,plain,
    ( ! [X4,X2,X3] :
        ( k1_funct_1(sK2,sK1) != sK3(sK2,X3,X4)
        | k9_relat_1(sK2,X3) = X4
        | ~ r2_hidden(sK5(sK2,k2_tarski(X2,sK1),k1_funct_1(sK2,sK1)),X3)
        | ~ r2_hidden(sK5(sK2,k2_tarski(X2,sK1),k1_funct_1(sK2,sK1)),k1_relat_1(sK2))
        | ~ r2_hidden(sK3(sK2,X3,X4),X4)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(superposition,[],[f53,f282])).

fof(f282,plain,
    ( ! [X0] : k1_funct_1(sK2,sK1) = k1_funct_1(sK2,sK5(sK2,k2_tarski(X0,sK1),k1_funct_1(sK2,sK1)))
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f106,f99,f108,f65])).

fof(f281,plain,
    ( ! [X0] : r2_hidden(sK5(sK2,k2_tarski(X0,sK1),k1_funct_1(sK2,sK1)),k2_tarski(X0,sK1))
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f106,f99,f108,f66])).

fof(f69,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f107,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f40,f105])).

fof(f40,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1)) != k9_relat_1(sK2,k2_tarski(sK0,sK1))
    & r2_hidden(sK1,k1_relat_1(sK2))
    & r2_hidden(sK0,k1_relat_1(sK2))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f27])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) != k9_relat_1(X2,k2_tarski(X0,X1))
        & r2_hidden(X1,k1_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1)) != k9_relat_1(sK2,k2_tarski(sK0,sK1))
      & r2_hidden(sK1,k1_relat_1(sK2))
      & r2_hidden(sK0,k1_relat_1(sK2))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) != k9_relat_1(X2,k2_tarski(X0,X1))
      & r2_hidden(X1,k1_relat_1(X2))
      & r2_hidden(X0,k1_relat_1(X2))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) != k9_relat_1(X2,k2_tarski(X0,X1))
      & r2_hidden(X1,k1_relat_1(X2))
      & r2_hidden(X0,k1_relat_1(X2))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r2_hidden(X1,k1_relat_1(X2))
            & r2_hidden(X0,k1_relat_1(X2)) )
         => k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r2_hidden(X1,k1_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) )
       => k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t118_funct_1.p',t118_funct_1)).

fof(f100,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f41,f98])).

fof(f41,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f93,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f42,f91])).

fof(f42,plain,(
    r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f28])).

fof(f86,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f43,f84])).

fof(f43,plain,(
    r2_hidden(sK1,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f28])).

fof(f79,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f44,f77])).

fof(f44,plain,(
    k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1)) != k9_relat_1(sK2,k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
