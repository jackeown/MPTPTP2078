%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   62 (  88 expanded)
%              Number of leaves         :   18 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :  223 ( 299 expanded)
%              Number of equality atoms :   16 (  16 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f130,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f73,f75,f113,f124,f129])).

fof(f129,plain,
    ( ~ spl10_2
    | spl10_8 ),
    inference(avatar_contradiction_clause,[],[f125])).

fof(f125,plain,
    ( $false
    | ~ spl10_2
    | spl10_8 ),
    inference(resolution,[],[f112,f92])).

fof(f92,plain,
    ( r2_hidden(sK2(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),k2_relat_1(sK0))
    | ~ spl10_2 ),
    inference(resolution,[],[f67,f47])).

fof(f47,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0)
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0)
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f22,f25,f24,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0)
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0)
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f67,plain,
    ( r2_hidden(k4_tarski(sK1(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),sK2(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),sK0)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl10_2
  <=> r2_hidden(k4_tarski(sK1(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),sK2(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f112,plain,
    ( ~ r2_hidden(sK2(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),k2_relat_1(sK0))
    | spl10_8 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl10_8
  <=> r2_hidden(sK2(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f124,plain,
    ( ~ spl10_2
    | spl10_7 ),
    inference(avatar_contradiction_clause,[],[f120])).

fof(f120,plain,
    ( $false
    | ~ spl10_2
    | spl10_7 ),
    inference(resolution,[],[f108,f93])).

fof(f93,plain,
    ( r2_hidden(sK1(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),k1_relat_1(sK0))
    | ~ spl10_2 ),
    inference(resolution,[],[f67,f45])).

fof(f45,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f16,f19,f18,f17])).

fof(f17,plain,(
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

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
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
    inference(rectify,[],[f15])).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f108,plain,
    ( ~ r2_hidden(sK1(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),k1_relat_1(sK0))
    | spl10_7 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl10_7
  <=> r2_hidden(sK1(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f113,plain,
    ( ~ spl10_7
    | ~ spl10_8
    | spl10_3 ),
    inference(avatar_split_clause,[],[f101,f70,f110,f106])).

fof(f70,plain,
    ( spl10_3
  <=> r2_hidden(k4_tarski(sK1(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),sK2(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f101,plain,
    ( ~ r2_hidden(sK2(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),k2_relat_1(sK0))
    | ~ r2_hidden(sK1(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),k1_relat_1(sK0))
    | spl10_3 ),
    inference(resolution,[],[f72,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f72,plain,
    ( ~ r2_hidden(k4_tarski(sK1(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),sK2(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | spl10_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f75,plain,(
    spl10_1 ),
    inference(avatar_contradiction_clause,[],[f74])).

fof(f74,plain,
    ( $false
    | spl10_1 ),
    inference(resolution,[],[f63,f29])).

fof(f29,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( ~ r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f9])).

fof(f9,plain,
    ( ? [X0] :
        ( ~ r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
        & v1_relat_1(X0) )
   => ( ~ r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(f63,plain,
    ( ~ v1_relat_1(sK0)
    | spl10_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl10_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f73,plain,
    ( ~ spl10_1
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f59,f70,f61])).

fof(f59,plain,
    ( ~ r2_hidden(k4_tarski(sK1(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),sK2(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f30,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f12,f13])).

fof(f13,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
                | ~ r2_hidden(k4_tarski(X2,X3),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

fof(f30,plain,(
    ~ r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f68,plain,
    ( ~ spl10_1
    | spl10_2 ),
    inference(avatar_split_clause,[],[f58,f65,f61])).

fof(f58,plain,
    ( r2_hidden(k4_tarski(sK1(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),sK2(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f30,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:08:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.44  % (32301)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.44  % (32301)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f130,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f68,f73,f75,f113,f124,f129])).
% 0.21/0.44  fof(f129,plain,(
% 0.21/0.44    ~spl10_2 | spl10_8),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f125])).
% 0.21/0.44  fof(f125,plain,(
% 0.21/0.44    $false | (~spl10_2 | spl10_8)),
% 0.21/0.44    inference(resolution,[],[f112,f92])).
% 0.21/0.44  fof(f92,plain,(
% 0.21/0.44    r2_hidden(sK2(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),k2_relat_1(sK0)) | ~spl10_2),
% 0.21/0.44    inference(resolution,[],[f67,f47])).
% 0.21/0.44  fof(f47,plain,(
% 0.21/0.44    ( ! [X6,X0,X5] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0)) )),
% 0.21/0.44    inference(equality_resolution,[],[f39])).
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 0.21/0.44    inference(cnf_transformation,[],[f26])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f22,f25,f24,f23])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1))))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0) => r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK8(X0,X5),X5),X0))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.21/0.44    inference(rectify,[],[f21])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 0.21/0.44    inference(nnf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 0.21/0.44  fof(f67,plain,(
% 0.21/0.44    r2_hidden(k4_tarski(sK1(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),sK2(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),sK0) | ~spl10_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f65])).
% 0.21/0.44  fof(f65,plain,(
% 0.21/0.44    spl10_2 <=> r2_hidden(k4_tarski(sK1(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),sK2(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.21/0.44  fof(f112,plain,(
% 0.21/0.44    ~r2_hidden(sK2(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),k2_relat_1(sK0)) | spl10_8),
% 0.21/0.44    inference(avatar_component_clause,[],[f110])).
% 0.21/0.44  fof(f110,plain,(
% 0.21/0.44    spl10_8 <=> r2_hidden(sK2(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),k2_relat_1(sK0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 0.21/0.44  fof(f124,plain,(
% 0.21/0.44    ~spl10_2 | spl10_7),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f120])).
% 0.21/0.44  fof(f120,plain,(
% 0.21/0.44    $false | (~spl10_2 | spl10_7)),
% 0.21/0.44    inference(resolution,[],[f108,f93])).
% 0.21/0.44  fof(f93,plain,(
% 0.21/0.44    r2_hidden(sK1(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),k1_relat_1(sK0)) | ~spl10_2),
% 0.21/0.44    inference(resolution,[],[f67,f45])).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 0.21/0.44    inference(equality_resolution,[],[f35])).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 0.21/0.44    inference(cnf_transformation,[],[f20])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f16,f19,f18,f17])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.21/0.44    inference(rectify,[],[f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 0.21/0.45    inference(nnf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 0.21/0.45  fof(f108,plain,(
% 0.21/0.45    ~r2_hidden(sK1(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),k1_relat_1(sK0)) | spl10_7),
% 0.21/0.45    inference(avatar_component_clause,[],[f106])).
% 0.21/0.45  fof(f106,plain,(
% 0.21/0.45    spl10_7 <=> r2_hidden(sK1(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),k1_relat_1(sK0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.21/0.45  fof(f113,plain,(
% 0.21/0.45    ~spl10_7 | ~spl10_8 | spl10_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f101,f70,f110,f106])).
% 0.21/0.45  fof(f70,plain,(
% 0.21/0.45    spl10_3 <=> r2_hidden(k4_tarski(sK1(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),sK2(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.21/0.45  fof(f101,plain,(
% 0.21/0.45    ~r2_hidden(sK2(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),k2_relat_1(sK0)) | ~r2_hidden(sK1(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),k1_relat_1(sK0)) | spl10_3),
% 0.21/0.45    inference(resolution,[],[f72,f44])).
% 0.21/0.45  fof(f44,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f28])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.21/0.45    inference(flattening,[],[f27])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.21/0.45    inference(nnf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.21/0.45  fof(f72,plain,(
% 0.21/0.45    ~r2_hidden(k4_tarski(sK1(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),sK2(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) | spl10_3),
% 0.21/0.45    inference(avatar_component_clause,[],[f70])).
% 0.21/0.45  fof(f75,plain,(
% 0.21/0.45    spl10_1),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f74])).
% 0.21/0.45  fof(f74,plain,(
% 0.21/0.45    $false | spl10_1),
% 0.21/0.45    inference(resolution,[],[f63,f29])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    v1_relat_1(sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f10])).
% 0.21/0.45  fof(f10,plain,(
% 0.21/0.45    ~r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) & v1_relat_1(sK0)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f9])).
% 0.21/0.45  fof(f9,plain,(
% 0.21/0.45    ? [X0] : (~r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) & v1_relat_1(X0)) => (~r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) & v1_relat_1(sK0))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f7,plain,(
% 0.21/0.45    ? [X0] : (~r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) & v1_relat_1(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,negated_conjecture,(
% 0.21/0.45    ~! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.21/0.45    inference(negated_conjecture,[],[f5])).
% 0.21/0.45  fof(f5,conjecture,(
% 0.21/0.45    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).
% 0.21/0.45  fof(f63,plain,(
% 0.21/0.45    ~v1_relat_1(sK0) | spl10_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f61])).
% 0.21/0.45  fof(f61,plain,(
% 0.21/0.45    spl10_1 <=> v1_relat_1(sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.21/0.45  fof(f73,plain,(
% 0.21/0.45    ~spl10_1 | ~spl10_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f59,f70,f61])).
% 0.21/0.45  fof(f59,plain,(
% 0.21/0.45    ~r2_hidden(k4_tarski(sK1(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),sK2(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) | ~v1_relat_1(sK0)),
% 0.21/0.45    inference(resolution,[],[f30,f33])).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) | ~v1_relat_1(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f14])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | (~r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) & r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f12,f13])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0)) => (~r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) & r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 0.21/0.45    inference(rectify,[],[f11])).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 0.21/0.45    inference(nnf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    ~r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),
% 0.21/0.45    inference(cnf_transformation,[],[f10])).
% 0.21/0.45  fof(f68,plain,(
% 0.21/0.45    ~spl10_1 | spl10_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f58,f65,f61])).
% 0.21/0.45  fof(f58,plain,(
% 0.21/0.45    r2_hidden(k4_tarski(sK1(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),sK2(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),sK0) | ~v1_relat_1(sK0)),
% 0.21/0.45    inference(resolution,[],[f30,f32])).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | ~v1_relat_1(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f14])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (32301)------------------------------
% 0.21/0.45  % (32301)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (32301)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (32301)Memory used [KB]: 6140
% 0.21/0.45  % (32301)Time elapsed: 0.007 s
% 0.21/0.45  % (32301)------------------------------
% 0.21/0.45  % (32301)------------------------------
% 0.21/0.45  % (32284)Success in time 0.087 s
%------------------------------------------------------------------------------
