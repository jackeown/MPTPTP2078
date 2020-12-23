%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:20 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 183 expanded)
%              Number of leaves         :   26 (  78 expanded)
%              Depth                    :   10
%              Number of atoms          :  442 ( 829 expanded)
%              Number of equality atoms :   39 (  88 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f773,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f129,f133,f155,f167,f306,f311,f327,f492,f529,f534,f554,f765])).

fof(f765,plain,
    ( ~ spl12_37
    | ~ spl12_9
    | ~ spl12_36 ),
    inference(avatar_split_clause,[],[f753,f526,f165,f531])).

fof(f531,plain,
    ( spl12_37
  <=> r2_hidden(sK10(sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_37])])).

fof(f165,plain,
    ( spl12_9
  <=> ! [X1] :
        ( ~ r2_hidden(X1,sK0)
        | ~ r2_hidden(k4_tarski(X1,sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_9])])).

fof(f526,plain,
    ( spl12_36
  <=> r2_hidden(k4_tarski(sK10(sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),sK0,sK1),sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_36])])).

fof(f753,plain,
    ( ~ r2_hidden(sK10(sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),sK0,sK1),sK0)
    | ~ spl12_9
    | ~ spl12_36 ),
    inference(resolution,[],[f528,f166])).

fof(f166,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k4_tarski(X1,sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),sK1)
        | ~ r2_hidden(X1,sK0) )
    | ~ spl12_9 ),
    inference(avatar_component_clause,[],[f165])).

fof(f528,plain,
    ( r2_hidden(k4_tarski(sK10(sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),sK0,sK1),sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),sK1)
    | ~ spl12_36 ),
    inference(avatar_component_clause,[],[f526])).

fof(f554,plain,
    ( ~ spl12_1
    | ~ spl12_20
    | spl12_9
    | ~ spl12_7 ),
    inference(avatar_split_clause,[],[f547,f131,f165,f299,f104])).

fof(f104,plain,
    ( spl12_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f299,plain,
    ( spl12_20
  <=> v1_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_20])])).

fof(f131,plain,
    ( spl12_7
  <=> ! [X0] : ~ r2_hidden(k4_tarski(X0,sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).

fof(f547,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),sK1)
        | ~ r2_hidden(X0,sK0)
        | ~ v1_relat_1(k7_relat_1(sK1,sK0))
        | ~ v1_relat_1(sK1) )
    | ~ spl12_7 ),
    inference(resolution,[],[f132,f59])).

fof(f59,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0)
                  | ~ r2_hidden(sK2(X0,X1,X2),X1)
                  | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0)
                    & r2_hidden(sK2(X0,X1,X2),X1) )
                  | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f17,f18])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0)
            & r2_hidden(sK2(X0,X1,X2),X1) )
          | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_relat_1)).

fof(f132,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),k7_relat_1(sK1,sK0))
    | ~ spl12_7 ),
    inference(avatar_component_clause,[],[f131])).

fof(f534,plain,
    ( ~ spl12_1
    | spl12_37
    | ~ spl12_5 ),
    inference(avatar_split_clause,[],[f514,f122,f531,f104])).

fof(f122,plain,
    ( spl12_5
  <=> r2_hidden(sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),k9_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).

fof(f514,plain,
    ( r2_hidden(sK10(sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),sK0,sK1),sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl12_5 ),
    inference(resolution,[],[f124,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK10(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK10(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK10(X0,X1,X2),X0),X2)
            & r2_hidden(sK10(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f33,f34])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK10(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK10(X0,X1,X2),X0),X2)
        & r2_hidden(sK10(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f124,plain,
    ( r2_hidden(sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),k9_relat_1(sK1,sK0))
    | ~ spl12_5 ),
    inference(avatar_component_clause,[],[f122])).

fof(f529,plain,
    ( ~ spl12_1
    | spl12_36
    | ~ spl12_5 ),
    inference(avatar_split_clause,[],[f513,f122,f526,f104])).

fof(f513,plain,
    ( r2_hidden(k4_tarski(sK10(sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),sK0,sK1),sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl12_5 ),
    inference(resolution,[],[f124,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK10(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f492,plain,
    ( ~ spl12_21
    | ~ spl12_9
    | ~ spl12_22 ),
    inference(avatar_split_clause,[],[f481,f308,f165,f303])).

fof(f303,plain,
    ( spl12_21
  <=> r2_hidden(sK8(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_21])])).

fof(f308,plain,
    ( spl12_22
  <=> r2_hidden(k4_tarski(sK8(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_22])])).

fof(f481,plain,
    ( ~ r2_hidden(sK8(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),sK0)
    | ~ spl12_9
    | ~ spl12_22 ),
    inference(resolution,[],[f310,f166])).

fof(f310,plain,
    ( r2_hidden(k4_tarski(sK8(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),sK1)
    | ~ spl12_22 ),
    inference(avatar_component_clause,[],[f308])).

fof(f327,plain,(
    spl12_20 ),
    inference(avatar_contradiction_clause,[],[f325])).

fof(f325,plain,
    ( $false
    | spl12_20 ),
    inference(resolution,[],[f301,f78])).

fof(f78,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(resolution,[],[f36,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f36,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( k2_relat_1(k7_relat_1(sK1,sK0)) != k9_relat_1(sK1,sK0)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f13])).

fof(f13,plain,
    ( ? [X0,X1] :
        ( k2_relat_1(k7_relat_1(X1,X0)) != k9_relat_1(X1,X0)
        & v1_relat_1(X1) )
   => ( k2_relat_1(k7_relat_1(sK1,sK0)) != k9_relat_1(sK1,sK0)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) != k9_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f301,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | spl12_20 ),
    inference(avatar_component_clause,[],[f299])).

fof(f311,plain,
    ( ~ spl12_1
    | ~ spl12_20
    | spl12_22
    | ~ spl12_6 ),
    inference(avatar_split_clause,[],[f290,f126,f308,f299,f104])).

fof(f126,plain,
    ( spl12_6
  <=> r2_hidden(k4_tarski(sK8(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).

fof(f290,plain,
    ( r2_hidden(k4_tarski(sK8(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),sK1)
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl12_6 ),
    inference(resolution,[],[f128,f60])).

fof(f60,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f128,plain,
    ( r2_hidden(k4_tarski(sK8(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),k7_relat_1(sK1,sK0))
    | ~ spl12_6 ),
    inference(avatar_component_clause,[],[f126])).

fof(f306,plain,
    ( ~ spl12_1
    | ~ spl12_20
    | spl12_21
    | ~ spl12_6 ),
    inference(avatar_split_clause,[],[f289,f126,f303,f299,f104])).

fof(f289,plain,
    ( r2_hidden(sK8(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),sK0)
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl12_6 ),
    inference(resolution,[],[f128,f61])).

fof(f61,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f167,plain,
    ( ~ spl12_1
    | spl12_9
    | spl12_5 ),
    inference(avatar_split_clause,[],[f158,f122,f165,f104])).

fof(f158,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK0)
        | ~ r2_hidden(k4_tarski(X1,sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),sK1)
        | ~ v1_relat_1(sK1) )
    | spl12_5 ),
    inference(resolution,[],[f123,f62])).

fof(f62,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(X4,sK4(X0,X1,X2)),X0) )
                | ~ r2_hidden(sK4(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK5(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X0) )
                | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ( r2_hidden(sK6(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(sK6(X0,X1,X6),X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f21,f24,f23,f22])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X4,X3),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X5,X3),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(X4,sK4(X0,X1,X2)),X0) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X0) )
     => ( r2_hidden(sK5(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X8,X6),X0) )
     => ( r2_hidden(sK6(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(sK6(X0,X1,X6),X6),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X5,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X8,X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).

fof(f123,plain,
    ( ~ r2_hidden(sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),k9_relat_1(sK1,sK0))
    | spl12_5 ),
    inference(avatar_component_clause,[],[f122])).

fof(f155,plain,(
    spl12_1 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | spl12_1 ),
    inference(resolution,[],[f106,f36])).

fof(f106,plain,
    ( ~ v1_relat_1(sK1)
    | spl12_1 ),
    inference(avatar_component_clause,[],[f104])).

fof(f133,plain,
    ( ~ spl12_5
    | spl12_7 ),
    inference(avatar_split_clause,[],[f120,f131,f122])).

fof(f120,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(X0,sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),k7_relat_1(sK1,sK0))
      | ~ r2_hidden(sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),k9_relat_1(sK1,sK0)) ) ),
    inference(resolution,[],[f68,f75])).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( sQ11_eqProxy(k2_relat_1(X0),X1)
      | ~ r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0)
      | ~ r2_hidden(sK7(X0,X1),X1) ) ),
    inference(equality_proxy_replacement,[],[f54,f67])).

fof(f67,plain,(
    ! [X1,X0] :
      ( sQ11_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ11_eqProxy])])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( k2_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0)
      | ~ r2_hidden(sK7(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0)
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0)
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK9(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f27,f30,f29,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0)
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK7(X0,X1)),X0)
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK7(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK9(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f68,plain,(
    ~ sQ11_eqProxy(k2_relat_1(k7_relat_1(sK1,sK0)),k9_relat_1(sK1,sK0)) ),
    inference(equality_proxy_replacement,[],[f37,f67])).

fof(f37,plain,(
    k2_relat_1(k7_relat_1(sK1,sK0)) != k9_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f129,plain,
    ( spl12_5
    | spl12_6 ),
    inference(avatar_split_clause,[],[f119,f126,f122])).

fof(f119,plain,
    ( r2_hidden(k4_tarski(sK8(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),k7_relat_1(sK1,sK0))
    | r2_hidden(sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),k9_relat_1(sK1,sK0)) ),
    inference(resolution,[],[f68,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( sQ11_eqProxy(k2_relat_1(X0),X1)
      | r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0)
      | r2_hidden(sK7(X0,X1),X1) ) ),
    inference(equality_proxy_replacement,[],[f53,f67])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0)
      | r2_hidden(sK7(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:23:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (2609)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.47  % (2601)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.47  % (2612)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.50  % (2610)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.50  % (2600)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  % (2610)Refutation not found, incomplete strategy% (2610)------------------------------
% 0.22/0.50  % (2610)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (2610)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (2610)Memory used [KB]: 1663
% 0.22/0.50  % (2610)Time elapsed: 0.076 s
% 0.22/0.50  % (2610)------------------------------
% 0.22/0.50  % (2610)------------------------------
% 0.22/0.50  % (2603)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (2602)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (2599)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.50  % (2598)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (2597)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (2611)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.51  % (2598)Refutation not found, incomplete strategy% (2598)------------------------------
% 0.22/0.51  % (2598)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (2598)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (2598)Memory used [KB]: 10618
% 0.22/0.51  % (2598)Time elapsed: 0.085 s
% 0.22/0.51  % (2598)------------------------------
% 0.22/0.51  % (2598)------------------------------
% 0.22/0.51  % (2609)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f773,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f129,f133,f155,f167,f306,f311,f327,f492,f529,f534,f554,f765])).
% 0.22/0.51  fof(f765,plain,(
% 0.22/0.51    ~spl12_37 | ~spl12_9 | ~spl12_36),
% 0.22/0.51    inference(avatar_split_clause,[],[f753,f526,f165,f531])).
% 0.22/0.51  fof(f531,plain,(
% 0.22/0.51    spl12_37 <=> r2_hidden(sK10(sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),sK0,sK1),sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl12_37])])).
% 0.22/0.51  fof(f165,plain,(
% 0.22/0.51    spl12_9 <=> ! [X1] : (~r2_hidden(X1,sK0) | ~r2_hidden(k4_tarski(X1,sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),sK1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl12_9])])).
% 0.22/0.51  fof(f526,plain,(
% 0.22/0.51    spl12_36 <=> r2_hidden(k4_tarski(sK10(sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),sK0,sK1),sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl12_36])])).
% 0.22/0.51  fof(f753,plain,(
% 0.22/0.51    ~r2_hidden(sK10(sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),sK0,sK1),sK0) | (~spl12_9 | ~spl12_36)),
% 0.22/0.51    inference(resolution,[],[f528,f166])).
% 0.22/0.51  fof(f166,plain,(
% 0.22/0.51    ( ! [X1] : (~r2_hidden(k4_tarski(X1,sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),sK1) | ~r2_hidden(X1,sK0)) ) | ~spl12_9),
% 0.22/0.51    inference(avatar_component_clause,[],[f165])).
% 0.22/0.51  fof(f528,plain,(
% 0.22/0.51    r2_hidden(k4_tarski(sK10(sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),sK0,sK1),sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),sK1) | ~spl12_36),
% 0.22/0.51    inference(avatar_component_clause,[],[f526])).
% 0.22/0.51  fof(f554,plain,(
% 0.22/0.51    ~spl12_1 | ~spl12_20 | spl12_9 | ~spl12_7),
% 0.22/0.51    inference(avatar_split_clause,[],[f547,f131,f165,f299,f104])).
% 0.22/0.51  fof(f104,plain,(
% 0.22/0.51    spl12_1 <=> v1_relat_1(sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).
% 0.22/0.51  fof(f299,plain,(
% 0.22/0.51    spl12_20 <=> v1_relat_1(k7_relat_1(sK1,sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl12_20])])).
% 0.22/0.51  fof(f131,plain,(
% 0.22/0.51    spl12_7 <=> ! [X0] : ~r2_hidden(k4_tarski(X0,sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),k7_relat_1(sK1,sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).
% 0.22/0.51  fof(f547,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),sK1) | ~r2_hidden(X0,sK0) | ~v1_relat_1(k7_relat_1(sK1,sK0)) | ~v1_relat_1(sK1)) ) | ~spl12_7),
% 0.22/0.51    inference(resolution,[],[f132,f59])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    ( ! [X6,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(equality_resolution,[],[f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1) | k7_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0) | ~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0) & r2_hidden(sK2(X0,X1,X2),X1)) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1)) & ((r2_hidden(k4_tarski(X5,X6),X0) & r2_hidden(X5,X1)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f17,f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X2,X1,X0] : (? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0) | ~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0) & r2_hidden(sK2(X0,X1,X2),X1)) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1)) & ((r2_hidden(k4_tarski(X5,X6),X0) & r2_hidden(X5,X1)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(rectify,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(flattening,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : (((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | (~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1))) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,plain,(
% 0.22/0.51    ! [X0] : (! [X1,X2] : ((k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (v1_relat_1(X2) => (k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_relat_1)).
% 0.22/0.51  fof(f132,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),k7_relat_1(sK1,sK0))) ) | ~spl12_7),
% 0.22/0.51    inference(avatar_component_clause,[],[f131])).
% 0.22/0.51  fof(f534,plain,(
% 0.22/0.51    ~spl12_1 | spl12_37 | ~spl12_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f514,f122,f531,f104])).
% 0.22/0.51  fof(f122,plain,(
% 0.22/0.51    spl12_5 <=> r2_hidden(sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),k9_relat_1(sK1,sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).
% 0.22/0.51  fof(f514,plain,(
% 0.22/0.51    r2_hidden(sK10(sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),sK0,sK1),sK0) | ~v1_relat_1(sK1) | ~spl12_5),
% 0.22/0.51    inference(resolution,[],[f124,f57])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (r2_hidden(sK10(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK10(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK10(X0,X1,X2),X0),X2) & r2_hidden(sK10(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f33,f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK10(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK10(X0,X1,X2),X0),X2) & r2_hidden(sK10(X0,X1,X2),k1_relat_1(X2))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.51    inference(rectify,[],[f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.51    inference(nnf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 0.22/0.51  fof(f124,plain,(
% 0.22/0.51    r2_hidden(sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),k9_relat_1(sK1,sK0)) | ~spl12_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f122])).
% 0.22/0.51  fof(f529,plain,(
% 0.22/0.51    ~spl12_1 | spl12_36 | ~spl12_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f513,f122,f526,f104])).
% 0.22/0.51  fof(f513,plain,(
% 0.22/0.51    r2_hidden(k4_tarski(sK10(sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),sK0,sK1),sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),sK1) | ~v1_relat_1(sK1) | ~spl12_5),
% 0.22/0.51    inference(resolution,[],[f124,f56])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK10(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  fof(f492,plain,(
% 0.22/0.51    ~spl12_21 | ~spl12_9 | ~spl12_22),
% 0.22/0.51    inference(avatar_split_clause,[],[f481,f308,f165,f303])).
% 0.22/0.51  fof(f303,plain,(
% 0.22/0.51    spl12_21 <=> r2_hidden(sK8(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl12_21])])).
% 0.22/0.51  fof(f308,plain,(
% 0.22/0.51    spl12_22 <=> r2_hidden(k4_tarski(sK8(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl12_22])])).
% 0.22/0.51  fof(f481,plain,(
% 0.22/0.51    ~r2_hidden(sK8(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),sK0) | (~spl12_9 | ~spl12_22)),
% 0.22/0.51    inference(resolution,[],[f310,f166])).
% 0.22/0.51  fof(f310,plain,(
% 0.22/0.51    r2_hidden(k4_tarski(sK8(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),sK1) | ~spl12_22),
% 0.22/0.51    inference(avatar_component_clause,[],[f308])).
% 0.22/0.51  fof(f327,plain,(
% 0.22/0.51    spl12_20),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f325])).
% 0.22/0.51  fof(f325,plain,(
% 0.22/0.51    $false | spl12_20),
% 0.22/0.51    inference(resolution,[],[f301,f78])).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0))) )),
% 0.22/0.51    inference(resolution,[],[f36,f50])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    v1_relat_1(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    k2_relat_1(k7_relat_1(sK1,sK0)) != k9_relat_1(sK1,sK0) & v1_relat_1(sK1)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ? [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) != k9_relat_1(X1,X0) & v1_relat_1(X1)) => (k2_relat_1(k7_relat_1(sK1,sK0)) != k9_relat_1(sK1,sK0) & v1_relat_1(sK1))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f8,plain,(
% 0.22/0.51    ? [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) != k9_relat_1(X1,X0) & v1_relat_1(X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.22/0.51    inference(negated_conjecture,[],[f6])).
% 0.22/0.51  fof(f6,conjecture,(
% 0.22/0.51    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.51  fof(f301,plain,(
% 0.22/0.51    ~v1_relat_1(k7_relat_1(sK1,sK0)) | spl12_20),
% 0.22/0.51    inference(avatar_component_clause,[],[f299])).
% 0.22/0.51  fof(f311,plain,(
% 0.22/0.51    ~spl12_1 | ~spl12_20 | spl12_22 | ~spl12_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f290,f126,f308,f299,f104])).
% 0.22/0.51  fof(f126,plain,(
% 0.22/0.51    spl12_6 <=> r2_hidden(k4_tarski(sK8(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),k7_relat_1(sK1,sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).
% 0.22/0.51  fof(f290,plain,(
% 0.22/0.51    r2_hidden(k4_tarski(sK8(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),sK1) | ~v1_relat_1(k7_relat_1(sK1,sK0)) | ~v1_relat_1(sK1) | ~spl12_6),
% 0.22/0.51    inference(resolution,[],[f128,f60])).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    ( ! [X6,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1)) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(equality_resolution,[],[f39])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X5,X6),X2) | k7_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f128,plain,(
% 0.22/0.51    r2_hidden(k4_tarski(sK8(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),k7_relat_1(sK1,sK0)) | ~spl12_6),
% 0.22/0.51    inference(avatar_component_clause,[],[f126])).
% 0.22/0.51  fof(f306,plain,(
% 0.22/0.51    ~spl12_1 | ~spl12_20 | spl12_21 | ~spl12_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f289,f126,f303,f299,f104])).
% 0.22/0.51  fof(f289,plain,(
% 0.22/0.51    r2_hidden(sK8(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),sK0) | ~v1_relat_1(k7_relat_1(sK1,sK0)) | ~v1_relat_1(sK1) | ~spl12_6),
% 0.22/0.51    inference(resolution,[],[f128,f61])).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1)) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(equality_resolution,[],[f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X2) | k7_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f167,plain,(
% 0.22/0.51    ~spl12_1 | spl12_9 | spl12_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f158,f122,f165,f104])).
% 0.22/0.51  fof(f158,plain,(
% 0.22/0.51    ( ! [X1] : (~r2_hidden(X1,sK0) | ~r2_hidden(k4_tarski(X1,sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),sK1) | ~v1_relat_1(sK1)) ) | spl12_5),
% 0.22/0.51    inference(resolution,[],[f123,f62])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    ( ! [X6,X0,X7,X1] : (r2_hidden(X6,k9_relat_1(X0,X1)) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(equality_resolution,[],[f46])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0) | k9_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,sK4(X0,X1,X2)),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0))) & ((r2_hidden(sK6(X0,X1,X6),X1) & r2_hidden(k4_tarski(sK6(X0,X1,X6),X6),X0)) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f21,f24,f23,f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X3),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,sK4(X0,X1,X2)),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X0)) => (r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X0)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X8,X6),X0)) => (r2_hidden(sK6(X0,X1,X6),X1) & r2_hidden(k4_tarski(sK6(X0,X1,X6),X6),X0)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X3),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X8,X6),X0)) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(rectify,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).
% 0.22/0.51  fof(f123,plain,(
% 0.22/0.51    ~r2_hidden(sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),k9_relat_1(sK1,sK0)) | spl12_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f122])).
% 0.22/0.51  fof(f155,plain,(
% 0.22/0.51    spl12_1),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f154])).
% 0.22/0.51  fof(f154,plain,(
% 0.22/0.51    $false | spl12_1),
% 0.22/0.51    inference(resolution,[],[f106,f36])).
% 0.22/0.51  fof(f106,plain,(
% 0.22/0.51    ~v1_relat_1(sK1) | spl12_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f104])).
% 0.22/0.51  fof(f133,plain,(
% 0.22/0.51    ~spl12_5 | spl12_7),
% 0.22/0.51    inference(avatar_split_clause,[],[f120,f131,f122])).
% 0.22/0.51  fof(f120,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),k7_relat_1(sK1,sK0)) | ~r2_hidden(sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),k9_relat_1(sK1,sK0))) )),
% 0.22/0.51    inference(resolution,[],[f68,f75])).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    ( ! [X0,X3,X1] : (sQ11_eqProxy(k2_relat_1(X0),X1) | ~r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0) | ~r2_hidden(sK7(X0,X1),X1)) )),
% 0.22/0.51    inference(equality_proxy_replacement,[],[f54,f67])).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    ! [X1,X0] : (sQ11_eqProxy(X0,X1) <=> X0 = X1)),
% 0.22/0.51    introduced(equality_proxy_definition,[new_symbols(naming,[sQ11_eqProxy])])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    ( ! [X0,X3,X1] : (k2_relat_1(X0) = X1 | ~r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0) | ~r2_hidden(sK7(X0,X1),X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0) | ~r2_hidden(sK7(X0,X1),X1)) & (r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0) | r2_hidden(sK7(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK9(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f27,f30,f29,f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0) | ~r2_hidden(sK7(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK7(X0,X1)),X0) | r2_hidden(sK7(X0,X1),X1))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK7(X0,X1)),X0) => r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK9(X0,X5),X5),X0))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.22/0.51    inference(rectify,[],[f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 0.22/0.51    inference(nnf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    ~sQ11_eqProxy(k2_relat_1(k7_relat_1(sK1,sK0)),k9_relat_1(sK1,sK0))),
% 0.22/0.51    inference(equality_proxy_replacement,[],[f37,f67])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    k2_relat_1(k7_relat_1(sK1,sK0)) != k9_relat_1(sK1,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  fof(f129,plain,(
% 0.22/0.51    spl12_5 | spl12_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f119,f126,f122])).
% 0.22/0.51  fof(f119,plain,(
% 0.22/0.51    r2_hidden(k4_tarski(sK8(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),k7_relat_1(sK1,sK0)) | r2_hidden(sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),k9_relat_1(sK1,sK0))),
% 0.22/0.51    inference(resolution,[],[f68,f76])).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    ( ! [X0,X1] : (sQ11_eqProxy(k2_relat_1(X0),X1) | r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0) | r2_hidden(sK7(X0,X1),X1)) )),
% 0.22/0.51    inference(equality_proxy_replacement,[],[f53,f67])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0) | r2_hidden(sK7(X0,X1),X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f31])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (2609)------------------------------
% 0.22/0.51  % (2609)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (2609)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (2609)Memory used [KB]: 6780
% 0.22/0.51  % (2609)Time elapsed: 0.081 s
% 0.22/0.51  % (2609)------------------------------
% 0.22/0.51  % (2609)------------------------------
% 0.22/0.51  % (2596)Success in time 0.143 s
%------------------------------------------------------------------------------
