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
% DateTime   : Thu Dec  3 12:55:54 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 164 expanded)
%              Number of leaves         :   18 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :  269 ( 668 expanded)
%              Number of equality atoms :   46 ( 112 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f156,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f49,f62,f71,f74,f114,f119,f148,f151,f155])).

fof(f155,plain,
    ( ~ spl5_4
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f152,f133,f66])).

fof(f66,plain,
    ( spl5_4
  <=> v1_relat_1(k2_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f133,plain,
    ( spl5_13
  <=> r2_hidden(sK1,k1_wellord1(k2_wellord1(sK2,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f152,plain,
    ( ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | ~ spl5_13 ),
    inference(resolution,[],[f134,f41])).

fof(f41,plain,(
    ! [X4,X0] :
      ( ~ r2_hidden(X4,k1_wellord1(X0,X4))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X4,X2,X0] :
      ( ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X4) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 != X4
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X1),X0)
                | sK3(X0,X1,X2) = X1
                | ~ r2_hidden(sK3(X0,X1,X2),X2) )
              & ( ( r2_hidden(k4_tarski(sK3(X0,X1,X2),X1),X0)
                  & sK3(X0,X1,X2) != X1 )
                | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            | X1 = X3
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k4_tarski(X3,X1),X0)
              & X1 != X3 )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X1),X0)
          | sK3(X0,X1,X2) = X1
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(k4_tarski(sK3(X0,X1,X2),X1),X0)
            & sK3(X0,X1,X2) != X1 )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).

fof(f134,plain,
    ( r2_hidden(sK1,k1_wellord1(k2_wellord1(sK2,sK0),sK1))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f133])).

fof(f151,plain,
    ( ~ spl5_2
    | spl5_11 ),
    inference(avatar_split_clause,[],[f149,f112,f47])).

fof(f47,plain,
    ( spl5_2
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f112,plain,
    ( spl5_11
  <=> r1_tarski(k2_wellord1(sK2,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f149,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_11 ),
    inference(resolution,[],[f113,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_wellord1(X0,X1),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f33,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_wellord1)).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f113,plain,
    ( ~ r1_tarski(k2_wellord1(sK2,sK0),sK2)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f112])).

fof(f148,plain,
    ( spl5_1
    | spl5_13
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f131,f108,f133,f43])).

fof(f43,plain,
    ( spl5_1
  <=> r1_tarski(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f108,plain,
    ( spl5_10
  <=> sK1 = sK4(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f131,plain,
    ( r2_hidden(sK1,k1_wellord1(k2_wellord1(sK2,sK0),sK1))
    | r1_tarski(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1))
    | ~ spl5_10 ),
    inference(superposition,[],[f36,f109])).

fof(f109,plain,
    ( sK1 = sK4(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f108])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f119,plain,
    ( spl5_1
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f115,f105,f43])).

fof(f105,plain,
    ( spl5_9
  <=> r2_hidden(sK4(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f115,plain,
    ( r1_tarski(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1))
    | ~ spl5_9 ),
    inference(resolution,[],[f106,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f106,plain,
    ( r2_hidden(sK4(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK1))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f105])).

fof(f114,plain,
    ( ~ spl5_11
    | spl5_9
    | spl5_10
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f100,f69,f47,f108,f105,f112])).

fof(f69,plain,
    ( spl5_5
  <=> r2_hidden(k4_tarski(sK4(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)),sK1),k2_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f100,plain,
    ( sK1 = sK4(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1))
    | r2_hidden(sK4(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK1))
    | ~ r1_tarski(k2_wellord1(sK2,sK0),sK2)
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(resolution,[],[f97,f75])).

fof(f75,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK4(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)),sK1),X0)
        | ~ r1_tarski(k2_wellord1(sK2,sK0),X0) )
    | ~ spl5_5 ),
    inference(resolution,[],[f70,f35])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f70,plain,
    ( r2_hidden(k4_tarski(sK4(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)),sK1),k2_wellord1(sK2,sK0))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f69])).

fof(f97,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | X0 = X1
        | r2_hidden(X0,k1_wellord1(sK2,X1)) )
    | ~ spl5_2 ),
    inference(resolution,[],[f38,f48])).

fof(f48,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f38,plain,(
    ! [X4,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | r2_hidden(X4,k1_wellord1(X0,X1)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f74,plain,
    ( ~ spl5_2
    | spl5_4 ),
    inference(avatar_split_clause,[],[f72,f66,f47])).

fof(f72,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_4 ),
    inference(resolution,[],[f67,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_wellord1)).

fof(f67,plain,
    ( ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f66])).

fof(f71,plain,
    ( ~ spl5_4
    | spl5_5
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f63,f60,f69,f66])).

fof(f60,plain,
    ( spl5_3
  <=> r2_hidden(sK4(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)),k1_wellord1(k2_wellord1(sK2,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f63,plain,
    ( r2_hidden(k4_tarski(sK4(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)),sK1),k2_wellord1(sK2,sK0))
    | ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | ~ spl5_3 ),
    inference(resolution,[],[f61,f39])).

fof(f39,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k1_wellord1(X0,X1))
      | r2_hidden(k4_tarski(X4,X1),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f61,plain,
    ( r2_hidden(sK4(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)),k1_wellord1(k2_wellord1(sK2,sK0),sK1))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f62,plain,
    ( spl5_3
    | spl5_1 ),
    inference(avatar_split_clause,[],[f57,f43,f60])).

fof(f57,plain,
    ( r2_hidden(sK4(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)),k1_wellord1(k2_wellord1(sK2,sK0),sK1))
    | spl5_1 ),
    inference(resolution,[],[f55,f52])).

fof(f52,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f37,f36])).

fof(f55,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_wellord1(k2_wellord1(sK2,sK0),sK1),X0)
        | r2_hidden(sK4(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)),X0) )
    | spl5_1 ),
    inference(resolution,[],[f53,f44])).

fof(f44,plain,
    ( ~ r1_tarski(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X2)
      | r2_hidden(sK4(X0,X1),X2) ) ),
    inference(resolution,[],[f35,f36])).

fof(f49,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f24,f47])).

fof(f24,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ r1_tarski(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k1_wellord1(k2_wellord1(X2,X0),X1),k1_wellord1(X2,X1))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k1_wellord1(k2_wellord1(X2,X0),X1),k1_wellord1(X2,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k1_wellord1(k2_wellord1(X2,X0),X1),k1_wellord1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_wellord1(k2_wellord1(X2,X0),X1),k1_wellord1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_wellord1)).

fof(f45,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f25,f43])).

fof(f25,plain,(
    ~ r1_tarski(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:38:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (24181)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (24191)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (24189)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (24184)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.32/0.53  % (24199)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.32/0.53  % (24190)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.32/0.53  % (24185)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.32/0.53  % (24186)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.32/0.53  % (24183)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.32/0.53  % (24197)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.32/0.53  % (24183)Refutation not found, incomplete strategy% (24183)------------------------------
% 1.32/0.53  % (24183)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.53  % (24183)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.53  
% 1.32/0.53  % (24183)Memory used [KB]: 10618
% 1.32/0.53  % (24183)Time elapsed: 0.130 s
% 1.32/0.53  % (24183)------------------------------
% 1.32/0.53  % (24183)------------------------------
% 1.32/0.53  % (24200)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.32/0.53  % (24182)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.32/0.53  % (24195)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.32/0.54  % (24200)Refutation found. Thanks to Tanya!
% 1.32/0.54  % SZS status Theorem for theBenchmark
% 1.32/0.54  % SZS output start Proof for theBenchmark
% 1.32/0.54  fof(f156,plain,(
% 1.32/0.54    $false),
% 1.32/0.54    inference(avatar_sat_refutation,[],[f45,f49,f62,f71,f74,f114,f119,f148,f151,f155])).
% 1.32/0.54  fof(f155,plain,(
% 1.32/0.54    ~spl5_4 | ~spl5_13),
% 1.32/0.54    inference(avatar_split_clause,[],[f152,f133,f66])).
% 1.32/0.54  fof(f66,plain,(
% 1.32/0.54    spl5_4 <=> v1_relat_1(k2_wellord1(sK2,sK0))),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.32/0.54  fof(f133,plain,(
% 1.32/0.54    spl5_13 <=> r2_hidden(sK1,k1_wellord1(k2_wellord1(sK2,sK0),sK1))),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.32/0.54  fof(f152,plain,(
% 1.32/0.54    ~v1_relat_1(k2_wellord1(sK2,sK0)) | ~spl5_13),
% 1.32/0.54    inference(resolution,[],[f134,f41])).
% 1.32/0.54  fof(f41,plain,(
% 1.32/0.54    ( ! [X4,X0] : (~r2_hidden(X4,k1_wellord1(X0,X4)) | ~v1_relat_1(X0)) )),
% 1.32/0.54    inference(equality_resolution,[],[f40])).
% 1.32/0.54  fof(f40,plain,(
% 1.32/0.54    ( ! [X4,X2,X0] : (~r2_hidden(X4,X2) | k1_wellord1(X0,X4) != X2 | ~v1_relat_1(X0)) )),
% 1.32/0.54    inference(equality_resolution,[],[f27])).
% 1.32/0.54  fof(f27,plain,(
% 1.32/0.54    ( ! [X4,X2,X0,X1] : (X1 != X4 | ~r2_hidden(X4,X2) | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f19])).
% 1.32/0.54  fof(f19,plain,(
% 1.32/0.54    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK3(X0,X1,X2),X1),X0) | sK3(X0,X1,X2) = X1 | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK3(X0,X1,X2),X1),X0) & sK3(X0,X1,X2) != X1) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.32/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).
% 1.32/0.54  fof(f18,plain,(
% 1.32/0.54    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2))) => ((~r2_hidden(k4_tarski(sK3(X0,X1,X2),X1),X0) | sK3(X0,X1,X2) = X1 | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK3(X0,X1,X2),X1),X0) & sK3(X0,X1,X2) != X1) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.32/0.54    introduced(choice_axiom,[])).
% 1.32/0.54  fof(f17,plain,(
% 1.32/0.54    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.32/0.54    inference(rectify,[],[f16])).
% 1.32/0.54  fof(f16,plain,(
% 1.32/0.54    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.32/0.54    inference(flattening,[],[f15])).
% 1.32/0.54  fof(f15,plain,(
% 1.32/0.54    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.32/0.54    inference(nnf_transformation,[],[f10])).
% 1.32/0.54  fof(f10,plain,(
% 1.32/0.54    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))) | ~v1_relat_1(X0))),
% 1.32/0.54    inference(ennf_transformation,[],[f3])).
% 1.32/0.54  fof(f3,axiom,(
% 1.32/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).
% 1.32/0.54  fof(f134,plain,(
% 1.32/0.54    r2_hidden(sK1,k1_wellord1(k2_wellord1(sK2,sK0),sK1)) | ~spl5_13),
% 1.32/0.54    inference(avatar_component_clause,[],[f133])).
% 1.32/0.54  fof(f151,plain,(
% 1.32/0.54    ~spl5_2 | spl5_11),
% 1.32/0.54    inference(avatar_split_clause,[],[f149,f112,f47])).
% 1.32/0.54  fof(f47,plain,(
% 1.32/0.54    spl5_2 <=> v1_relat_1(sK2)),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.32/0.54  fof(f112,plain,(
% 1.32/0.54    spl5_11 <=> r1_tarski(k2_wellord1(sK2,sK0),sK2)),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.32/0.54  fof(f149,plain,(
% 1.32/0.54    ~v1_relat_1(sK2) | spl5_11),
% 1.32/0.54    inference(resolution,[],[f113,f54])).
% 1.32/0.54  fof(f54,plain,(
% 1.32/0.54    ( ! [X0,X1] : (r1_tarski(k2_wellord1(X0,X1),X0) | ~v1_relat_1(X0)) )),
% 1.32/0.54    inference(superposition,[],[f33,f26])).
% 1.32/0.54  fof(f26,plain,(
% 1.32/0.54    ( ! [X0,X1] : (k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) | ~v1_relat_1(X0)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f9])).
% 1.32/0.54  fof(f9,plain,(
% 1.32/0.54    ! [X0] : (! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) | ~v1_relat_1(X0))),
% 1.32/0.54    inference(ennf_transformation,[],[f4])).
% 1.32/0.54  fof(f4,axiom,(
% 1.32/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_wellord1)).
% 1.32/0.54  fof(f33,plain,(
% 1.32/0.54    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f2])).
% 1.32/0.54  fof(f2,axiom,(
% 1.32/0.54    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.32/0.54  fof(f113,plain,(
% 1.32/0.54    ~r1_tarski(k2_wellord1(sK2,sK0),sK2) | spl5_11),
% 1.32/0.54    inference(avatar_component_clause,[],[f112])).
% 1.32/0.54  fof(f148,plain,(
% 1.32/0.54    spl5_1 | spl5_13 | ~spl5_10),
% 1.32/0.54    inference(avatar_split_clause,[],[f131,f108,f133,f43])).
% 1.32/0.54  fof(f43,plain,(
% 1.32/0.54    spl5_1 <=> r1_tarski(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1))),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.32/0.54  fof(f108,plain,(
% 1.32/0.54    spl5_10 <=> sK1 = sK4(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1))),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.32/0.54  fof(f131,plain,(
% 1.32/0.54    r2_hidden(sK1,k1_wellord1(k2_wellord1(sK2,sK0),sK1)) | r1_tarski(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)) | ~spl5_10),
% 1.32/0.54    inference(superposition,[],[f36,f109])).
% 1.32/0.54  fof(f109,plain,(
% 1.32/0.54    sK1 = sK4(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)) | ~spl5_10),
% 1.32/0.54    inference(avatar_component_clause,[],[f108])).
% 1.32/0.54  fof(f36,plain,(
% 1.32/0.54    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f23])).
% 1.32/0.54  fof(f23,plain,(
% 1.32/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.32/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f22])).
% 1.32/0.54  fof(f22,plain,(
% 1.32/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.32/0.54    introduced(choice_axiom,[])).
% 1.32/0.54  fof(f21,plain,(
% 1.32/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.32/0.54    inference(rectify,[],[f20])).
% 1.32/0.54  fof(f20,plain,(
% 1.32/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.32/0.54    inference(nnf_transformation,[],[f12])).
% 1.32/0.54  fof(f12,plain,(
% 1.32/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.32/0.54    inference(ennf_transformation,[],[f1])).
% 1.32/0.54  fof(f1,axiom,(
% 1.32/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.32/0.54  fof(f119,plain,(
% 1.32/0.54    spl5_1 | ~spl5_9),
% 1.32/0.54    inference(avatar_split_clause,[],[f115,f105,f43])).
% 1.32/0.54  fof(f105,plain,(
% 1.32/0.54    spl5_9 <=> r2_hidden(sK4(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK1))),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.32/0.54  fof(f115,plain,(
% 1.32/0.54    r1_tarski(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)) | ~spl5_9),
% 1.32/0.54    inference(resolution,[],[f106,f37])).
% 1.32/0.54  fof(f37,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f23])).
% 1.32/0.54  fof(f106,plain,(
% 1.32/0.54    r2_hidden(sK4(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK1)) | ~spl5_9),
% 1.32/0.54    inference(avatar_component_clause,[],[f105])).
% 1.32/0.54  fof(f114,plain,(
% 1.32/0.54    ~spl5_11 | spl5_9 | spl5_10 | ~spl5_2 | ~spl5_5),
% 1.32/0.54    inference(avatar_split_clause,[],[f100,f69,f47,f108,f105,f112])).
% 1.32/0.54  fof(f69,plain,(
% 1.32/0.54    spl5_5 <=> r2_hidden(k4_tarski(sK4(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)),sK1),k2_wellord1(sK2,sK0))),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.32/0.54  fof(f100,plain,(
% 1.32/0.54    sK1 = sK4(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)) | r2_hidden(sK4(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK1)) | ~r1_tarski(k2_wellord1(sK2,sK0),sK2) | (~spl5_2 | ~spl5_5)),
% 1.32/0.54    inference(resolution,[],[f97,f75])).
% 1.32/0.54  fof(f75,plain,(
% 1.32/0.54    ( ! [X0] : (r2_hidden(k4_tarski(sK4(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)),sK1),X0) | ~r1_tarski(k2_wellord1(sK2,sK0),X0)) ) | ~spl5_5),
% 1.32/0.54    inference(resolution,[],[f70,f35])).
% 1.32/0.54  fof(f35,plain,(
% 1.32/0.54    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f23])).
% 1.32/0.54  fof(f70,plain,(
% 1.32/0.54    r2_hidden(k4_tarski(sK4(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)),sK1),k2_wellord1(sK2,sK0)) | ~spl5_5),
% 1.32/0.54    inference(avatar_component_clause,[],[f69])).
% 1.32/0.54  fof(f97,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | X0 = X1 | r2_hidden(X0,k1_wellord1(sK2,X1))) ) | ~spl5_2),
% 1.32/0.54    inference(resolution,[],[f38,f48])).
% 1.32/0.54  fof(f48,plain,(
% 1.32/0.54    v1_relat_1(sK2) | ~spl5_2),
% 1.32/0.54    inference(avatar_component_clause,[],[f47])).
% 1.32/0.54  fof(f38,plain,(
% 1.32/0.54    ( ! [X4,X0,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4 | r2_hidden(X4,k1_wellord1(X0,X1))) )),
% 1.32/0.54    inference(equality_resolution,[],[f29])).
% 1.32/0.54  fof(f29,plain,(
% 1.32/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4 | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f19])).
% 1.32/0.54  fof(f74,plain,(
% 1.32/0.54    ~spl5_2 | spl5_4),
% 1.32/0.54    inference(avatar_split_clause,[],[f72,f66,f47])).
% 1.32/0.54  fof(f72,plain,(
% 1.32/0.54    ~v1_relat_1(sK2) | spl5_4),
% 1.32/0.54    inference(resolution,[],[f67,f34])).
% 1.32/0.54  fof(f34,plain,(
% 1.32/0.54    ( ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f11])).
% 1.32/0.54  fof(f11,plain,(
% 1.32/0.54    ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0))),
% 1.32/0.54    inference(ennf_transformation,[],[f5])).
% 1.32/0.54  fof(f5,axiom,(
% 1.32/0.54    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k2_wellord1(X0,X1)))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_wellord1)).
% 1.32/0.54  fof(f67,plain,(
% 1.32/0.54    ~v1_relat_1(k2_wellord1(sK2,sK0)) | spl5_4),
% 1.32/0.54    inference(avatar_component_clause,[],[f66])).
% 1.32/0.54  fof(f71,plain,(
% 1.32/0.54    ~spl5_4 | spl5_5 | ~spl5_3),
% 1.32/0.54    inference(avatar_split_clause,[],[f63,f60,f69,f66])).
% 1.32/0.54  fof(f60,plain,(
% 1.32/0.54    spl5_3 <=> r2_hidden(sK4(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)),k1_wellord1(k2_wellord1(sK2,sK0),sK1))),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.32/0.54  fof(f63,plain,(
% 1.32/0.54    r2_hidden(k4_tarski(sK4(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)),sK1),k2_wellord1(sK2,sK0)) | ~v1_relat_1(k2_wellord1(sK2,sK0)) | ~spl5_3),
% 1.32/0.54    inference(resolution,[],[f61,f39])).
% 1.32/0.54  fof(f39,plain,(
% 1.32/0.54    ( ! [X4,X0,X1] : (~r2_hidden(X4,k1_wellord1(X0,X1)) | r2_hidden(k4_tarski(X4,X1),X0) | ~v1_relat_1(X0)) )),
% 1.32/0.54    inference(equality_resolution,[],[f28])).
% 1.32/0.54  fof(f28,plain,(
% 1.32/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(k4_tarski(X4,X1),X0) | ~r2_hidden(X4,X2) | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f19])).
% 1.32/0.54  fof(f61,plain,(
% 1.32/0.54    r2_hidden(sK4(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)),k1_wellord1(k2_wellord1(sK2,sK0),sK1)) | ~spl5_3),
% 1.32/0.54    inference(avatar_component_clause,[],[f60])).
% 1.32/0.54  fof(f62,plain,(
% 1.32/0.54    spl5_3 | spl5_1),
% 1.32/0.54    inference(avatar_split_clause,[],[f57,f43,f60])).
% 1.32/0.54  fof(f57,plain,(
% 1.32/0.54    r2_hidden(sK4(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)),k1_wellord1(k2_wellord1(sK2,sK0),sK1)) | spl5_1),
% 1.32/0.54    inference(resolution,[],[f55,f52])).
% 1.32/0.54  fof(f52,plain,(
% 1.32/0.54    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.32/0.54    inference(duplicate_literal_removal,[],[f51])).
% 1.32/0.54  fof(f51,plain,(
% 1.32/0.54    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 1.32/0.54    inference(resolution,[],[f37,f36])).
% 1.32/0.54  fof(f55,plain,(
% 1.32/0.54    ( ! [X0] : (~r1_tarski(k1_wellord1(k2_wellord1(sK2,sK0),sK1),X0) | r2_hidden(sK4(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)),X0)) ) | spl5_1),
% 1.32/0.54    inference(resolution,[],[f53,f44])).
% 1.32/0.54  fof(f44,plain,(
% 1.32/0.54    ~r1_tarski(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)) | spl5_1),
% 1.32/0.54    inference(avatar_component_clause,[],[f43])).
% 1.32/0.54  fof(f53,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,X2) | r2_hidden(sK4(X0,X1),X2)) )),
% 1.32/0.54    inference(resolution,[],[f35,f36])).
% 1.32/0.54  fof(f49,plain,(
% 1.32/0.54    spl5_2),
% 1.32/0.54    inference(avatar_split_clause,[],[f24,f47])).
% 1.32/0.54  fof(f24,plain,(
% 1.32/0.54    v1_relat_1(sK2)),
% 1.32/0.54    inference(cnf_transformation,[],[f14])).
% 1.32/0.54  fof(f14,plain,(
% 1.32/0.54    ~r1_tarski(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)) & v1_relat_1(sK2)),
% 1.32/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f13])).
% 1.32/0.54  fof(f13,plain,(
% 1.32/0.54    ? [X0,X1,X2] : (~r1_tarski(k1_wellord1(k2_wellord1(X2,X0),X1),k1_wellord1(X2,X1)) & v1_relat_1(X2)) => (~r1_tarski(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1)) & v1_relat_1(sK2))),
% 1.32/0.54    introduced(choice_axiom,[])).
% 1.32/0.54  fof(f8,plain,(
% 1.32/0.54    ? [X0,X1,X2] : (~r1_tarski(k1_wellord1(k2_wellord1(X2,X0),X1),k1_wellord1(X2,X1)) & v1_relat_1(X2))),
% 1.32/0.54    inference(ennf_transformation,[],[f7])).
% 1.32/0.54  fof(f7,negated_conjecture,(
% 1.32/0.54    ~! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k1_wellord1(k2_wellord1(X2,X0),X1),k1_wellord1(X2,X1)))),
% 1.32/0.54    inference(negated_conjecture,[],[f6])).
% 1.32/0.54  fof(f6,conjecture,(
% 1.32/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k1_wellord1(k2_wellord1(X2,X0),X1),k1_wellord1(X2,X1)))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_wellord1)).
% 1.32/0.54  fof(f45,plain,(
% 1.32/0.54    ~spl5_1),
% 1.32/0.54    inference(avatar_split_clause,[],[f25,f43])).
% 1.32/0.54  fof(f25,plain,(
% 1.32/0.54    ~r1_tarski(k1_wellord1(k2_wellord1(sK2,sK0),sK1),k1_wellord1(sK2,sK1))),
% 1.32/0.54    inference(cnf_transformation,[],[f14])).
% 1.32/0.54  % SZS output end Proof for theBenchmark
% 1.32/0.54  % (24200)------------------------------
% 1.32/0.54  % (24200)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (24200)Termination reason: Refutation
% 1.32/0.54  
% 1.32/0.54  % (24200)Memory used [KB]: 10746
% 1.32/0.54  % (24200)Time elapsed: 0.132 s
% 1.32/0.54  % (24200)------------------------------
% 1.32/0.54  % (24200)------------------------------
% 1.32/0.54  % (24207)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.32/0.54  % (24202)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.32/0.54  % (24201)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.32/0.54  % (24188)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.32/0.54  % (24208)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.32/0.54  % (24204)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.50/0.55  % (24198)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.50/0.55  % (24209)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.50/0.55  % (24210)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.50/0.55  % (24198)Refutation not found, incomplete strategy% (24198)------------------------------
% 1.50/0.55  % (24198)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.55  % (24206)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.50/0.55  % (24180)Success in time 0.192 s
%------------------------------------------------------------------------------
