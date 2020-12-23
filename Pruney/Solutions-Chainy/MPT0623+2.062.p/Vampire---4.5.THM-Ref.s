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
% DateTime   : Thu Dec  3 12:52:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 145 expanded)
%              Number of leaves         :   20 (  52 expanded)
%              Depth                    :   12
%              Number of atoms          :  286 ( 636 expanded)
%              Number of equality atoms :  129 ( 281 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f173,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f101,f103,f167,f171,f172])).

fof(f172,plain,
    ( ~ spl7_2
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f107,f99,f66])).

fof(f66,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f99,plain,
    ( spl7_8
  <=> ! [X0] :
        ( sK1 != X0
        | k1_xboole_0 != X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f107,plain,
    ( k1_xboole_0 != sK1
    | ~ spl7_8 ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,
    ( ! [X0] :
        ( sK1 != X0
        | k1_xboole_0 != X0 )
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f99])).

fof(f171,plain,
    ( spl7_2
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f170,f164,f66])).

fof(f164,plain,
    ( spl7_9
  <=> ! [X1] :
        ( sK1 != k1_relat_1(sK2(X1,sK4(sK3(sK0),k1_xboole_0)))
        | k1_xboole_0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f170,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_9 ),
    inference(equality_resolution,[],[f169])).

fof(f169,plain,
    ( ! [X0] :
        ( sK1 != X0
        | k1_xboole_0 = X0 )
    | ~ spl7_9 ),
    inference(duplicate_literal_removal,[],[f168])).

fof(f168,plain,
    ( ! [X0] :
        ( sK1 != X0
        | k1_xboole_0 = X0
        | k1_xboole_0 = X0 )
    | ~ spl7_9 ),
    inference(superposition,[],[f165,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK2(X0,X1)) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
          & k1_relat_1(sK2(X0,X1)) = X0
          & v1_funct_1(sK2(X0,X1))
          & v1_relat_1(sK2(X0,X1)) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
        & k1_relat_1(sK2(X0,X1)) = X0
        & v1_funct_1(sK2(X0,X1))
        & v1_relat_1(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).

fof(f165,plain,
    ( ! [X1] :
        ( sK1 != k1_relat_1(sK2(X1,sK4(sK3(sK0),k1_xboole_0)))
        | k1_xboole_0 = X1 )
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f164])).

fof(f167,plain,
    ( spl7_9
    | spl7_1 ),
    inference(avatar_split_clause,[],[f162,f63,f164])).

fof(f63,plain,
    ( spl7_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f162,plain,(
    ! [X1] :
      ( k1_xboole_0 = sK0
      | sK1 != k1_relat_1(sK2(X1,sK4(sK3(sK0),k1_xboole_0)))
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f149,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X1),sK0)
      | sK1 != k1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(global_subsumption,[],[f41,f40,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X1),sK0)
      | sK1 != k1_relat_1(sK2(X0,X1))
      | ~ v1_funct_1(sK2(X0,X1))
      | ~ v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f34,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f34,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_relat_1(X2),sK0)
      | k1_relat_1(X2) != sK1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_relat_1(X2),sK0)
        | k1_relat_1(X2) != sK1
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( ~ r1_tarski(k2_relat_1(X2),X0)
            | k1_relat_1(X2) != X1
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 != X0 ) )
   => ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),sK0)
          | k1_relat_1(X2) != sK1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = sK1
        | k1_xboole_0 != sK0 ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f149,plain,(
    ! [X5] :
      ( r1_tarski(k1_tarski(sK4(sK3(X5),k1_xboole_0)),X5)
      | k1_xboole_0 = X5 ) ),
    inference(resolution,[],[f140,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f140,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK3(X0),k1_xboole_0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f128,f46])).

fof(f46,plain,(
    ! [X0] : k1_relat_1(sK3(X0)) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X2] :
          ( np__1 = k1_funct_1(sK3(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK3(X0)) = X0
      & v1_funct_1(sK3(X0))
      & v1_relat_1(sK3(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_funct_1(X1,X2) = np__1
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( np__1 = k1_funct_1(sK3(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK3(X0)) = X0
        & v1_funct_1(sK3(X0))
        & v1_relat_1(sK3(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = np__1
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_funct_1(X1,X2) = np__1 )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).

fof(f128,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0,k1_xboole_0),k1_relat_1(X0))
      | k1_xboole_0 = k1_relat_1(X0) ) ),
    inference(resolution,[],[f125,f58])).

fof(f58,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK4(X0,X1),X3),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f25,f28,f27,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK4(X0,X1),X3),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f125,plain,(
    ! [X12] :
      ( r2_hidden(k4_tarski(sK4(X12,k1_xboole_0),sK5(X12,k1_xboole_0)),X12)
      | k1_xboole_0 = k1_relat_1(X12) ) ),
    inference(resolution,[],[f51,f77])).

fof(f77,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f48,f60])).

fof(f60,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f48,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f103,plain,(
    spl7_7 ),
    inference(avatar_contradiction_clause,[],[f102])).

fof(f102,plain,
    ( $false
    | spl7_7 ),
    inference(resolution,[],[f89,f37])).

fof(f37,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f89,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl7_7
  <=> r1_tarski(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f101,plain,
    ( ~ spl7_7
    | spl7_8 ),
    inference(avatar_split_clause,[],[f97,f99,f88])).

% (26955)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% (26953)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f97,plain,(
    ! [X0] :
      ( sK1 != X0
      | ~ r1_tarski(k1_xboole_0,sK0)
      | k1_xboole_0 != X0 ) ),
    inference(global_subsumption,[],[f45,f44,f96])).

fof(f96,plain,(
    ! [X0] :
      ( sK1 != X0
      | ~ r1_tarski(k1_xboole_0,sK0)
      | ~ v1_funct_1(sK3(X0))
      | ~ v1_relat_1(sK3(X0))
      | k1_xboole_0 != X0 ) ),
    inference(forward_demodulation,[],[f95,f46])).

fof(f95,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,sK0)
      | sK1 != k1_relat_1(sK3(X0))
      | ~ v1_funct_1(sK3(X0))
      | ~ v1_relat_1(sK3(X0))
      | k1_xboole_0 != X0 ) ),
    inference(superposition,[],[f34,f94])).

fof(f94,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(sK3(X0))
      | k1_xboole_0 != X0 ) ),
    inference(forward_demodulation,[],[f92,f46])).

fof(f92,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(sK3(X0))
      | k1_xboole_0 = k2_relat_1(sK3(X0)) ) ),
    inference(resolution,[],[f38,f44])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(f44,plain,(
    ! [X0] : v1_relat_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f45,plain,(
    ! [X0] : v1_funct_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f68,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f33,f66,f63])).

fof(f33,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:44:26 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.21/0.46  % (26964)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.50  % (26967)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.51  % (26959)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.51  % (26956)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (26956)Refutation not found, incomplete strategy% (26956)------------------------------
% 0.21/0.51  % (26956)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (26956)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (26956)Memory used [KB]: 10618
% 0.21/0.51  % (26956)Time elapsed: 0.067 s
% 0.21/0.51  % (26956)------------------------------
% 0.21/0.51  % (26956)------------------------------
% 0.21/0.52  % (26954)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (26965)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (26965)Refutation not found, incomplete strategy% (26965)------------------------------
% 0.21/0.52  % (26965)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (26965)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (26965)Memory used [KB]: 6012
% 0.21/0.52  % (26965)Time elapsed: 0.002 s
% 0.21/0.52  % (26965)------------------------------
% 0.21/0.52  % (26965)------------------------------
% 0.21/0.53  % (26957)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.53  % (26959)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f173,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f68,f101,f103,f167,f171,f172])).
% 0.21/0.53  fof(f172,plain,(
% 0.21/0.53    ~spl7_2 | ~spl7_8),
% 0.21/0.53    inference(avatar_split_clause,[],[f107,f99,f66])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    spl7_2 <=> k1_xboole_0 = sK1),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    spl7_8 <=> ! [X0] : (sK1 != X0 | k1_xboole_0 != X0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.21/0.53  fof(f107,plain,(
% 0.21/0.53    k1_xboole_0 != sK1 | ~spl7_8),
% 0.21/0.53    inference(equality_resolution,[],[f100])).
% 0.21/0.53  fof(f100,plain,(
% 0.21/0.53    ( ! [X0] : (sK1 != X0 | k1_xboole_0 != X0) ) | ~spl7_8),
% 0.21/0.53    inference(avatar_component_clause,[],[f99])).
% 0.21/0.53  fof(f171,plain,(
% 0.21/0.53    spl7_2 | ~spl7_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f170,f164,f66])).
% 0.21/0.53  fof(f164,plain,(
% 0.21/0.53    spl7_9 <=> ! [X1] : (sK1 != k1_relat_1(sK2(X1,sK4(sK3(sK0),k1_xboole_0))) | k1_xboole_0 = X1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.21/0.53  fof(f170,plain,(
% 0.21/0.53    k1_xboole_0 = sK1 | ~spl7_9),
% 0.21/0.53    inference(equality_resolution,[],[f169])).
% 0.21/0.53  fof(f169,plain,(
% 0.21/0.53    ( ! [X0] : (sK1 != X0 | k1_xboole_0 = X0) ) | ~spl7_9),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f168])).
% 0.21/0.53  fof(f168,plain,(
% 0.21/0.53    ( ! [X0] : (sK1 != X0 | k1_xboole_0 = X0 | k1_xboole_0 = X0) ) | ~spl7_9),
% 0.21/0.53    inference(superposition,[],[f165,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_relat_1(sK2(X0,X1)) = X0 | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) & k1_relat_1(sK2(X0,X1)) = X0 & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1))) | k1_xboole_0 = X0)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) & k1_relat_1(sK2(X0,X1)) = X0 & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | k1_xboole_0 = X0)),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).
% 0.21/0.53  fof(f165,plain,(
% 0.21/0.53    ( ! [X1] : (sK1 != k1_relat_1(sK2(X1,sK4(sK3(sK0),k1_xboole_0))) | k1_xboole_0 = X1) ) | ~spl7_9),
% 0.21/0.53    inference(avatar_component_clause,[],[f164])).
% 0.21/0.53  fof(f167,plain,(
% 0.21/0.53    spl7_9 | spl7_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f162,f63,f164])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    spl7_1 <=> k1_xboole_0 = sK0),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.53  fof(f162,plain,(
% 0.21/0.53    ( ! [X1] : (k1_xboole_0 = sK0 | sK1 != k1_relat_1(sK2(X1,sK4(sK3(sK0),k1_xboole_0))) | k1_xboole_0 = X1) )),
% 0.21/0.53    inference(resolution,[],[f149,f110])).
% 0.21/0.53  fof(f110,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X1),sK0) | sK1 != k1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(global_subsumption,[],[f41,f40,f109])).
% 0.21/0.53  fof(f109,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X1),sK0) | sK1 != k1_relat_1(sK2(X0,X1)) | ~v1_funct_1(sK2(X0,X1)) | ~v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(superposition,[],[f34,f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ( ! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK0)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0)) => (! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 0.21/0.53    inference(flattening,[],[f12])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.21/0.53    inference(negated_conjecture,[],[f10])).
% 0.21/0.53  fof(f10,conjecture,(
% 0.21/0.53    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v1_funct_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f149,plain,(
% 0.21/0.53    ( ! [X5] : (r1_tarski(k1_tarski(sK4(sK3(X5),k1_xboole_0)),X5) | k1_xboole_0 = X5) )),
% 0.21/0.53    inference(resolution,[],[f140,f54])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.21/0.53    inference(nnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.21/0.53  fof(f140,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(sK4(sK3(X0),k1_xboole_0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(superposition,[],[f128,f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X0] : (k1_relat_1(sK3(X0)) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0] : (! [X2] : (np__1 = k1_funct_1(sK3(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK3(X0)) = X0 & v1_funct_1(sK3(X0)) & v1_relat_1(sK3(X0)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0] : (? [X1] : (! [X2] : (k1_funct_1(X1,X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (np__1 = k1_funct_1(sK3(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK3(X0)) = X0 & v1_funct_1(sK3(X0)) & v1_relat_1(sK3(X0))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0] : ? [X1] : (! [X2] : (k1_funct_1(X1,X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = np__1) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).
% 0.21/0.53  fof(f128,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(sK4(X0,k1_xboole_0),k1_relat_1(X0)) | k1_xboole_0 = k1_relat_1(X0)) )),
% 0.21/0.53    inference(resolution,[],[f125,f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X5,X6),X0) | r2_hidden(X5,k1_relat_1(X0))) )),
% 0.21/0.53    inference(equality_resolution,[],[f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK4(X0,X1),X3),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f25,f28,f27,f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK4(X0,X1),X3),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.21/0.53    inference(rectify,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 0.21/0.53  fof(f125,plain,(
% 0.21/0.53    ( ! [X12] : (r2_hidden(k4_tarski(sK4(X12,k1_xboole_0),sK5(X12,k1_xboole_0)),X12) | k1_xboole_0 = k1_relat_1(X12)) )),
% 0.21/0.53    inference(resolution,[],[f51,f77])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.53    inference(superposition,[],[f48,f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f57])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.53    inference(flattening,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.53    inference(nnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | k1_relat_1(X0) = X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    spl7_7),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f102])).
% 0.21/0.53  fof(f102,plain,(
% 0.21/0.53    $false | spl7_7),
% 0.21/0.53    inference(resolution,[],[f89,f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    ~r1_tarski(k1_xboole_0,sK0) | spl7_7),
% 0.21/0.53    inference(avatar_component_clause,[],[f88])).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    spl7_7 <=> r1_tarski(k1_xboole_0,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    ~spl7_7 | spl7_8),
% 0.21/0.53    inference(avatar_split_clause,[],[f97,f99,f88])).
% 0.21/0.53  % (26955)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.53  % (26953)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    ( ! [X0] : (sK1 != X0 | ~r1_tarski(k1_xboole_0,sK0) | k1_xboole_0 != X0) )),
% 0.21/0.53    inference(global_subsumption,[],[f45,f44,f96])).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    ( ! [X0] : (sK1 != X0 | ~r1_tarski(k1_xboole_0,sK0) | ~v1_funct_1(sK3(X0)) | ~v1_relat_1(sK3(X0)) | k1_xboole_0 != X0) )),
% 0.21/0.53    inference(forward_demodulation,[],[f95,f46])).
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(k1_xboole_0,sK0) | sK1 != k1_relat_1(sK3(X0)) | ~v1_funct_1(sK3(X0)) | ~v1_relat_1(sK3(X0)) | k1_xboole_0 != X0) )),
% 0.21/0.53    inference(superposition,[],[f34,f94])).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 = k2_relat_1(sK3(X0)) | k1_xboole_0 != X0) )),
% 0.21/0.53    inference(forward_demodulation,[],[f92,f46])).
% 0.21/0.53  fof(f92,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 != k1_relat_1(sK3(X0)) | k1_xboole_0 = k2_relat_1(sK3(X0))) )),
% 0.21/0.53    inference(resolution,[],[f38,f44])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = k2_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ( ! [X0] : (v1_relat_1(sK3(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ( ! [X0] : (v1_funct_1(sK3(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    ~spl7_1 | spl7_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f33,f66,f63])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    k1_xboole_0 = sK1 | k1_xboole_0 != sK0),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (26959)------------------------------
% 0.21/0.53  % (26959)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (26959)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (26959)Memory used [KB]: 10746
% 0.21/0.53  % (26959)Time elapsed: 0.015 s
% 0.21/0.53  % (26959)------------------------------
% 0.21/0.53  % (26959)------------------------------
% 0.21/0.53  % (26953)Refutation not found, incomplete strategy% (26953)------------------------------
% 0.21/0.53  % (26953)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (26953)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (26953)Memory used [KB]: 6140
% 0.21/0.53  % (26953)Time elapsed: 0.108 s
% 0.21/0.53  % (26953)------------------------------
% 0.21/0.53  % (26953)------------------------------
% 0.21/0.53  % (26952)Success in time 0.167 s
%------------------------------------------------------------------------------
