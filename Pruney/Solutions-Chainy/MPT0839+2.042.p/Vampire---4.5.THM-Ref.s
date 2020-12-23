%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 196 expanded)
%              Number of leaves         :   29 (  71 expanded)
%              Depth                    :   12
%              Number of atoms          :  356 ( 680 expanded)
%              Number of equality atoms :   56 ( 112 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f418,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f82,f124,f172,f226,f351,f353,f395,f411,f414,f417])).

fof(f417,plain,
    ( ~ spl7_2
    | ~ spl7_35 ),
    inference(avatar_contradiction_clause,[],[f416])).

fof(f416,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_35 ),
    inference(subsumption_resolution,[],[f81,f350])).

fof(f350,plain,
    ( ! [X2] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
    | ~ spl7_35 ),
    inference(avatar_component_clause,[],[f349])).

fof(f349,plain,
    ( spl7_35
  <=> ! [X2] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f81,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl7_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f414,plain,(
    spl7_41 ),
    inference(avatar_contradiction_clause,[],[f412])).

fof(f412,plain,
    ( $false
    | spl7_41 ),
    inference(resolution,[],[f410,f54])).

fof(f54,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f410,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | spl7_41 ),
    inference(avatar_component_clause,[],[f409])).

fof(f409,plain,
    ( spl7_41
  <=> v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f411,plain,
    ( ~ spl7_41
    | ~ spl7_2
    | spl7_39 ),
    inference(avatar_split_clause,[],[f406,f392,f80,f409])).

fof(f392,plain,
    ( spl7_39
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f406,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | ~ spl7_2
    | spl7_39 ),
    inference(resolution,[],[f401,f81])).

fof(f401,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl7_39 ),
    inference(resolution,[],[f393,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f393,plain,
    ( ~ v1_relat_1(sK2)
    | spl7_39 ),
    inference(avatar_component_clause,[],[f392])).

fof(f395,plain,
    ( ~ spl7_39
    | spl7_7
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f382,f224,f122,f392])).

fof(f122,plain,
    ( spl7_7
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f224,plain,
    ( spl7_19
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f382,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_19 ),
    inference(trivial_inequality_removal,[],[f372])).

fof(f372,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_19 ),
    inference(superposition,[],[f51,f225])).

fof(f225,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f224])).

fof(f51,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(f353,plain,
    ( spl7_19
    | ~ spl7_8
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f228,f221,f156,f224])).

fof(f156,plain,
    ( spl7_8
  <=> m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f221,plain,
    ( spl7_18
  <=> ! [X1] :
        ( ~ r2_hidden(sK3(sK2,k1_xboole_0),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f228,plain,
    ( ~ m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1))
    | k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl7_18 ),
    inference(resolution,[],[f222,f190])).

fof(f190,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0,k1_xboole_0),k1_relat_1(X0))
      | k1_xboole_0 = k1_relat_1(X0) ) ),
    inference(resolution,[],[f188,f71])).

fof(f71,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f36,f39,f38,f37])).

fof(f37,plain,(
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

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f188,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK3(X0,k1_xboole_0),sK4(X0,k1_xboole_0)),X0)
      | k1_xboole_0 = k1_relat_1(X0) ) ),
    inference(resolution,[],[f145,f50])).

fof(f50,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f145,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X4,sK3(X3,X4))
      | k1_relat_1(X3) = X4
      | r2_hidden(k4_tarski(sK3(X3,X4),sK4(X3,X4)),X3) ) ),
    inference(resolution,[],[f60,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f222,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK3(sK2,k1_xboole_0),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK1)) )
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f221])).

fof(f351,plain,
    ( spl7_35
    | spl7_10
    | spl7_8 ),
    inference(avatar_split_clause,[],[f346,f156,f165,f349])).

fof(f165,plain,
    ( spl7_10
  <=> ! [X3,X2] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f346,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) )
    | spl7_8 ),
    inference(resolution,[],[f142,f157])).

fof(f157,plain,
    ( ~ m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1))
    | spl7_8 ),
    inference(avatar_component_clause,[],[f156])).

fof(f142,plain,(
    ! [X14,X12,X10,X13,X11] :
      ( m1_subset_1(k1_relat_1(X10),k1_zfmisc_1(X11))
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) ) ),
    inference(resolution,[],[f138,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f138,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( r2_hidden(k1_relat_1(X5),k1_zfmisc_1(X8))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) ) ),
    inference(resolution,[],[f135,f73])).

fof(f73,plain,(
    ! [X0,X3] :
      ( ~ r1_tarski(X3,X0)
      | r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK6(X0,X1),X0)
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( r1_tarski(sK6(X0,X1),X0)
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f42,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK6(X0,X1),X0)
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( r1_tarski(sK6(X0,X1),X0)
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f135,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r1_tarski(k1_relat_1(X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f118,f54])).

fof(f118,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ v1_relat_1(X7)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X7))
      | r1_tarski(k1_relat_1(X4),X5) ) ),
    inference(resolution,[],[f110,f53])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(k1_relat_1(X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f69,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f226,plain,
    ( spl7_18
    | spl7_19 ),
    inference(avatar_split_clause,[],[f216,f224,f221])).

fof(f216,plain,(
    ! [X1] :
      ( k1_xboole_0 = k1_relat_1(sK2)
      | ~ r2_hidden(sK3(sK2,k1_xboole_0),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK1)) ) ),
    inference(resolution,[],[f190,f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(sK2))
      | ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK1)) ) ),
    inference(global_subsumption,[],[f45,f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(sK2))
      | ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK1))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    inference(superposition,[],[f115,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_relset_1(sK1,sK0,sK2))
      | ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK1)) ) ),
    inference(resolution,[],[f70,f47])).

fof(f47,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK1)
      | ~ r2_hidden(X3,k1_relset_1(sK1,sK0,sK2)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_relset_1(sK1,sK0,sK2))
        | ~ m1_subset_1(X3,sK1) )
    & k1_xboole_0 != k2_relset_1(sK1,sK0,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f31])).

fof(f31,plain,
    ( ? [X0,X1,X2] :
        ( ! [X3] :
            ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
            | ~ m1_subset_1(X3,X1) )
        & k1_xboole_0 != k2_relset_1(X1,X0,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ! [X3] :
          ( ~ r2_hidden(X3,k1_relset_1(sK1,sK0,sK2))
          | ~ m1_subset_1(X3,sK1) )
      & k1_xboole_0 != k2_relset_1(sK1,sK0,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
          | ~ m1_subset_1(X3,X1) )
      & k1_xboole_0 != k2_relset_1(X1,X0,X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
          | ~ m1_subset_1(X3,X1) )
      & k1_xboole_0 != k2_relset_1(X1,X0,X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ~ ( ! [X3] :
                ( m1_subset_1(X3,X1)
               => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
            & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,X1)
                       => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
                    & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,X1)
                     => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
                  & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relset_1)).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f45,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f172,plain,
    ( ~ spl7_2
    | ~ spl7_10 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f81,f166])).

fof(f166,plain,
    ( ! [X2,X3] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f165])).

fof(f124,plain,
    ( ~ spl7_2
    | ~ spl7_7
    | spl7_1 ),
    inference(avatar_split_clause,[],[f119,f76,f122,f80])).

fof(f76,plain,
    ( spl7_1
  <=> k1_xboole_0 = k2_relset_1(sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f119,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl7_1 ),
    inference(superposition,[],[f77,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f77,plain,
    ( k1_xboole_0 != k2_relset_1(sK1,sK0,sK2)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f82,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f45,f80])).

fof(f78,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f46,f76])).

fof(f46,plain,(
    k1_xboole_0 != k2_relset_1(sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:57:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.42  % (5540)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.43  % (5540)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f418,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f78,f82,f124,f172,f226,f351,f353,f395,f411,f414,f417])).
% 0.21/0.43  fof(f417,plain,(
% 0.21/0.43    ~spl7_2 | ~spl7_35),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f416])).
% 0.21/0.43  fof(f416,plain,(
% 0.21/0.43    $false | (~spl7_2 | ~spl7_35)),
% 0.21/0.43    inference(subsumption_resolution,[],[f81,f350])).
% 0.21/0.43  fof(f350,plain,(
% 0.21/0.43    ( ! [X2] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))) ) | ~spl7_35),
% 0.21/0.43    inference(avatar_component_clause,[],[f349])).
% 0.21/0.43  fof(f349,plain,(
% 0.21/0.43    spl7_35 <=> ! [X2] : ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).
% 0.21/0.43  fof(f81,plain,(
% 0.21/0.43    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl7_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f80])).
% 0.21/0.43  fof(f80,plain,(
% 0.21/0.43    spl7_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.43  fof(f414,plain,(
% 0.21/0.43    spl7_41),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f412])).
% 0.21/0.43  fof(f412,plain,(
% 0.21/0.43    $false | spl7_41),
% 0.21/0.43    inference(resolution,[],[f410,f54])).
% 0.21/0.43  fof(f54,plain,(
% 0.21/0.43    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,axiom,(
% 0.21/0.43    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.43  fof(f410,plain,(
% 0.21/0.43    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | spl7_41),
% 0.21/0.43    inference(avatar_component_clause,[],[f409])).
% 0.21/0.43  fof(f409,plain,(
% 0.21/0.43    spl7_41 <=> v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).
% 0.21/0.43  fof(f411,plain,(
% 0.21/0.43    ~spl7_41 | ~spl7_2 | spl7_39),
% 0.21/0.43    inference(avatar_split_clause,[],[f406,f392,f80,f409])).
% 0.21/0.43  fof(f392,plain,(
% 0.21/0.43    spl7_39 <=> v1_relat_1(sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).
% 0.21/0.43  fof(f406,plain,(
% 0.21/0.43    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | (~spl7_2 | spl7_39)),
% 0.21/0.43    inference(resolution,[],[f401,f81])).
% 0.21/0.43  fof(f401,plain,(
% 0.21/0.43    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl7_39),
% 0.21/0.43    inference(resolution,[],[f393,f53])).
% 0.21/0.43  fof(f53,plain,(
% 0.21/0.43    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f22])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.43  fof(f393,plain,(
% 0.21/0.43    ~v1_relat_1(sK2) | spl7_39),
% 0.21/0.43    inference(avatar_component_clause,[],[f392])).
% 0.21/0.43  fof(f395,plain,(
% 0.21/0.43    ~spl7_39 | spl7_7 | ~spl7_19),
% 0.21/0.43    inference(avatar_split_clause,[],[f382,f224,f122,f392])).
% 0.21/0.43  fof(f122,plain,(
% 0.21/0.43    spl7_7 <=> k1_xboole_0 = k2_relat_1(sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.43  fof(f224,plain,(
% 0.21/0.43    spl7_19 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.21/0.43  fof(f382,plain,(
% 0.21/0.43    k1_xboole_0 = k2_relat_1(sK2) | ~v1_relat_1(sK2) | ~spl7_19),
% 0.21/0.43    inference(trivial_inequality_removal,[],[f372])).
% 0.21/0.43  fof(f372,plain,(
% 0.21/0.43    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_relat_1(sK2) | ~v1_relat_1(sK2) | ~spl7_19),
% 0.21/0.43    inference(superposition,[],[f51,f225])).
% 0.21/0.43  fof(f225,plain,(
% 0.21/0.43    k1_xboole_0 = k1_relat_1(sK2) | ~spl7_19),
% 0.21/0.43    inference(avatar_component_clause,[],[f224])).
% 0.21/0.43  fof(f51,plain,(
% 0.21/0.43    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f33])).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.43    inference(nnf_transformation,[],[f21])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f10])).
% 0.21/0.43  fof(f10,axiom,(
% 0.21/0.43    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).
% 0.21/0.43  fof(f353,plain,(
% 0.21/0.43    spl7_19 | ~spl7_8 | ~spl7_18),
% 0.21/0.43    inference(avatar_split_clause,[],[f228,f221,f156,f224])).
% 0.21/0.43  fof(f156,plain,(
% 0.21/0.43    spl7_8 <=> m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.21/0.43  fof(f221,plain,(
% 0.21/0.43    spl7_18 <=> ! [X1] : (~r2_hidden(sK3(sK2,k1_xboole_0),X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK1)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.21/0.43  fof(f228,plain,(
% 0.21/0.43    ~m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1)) | k1_xboole_0 = k1_relat_1(sK2) | ~spl7_18),
% 0.21/0.43    inference(resolution,[],[f222,f190])).
% 0.21/0.43  fof(f190,plain,(
% 0.21/0.43    ( ! [X0] : (r2_hidden(sK3(X0,k1_xboole_0),k1_relat_1(X0)) | k1_xboole_0 = k1_relat_1(X0)) )),
% 0.21/0.43    inference(resolution,[],[f188,f71])).
% 0.21/0.43  fof(f71,plain,(
% 0.21/0.43    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X5,X6),X0) | r2_hidden(X5,k1_relat_1(X0))) )),
% 0.21/0.43    inference(equality_resolution,[],[f59])).
% 0.21/0.43  fof(f59,plain,(
% 0.21/0.43    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 0.21/0.43    inference(cnf_transformation,[],[f40])).
% 0.21/0.43  fof(f40,plain,(
% 0.21/0.43    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f36,f39,f38,f37])).
% 0.21/0.43  fof(f37,plain,(
% 0.21/0.43    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f38,plain,(
% 0.21/0.43    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f39,plain,(
% 0.21/0.43    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f36,plain,(
% 0.21/0.43    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.21/0.43    inference(rectify,[],[f35])).
% 0.21/0.43  fof(f35,plain,(
% 0.21/0.43    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 0.21/0.43    inference(nnf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,axiom,(
% 0.21/0.43    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 0.21/0.43  fof(f188,plain,(
% 0.21/0.43    ( ! [X0] : (r2_hidden(k4_tarski(sK3(X0,k1_xboole_0),sK4(X0,k1_xboole_0)),X0) | k1_xboole_0 = k1_relat_1(X0)) )),
% 0.21/0.43    inference(resolution,[],[f145,f50])).
% 0.21/0.43  fof(f50,plain,(
% 0.21/0.43    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.43  fof(f145,plain,(
% 0.21/0.43    ( ! [X4,X3] : (~r1_tarski(X4,sK3(X3,X4)) | k1_relat_1(X3) = X4 | r2_hidden(k4_tarski(sK3(X3,X4),sK4(X3,X4)),X3)) )),
% 0.21/0.43    inference(resolution,[],[f60,f66])).
% 0.21/0.43  fof(f66,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f25])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,axiom,(
% 0.21/0.43    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.43  fof(f60,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) | k1_relat_1(X0) = X1) )),
% 0.21/0.43    inference(cnf_transformation,[],[f40])).
% 0.21/0.43  fof(f222,plain,(
% 0.21/0.43    ( ! [X1] : (~r2_hidden(sK3(sK2,k1_xboole_0),X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK1))) ) | ~spl7_18),
% 0.21/0.43    inference(avatar_component_clause,[],[f221])).
% 0.21/0.43  fof(f351,plain,(
% 0.21/0.43    spl7_35 | spl7_10 | spl7_8),
% 0.21/0.43    inference(avatar_split_clause,[],[f346,f156,f165,f349])).
% 0.21/0.43  fof(f165,plain,(
% 0.21/0.43    spl7_10 <=> ! [X3,X2] : ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.21/0.43  fof(f346,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))) ) | spl7_8),
% 0.21/0.43    inference(resolution,[],[f142,f157])).
% 0.21/0.43  fof(f157,plain,(
% 0.21/0.43    ~m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1)) | spl7_8),
% 0.21/0.43    inference(avatar_component_clause,[],[f156])).
% 0.21/0.43  fof(f142,plain,(
% 0.21/0.43    ( ! [X14,X12,X10,X13,X11] : (m1_subset_1(k1_relat_1(X10),k1_zfmisc_1(X11)) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))) )),
% 0.21/0.43    inference(resolution,[],[f138,f57])).
% 0.21/0.43  fof(f57,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f24])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.21/0.43  fof(f138,plain,(
% 0.21/0.43    ( ! [X6,X8,X7,X5,X9] : (r2_hidden(k1_relat_1(X5),k1_zfmisc_1(X8)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) )),
% 0.21/0.43    inference(resolution,[],[f135,f73])).
% 0.21/0.43  fof(f73,plain,(
% 0.21/0.43    ( ! [X0,X3] : (~r1_tarski(X3,X0) | r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 0.21/0.43    inference(equality_resolution,[],[f63])).
% 0.21/0.43  fof(f63,plain,(
% 0.21/0.43    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.43    inference(cnf_transformation,[],[f44])).
% 0.21/0.43  fof(f44,plain,(
% 0.21/0.43    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK6(X0,X1),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (r1_tarski(sK6(X0,X1),X0) | r2_hidden(sK6(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f42,f43])).
% 0.21/0.43  fof(f43,plain,(
% 0.21/0.43    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK6(X0,X1),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (r1_tarski(sK6(X0,X1),X0) | r2_hidden(sK6(X0,X1),X1))))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f42,plain,(
% 0.21/0.43    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.43    inference(rectify,[],[f41])).
% 0.21/0.43  fof(f41,plain,(
% 0.21/0.43    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.43    inference(nnf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.21/0.43  fof(f135,plain,(
% 0.21/0.43    ( ! [X4,X2,X0,X3,X1] : (r1_tarski(k1_relat_1(X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.21/0.43    inference(resolution,[],[f118,f54])).
% 0.21/0.43  fof(f118,plain,(
% 0.21/0.43    ( ! [X6,X4,X7,X5] : (~v1_relat_1(X7) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~m1_subset_1(X4,k1_zfmisc_1(X7)) | r1_tarski(k1_relat_1(X4),X5)) )),
% 0.21/0.43    inference(resolution,[],[f110,f53])).
% 0.21/0.43  fof(f110,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | r1_tarski(k1_relat_1(X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.21/0.43    inference(resolution,[],[f69,f55])).
% 0.21/0.43  fof(f55,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f34])).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(nnf_transformation,[],[f23])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,axiom,(
% 0.21/0.43    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.43  fof(f69,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f28])).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.43    inference(ennf_transformation,[],[f18])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.21/0.43    inference(pure_predicate_removal,[],[f12])).
% 0.21/0.43  fof(f12,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.43  fof(f226,plain,(
% 0.21/0.43    spl7_18 | spl7_19),
% 0.21/0.43    inference(avatar_split_clause,[],[f216,f224,f221])).
% 0.21/0.43  fof(f216,plain,(
% 0.21/0.43    ( ! [X1] : (k1_xboole_0 = k1_relat_1(sK2) | ~r2_hidden(sK3(sK2,k1_xboole_0),X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK1))) )),
% 0.21/0.43    inference(resolution,[],[f190,f126])).
% 0.21/0.43  fof(f126,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(sK2)) | ~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK1))) )),
% 0.21/0.43    inference(global_subsumption,[],[f45,f125])).
% 0.21/0.43  fof(f125,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(sK2)) | ~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))) )),
% 0.21/0.43    inference(superposition,[],[f115,f68])).
% 0.21/0.43  fof(f68,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f27])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.43    inference(ennf_transformation,[],[f13])).
% 0.21/0.43  fof(f13,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.43  fof(f115,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r2_hidden(X1,k1_relset_1(sK1,sK0,sK2)) | ~r2_hidden(X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK1))) )),
% 0.21/0.43    inference(resolution,[],[f70,f47])).
% 0.21/0.43  fof(f47,plain,(
% 0.21/0.43    ( ! [X3] : (~m1_subset_1(X3,sK1) | ~r2_hidden(X3,k1_relset_1(sK1,sK0,sK2))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f32])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    ! [X3] : (~r2_hidden(X3,k1_relset_1(sK1,sK0,sK2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k2_relset_1(sK1,sK0,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f31])).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    ? [X0,X1,X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => (! [X3] : (~r2_hidden(X3,k1_relset_1(sK1,sK0,sK2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k2_relset_1(sK1,sK0,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ? [X0,X1,X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.43    inference(flattening,[],[f19])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ? [X0,X1,X2] : ((! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.43    inference(ennf_transformation,[],[f17])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))),
% 0.21/0.43    inference(pure_predicate_removal,[],[f16])).
% 0.21/0.43  fof(f16,negated_conjecture,(
% 0.21/0.43    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 0.21/0.43    inference(negated_conjecture,[],[f15])).
% 0.21/0.43  fof(f15,conjecture,(
% 0.21/0.43    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relset_1)).
% 0.21/0.43  fof(f70,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f30])).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.43    inference(flattening,[],[f29])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.43    inference(ennf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.43  fof(f45,plain,(
% 0.21/0.43    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.43    inference(cnf_transformation,[],[f32])).
% 0.21/0.43  fof(f172,plain,(
% 0.21/0.43    ~spl7_2 | ~spl7_10),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f171])).
% 0.21/0.43  fof(f171,plain,(
% 0.21/0.43    $false | (~spl7_2 | ~spl7_10)),
% 0.21/0.43    inference(subsumption_resolution,[],[f81,f166])).
% 0.21/0.43  fof(f166,plain,(
% 0.21/0.43    ( ! [X2,X3] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) ) | ~spl7_10),
% 0.21/0.43    inference(avatar_component_clause,[],[f165])).
% 0.21/0.43  fof(f124,plain,(
% 0.21/0.43    ~spl7_2 | ~spl7_7 | spl7_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f119,f76,f122,f80])).
% 0.21/0.43  fof(f76,plain,(
% 0.21/0.43    spl7_1 <=> k1_xboole_0 = k2_relset_1(sK1,sK0,sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.43  fof(f119,plain,(
% 0.21/0.43    k1_xboole_0 != k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl7_1),
% 0.21/0.43    inference(superposition,[],[f77,f67])).
% 0.21/0.43  fof(f67,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f26])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.43    inference(ennf_transformation,[],[f14])).
% 0.21/0.43  fof(f14,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.43  fof(f77,plain,(
% 0.21/0.43    k1_xboole_0 != k2_relset_1(sK1,sK0,sK2) | spl7_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f76])).
% 0.21/0.43  fof(f82,plain,(
% 0.21/0.43    spl7_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f45,f80])).
% 0.21/0.43  fof(f78,plain,(
% 0.21/0.43    ~spl7_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f46,f76])).
% 0.21/0.43  fof(f46,plain,(
% 0.21/0.43    k1_xboole_0 != k2_relset_1(sK1,sK0,sK2)),
% 0.21/0.43    inference(cnf_transformation,[],[f32])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (5540)------------------------------
% 0.21/0.43  % (5540)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (5540)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (5540)Memory used [KB]: 11001
% 0.21/0.43  % (5540)Time elapsed: 0.018 s
% 0.21/0.43  % (5540)------------------------------
% 0.21/0.43  % (5540)------------------------------
% 0.21/0.44  % (5533)Success in time 0.075 s
%------------------------------------------------------------------------------
