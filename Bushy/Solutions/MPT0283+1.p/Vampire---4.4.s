%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t84_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:12 EDT 2019

% Result     : Theorem 30.76s
% Output     : Refutation 30.76s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 169 expanded)
%              Number of leaves         :   30 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :  438 ( 702 expanded)
%              Number of equality atoms :   74 ( 103 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f58785,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f132,f195,f202,f8652,f9204,f29193,f53726,f58682,f58781,f58784])).

fof(f58784,plain,(
    spl7_1859 ),
    inference(avatar_contradiction_clause,[],[f58782])).

fof(f58782,plain,
    ( $false
    | ~ spl7_1859 ),
    inference(resolution,[],[f58780,f238])).

fof(f238,plain,(
    ! [X2,X1] : r2_hidden(X2,k2_xboole_0(k1_tarski(X2),X1)) ),
    inference(superposition,[],[f230,f84])).

fof(f84,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t84_zfmisc_1.p',commutativity_k2_xboole_0)).

fof(f230,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X0))) ),
    inference(resolution,[],[f126,f119])).

fof(f119,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f118])).

fof(f118,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f56,f57])).

fof(f57,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
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
    inference(rectify,[],[f55])).

fof(f55,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t84_zfmisc_1.p',d1_tarski)).

fof(f126,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f114])).

fof(f114,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
              & ~ r2_hidden(sK6(X0,X1,X2),X0) )
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( r2_hidden(sK6(X0,X1,X2),X1)
            | r2_hidden(sK6(X0,X1,X2),X0)
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f70,f71])).

fof(f71,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
            & ~ r2_hidden(sK6(X0,X1,X2),X0) )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( r2_hidden(sK6(X0,X1,X2),X1)
          | r2_hidden(sK6(X0,X1,X2),X0)
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t84_zfmisc_1.p',d3_xboole_0)).

fof(f58780,plain,
    ( ~ r2_hidden(k1_xboole_0,k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))))
    | ~ spl7_1859 ),
    inference(avatar_component_clause,[],[f58779])).

fof(f58779,plain,
    ( spl7_1859
  <=> ~ r2_hidden(k1_xboole_0,k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1859])])).

fof(f58781,plain,
    ( spl7_0
    | ~ spl7_1859
    | ~ spl7_1850 ),
    inference(avatar_split_clause,[],[f58759,f58680,f58779,f58776])).

fof(f58776,plain,
    ( spl7_0
  <=> r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_0])])).

fof(f58680,plain,
    ( spl7_1850
  <=> k1_xboole_0 = sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1850])])).

fof(f58759,plain,
    ( ~ r2_hidden(k1_xboole_0,k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))))
    | r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))))
    | ~ spl7_1850 ),
    inference(superposition,[],[f91,f58681])).

fof(f58681,plain,
    ( k1_xboole_0 = sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))))
    | ~ spl7_1850 ),
    inference(avatar_component_clause,[],[f58680])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f51,f52])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t84_zfmisc_1.p',d3_tarski)).

fof(f58682,plain,
    ( spl7_1850
    | ~ spl7_282
    | ~ spl7_1612 ),
    inference(avatar_split_clause,[],[f58678,f53724,f9202,f58680])).

fof(f9202,plain,
    ( spl7_282
  <=> k1_xboole_0 = k3_xboole_0(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_282])])).

fof(f53724,plain,
    ( spl7_1612
  <=> r1_tarski(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1612])])).

fof(f58678,plain,
    ( k1_xboole_0 = sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))))
    | ~ spl7_282
    | ~ spl7_1612 ),
    inference(forward_demodulation,[],[f58657,f9203])).

fof(f9203,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),sK1)
    | ~ spl7_282 ),
    inference(avatar_component_clause,[],[f9202])).

fof(f58657,plain,
    ( k3_xboole_0(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),sK1) = sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))))
    | ~ spl7_1612 ),
    inference(resolution,[],[f53725,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t84_zfmisc_1.p',t28_xboole_1)).

fof(f53725,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),sK1)
    | ~ spl7_1612 ),
    inference(avatar_component_clause,[],[f53724])).

fof(f53726,plain,
    ( spl7_1612
    | ~ spl7_1022 ),
    inference(avatar_split_clause,[],[f53718,f29191,f53724])).

fof(f29191,plain,
    ( spl7_1022
  <=> r2_hidden(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1022])])).

fof(f53718,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),sK1)
    | ~ spl7_1022 ),
    inference(resolution,[],[f29192,f122])).

fof(f122,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK4(X0,X1),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r1_tarski(sK4(X0,X1),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f60,f61])).

fof(f61,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK4(X0,X1),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( r1_tarski(sK4(X0,X1),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
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
    inference(rectify,[],[f59])).

fof(f59,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t84_zfmisc_1.p',d1_zfmisc_1)).

fof(f29192,plain,
    ( r2_hidden(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),k1_zfmisc_1(sK1))
    | ~ spl7_1022 ),
    inference(avatar_component_clause,[],[f29191])).

fof(f29193,plain,
    ( ~ spl7_257
    | spl7_1022
    | spl7_1 ),
    inference(avatar_split_clause,[],[f29162,f130,f29191,f29188])).

fof(f29188,plain,
    ( spl7_257
  <=> ~ r2_hidden(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_257])])).

fof(f130,plain,
    ( spl7_1
  <=> ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f29162,plain,
    ( r2_hidden(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),k1_zfmisc_1(sK1))
    | ~ r2_hidden(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),k1_zfmisc_1(sK0))
    | ~ spl7_1 ),
    inference(resolution,[],[f3986,f131])).

fof(f131,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f130])).

fof(f3986,plain,(
    ! [X92,X90,X91,X89] :
      ( r1_tarski(X89,k2_xboole_0(X90,k4_xboole_0(X91,X92)))
      | r2_hidden(sK2(X89,k2_xboole_0(X90,k4_xboole_0(X91,X92))),X92)
      | ~ r2_hidden(sK2(X89,k2_xboole_0(X90,k4_xboole_0(X91,X92))),X91) ) ),
    inference(resolution,[],[f570,f91])).

fof(f570,plain,(
    ! [X12,X10,X13,X11] :
      ( r2_hidden(X10,k2_xboole_0(X13,k4_xboole_0(X12,X11)))
      | ~ r2_hidden(X10,X12)
      | r2_hidden(X10,X11) ) ),
    inference(resolution,[],[f123,f126])).

fof(f123,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f108])).

fof(f108,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f65,f66])).

fof(f66,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t84_zfmisc_1.p',d5_xboole_0)).

fof(f9204,plain,
    ( spl7_282
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f9175,f200,f9202])).

fof(f200,plain,
    ( spl7_10
  <=> r1_tarski(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f9175,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),sK1)
    | ~ spl7_10 ),
    inference(resolution,[],[f3088,f201])).

fof(f201,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),k4_xboole_0(sK0,sK1))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f200])).

fof(f3088,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | k1_xboole_0 = k3_xboole_0(X0,X2) ) ),
    inference(resolution,[],[f481,f83])).

fof(f83,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t84_zfmisc_1.p',t79_xboole_1)).

fof(f481,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_xboole_0(X3,X4)
      | ~ r1_tarski(X5,X3)
      | k1_xboole_0 = k3_xboole_0(X5,X4) ) ),
    inference(resolution,[],[f105,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k3_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k1_xboole_0 != k3_xboole_0(X0,X1) )
      & ( k1_xboole_0 = k3_xboole_0(X0,X1)
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k1_xboole_0 = k3_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t84_zfmisc_1.p',d7_xboole_0)).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t84_zfmisc_1.p',t63_xboole_1)).

fof(f8652,plain,
    ( spl7_256
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f8631,f200,f8650])).

fof(f8650,plain,
    ( spl7_256
  <=> r2_hidden(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_256])])).

fof(f8631,plain,
    ( r2_hidden(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),k1_zfmisc_1(sK0))
    | ~ spl7_10 ),
    inference(resolution,[],[f2253,f201])).

fof(f2253,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X2,k4_xboole_0(X3,X4))
      | r2_hidden(X2,k1_zfmisc_1(X3)) ) ),
    inference(resolution,[],[f429,f82])).

fof(f82,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t84_zfmisc_1.p',t36_xboole_1)).

fof(f429,plain,(
    ! [X10,X8,X9] :
      ( ~ r1_tarski(X8,X9)
      | ~ r1_tarski(X10,X8)
      | r2_hidden(X10,k1_zfmisc_1(X9)) ) ),
    inference(resolution,[],[f104,f121])).

fof(f121,plain,(
    ! [X0,X3] :
      ( ~ r1_tarski(X3,X0)
      | r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f62])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t84_zfmisc_1.p',t1_xboole_1)).

fof(f202,plain,
    ( spl7_10
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f196,f193,f200])).

fof(f193,plain,
    ( spl7_8
  <=> r2_hidden(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),k1_zfmisc_1(k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f196,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),k4_xboole_0(sK0,sK1))
    | ~ spl7_8 ),
    inference(resolution,[],[f194,f122])).

fof(f194,plain,
    ( r2_hidden(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),k1_zfmisc_1(k4_xboole_0(sK0,sK1)))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f193])).

fof(f195,plain,
    ( spl7_8
    | spl7_1 ),
    inference(avatar_split_clause,[],[f189,f130,f193])).

fof(f189,plain,
    ( r2_hidden(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),k1_zfmisc_1(k4_xboole_0(sK0,sK1)))
    | ~ spl7_1 ),
    inference(resolution,[],[f90,f131])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f132,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f73,f130])).

fof(f73,plain,(
    ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f48])).

fof(f48,plain,
    ( ? [X0,X1] : ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(X0,X1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1))))
   => ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ? [X0,X1] : ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(X0,X1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k1_zfmisc_1(k4_xboole_0(X0,X1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] : r1_tarski(k1_zfmisc_1(k4_xboole_0(X0,X1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t84_zfmisc_1.p',t84_zfmisc_1)).
%------------------------------------------------------------------------------
