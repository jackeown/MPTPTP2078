%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : setfam_1__t4_setfam_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:18 EDT 2019

% Result     : Theorem 1.30s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 124 expanded)
%              Number of leaves         :   15 (  37 expanded)
%              Depth                    :   14
%              Number of atoms          :  227 ( 469 expanded)
%              Number of equality atoms :   50 (  89 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f577,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f419,f470,f576])).

fof(f576,plain,(
    ~ spl7_26 ),
    inference(avatar_contradiction_clause,[],[f575])).

fof(f575,plain,
    ( $false
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f572,f49])).

fof(f49,plain,(
    ~ r1_tarski(k1_setfam_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ~ r1_tarski(k1_setfam_1(sK1),sK0)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f33])).

fof(f33,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k1_setfam_1(X1),X0)
        & r2_hidden(X0,X1) )
   => ( ~ r1_tarski(k1_setfam_1(sK1),sK0)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_setfam_1(X1),X0)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => r1_tarski(k1_setfam_1(X1),X0) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t4_setfam_1.p',t4_setfam_1)).

fof(f572,plain,
    ( r1_tarski(k1_setfam_1(sK1),sK0)
    | ~ spl7_26 ),
    inference(resolution,[],[f499,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f44,f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t4_setfam_1.p',d3_tarski)).

fof(f499,plain,
    ( r2_hidden(sK6(k1_setfam_1(sK1),sK0),sK0)
    | ~ spl7_26 ),
    inference(resolution,[],[f418,f48])).

fof(f48,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f418,plain,
    ( ! [X10] :
        ( ~ r2_hidden(X10,sK1)
        | r2_hidden(sK6(k1_setfam_1(sK1),sK0),X10) )
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f417])).

fof(f417,plain,
    ( spl7_26
  <=> ! [X10] :
        ( ~ r2_hidden(X10,sK1)
        | r2_hidden(sK6(k1_setfam_1(sK1),sK0),X10) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f470,plain,(
    ~ spl7_24 ),
    inference(avatar_contradiction_clause,[],[f469])).

fof(f469,plain,
    ( $false
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f468,f83])).

fof(f83,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f70,f81])).

fof(f81,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f80,f50])).

fof(f50,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t4_setfam_1.p',dt_o_0_0_xboole_0)).

fof(f80,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(resolution,[],[f51,f50])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t4_setfam_1.p',t6_boole)).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t4_setfam_1.p',t7_boole)).

fof(f468,plain,
    ( r2_hidden(sK6(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl7_24 ),
    inference(forward_demodulation,[],[f441,f74])).

fof(f74,plain,(
    k1_setfam_1(k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( k1_setfam_1(X0) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(X0) = X1
      | k1_xboole_0 != X1
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ( ( ( ~ r2_hidden(sK3(X0,X1),sK4(X0,X1))
                  & r2_hidden(sK4(X0,X1),X0) )
                | ~ r2_hidden(sK3(X0,X1),X1) )
              & ( ! [X4] :
                    ( r2_hidden(sK3(X0,X1),X4)
                    | ~ r2_hidden(X4,X0) )
                | r2_hidden(sK3(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ( ~ r2_hidden(X5,sK5(X0,X5))
                    & r2_hidden(sK5(X0,X5),X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f38,f41,f40,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ~ r2_hidden(X2,X3)
                & r2_hidden(X3,X0) )
            | ~ r2_hidden(X2,X1) )
          & ( ! [X4] :
                ( r2_hidden(X2,X4)
                | ~ r2_hidden(X4,X0) )
            | r2_hidden(X2,X1) ) )
     => ( ( ? [X3] :
              ( ~ r2_hidden(sK3(X0,X1),X3)
              & r2_hidden(X3,X0) )
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ! [X4] :
              ( r2_hidden(sK3(X0,X1),X4)
              | ~ r2_hidden(X4,X0) )
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X2,X3)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(X2,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X5,X0] :
      ( ? [X6] :
          ( ~ r2_hidden(X5,X6)
          & r2_hidden(X6,X0) )
     => ( ~ r2_hidden(X5,sK5(X0,X5))
        & r2_hidden(sK5(X0,X5),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) )
                & ( ! [X4] :
                      ( r2_hidden(X2,X4)
                      | ~ r2_hidden(X4,X0) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ? [X6] :
                      ( ~ r2_hidden(X5,X6)
                      & r2_hidden(X6,X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r2_hidden(X3,X0) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) ) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 )
        | k1_xboole_0 != X0 )
      & ( ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r2_hidden(X3,X0) ) ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = X0
       => ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 ) )
      & ( k1_xboole_0 != X0
       => ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X3,X0)
                 => r2_hidden(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t4_setfam_1.p',d1_setfam_1)).

fof(f441,plain,
    ( r2_hidden(sK6(k1_setfam_1(k1_xboole_0),k1_xboole_0),k1_setfam_1(k1_xboole_0))
    | ~ spl7_24 ),
    inference(backward_demodulation,[],[f415,f109])).

fof(f109,plain,(
    r2_hidden(sK6(k1_setfam_1(sK1),k1_xboole_0),k1_setfam_1(sK1)) ),
    inference(resolution,[],[f106,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK6(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f106,plain,(
    ~ r1_tarski(k1_setfam_1(sK1),k1_xboole_0) ),
    inference(resolution,[],[f100,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t4_setfam_1.p',t3_subset)).

fof(f100,plain,(
    ~ m1_subset_1(k1_setfam_1(sK1),k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[],[f96,f92])).

fof(f92,plain,(
    r2_hidden(sK6(k1_setfam_1(sK1),sK0),k1_setfam_1(sK1)) ),
    inference(resolution,[],[f65,f49])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[],[f72,f81])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t4_setfam_1.p',t5_subset)).

fof(f415,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f414])).

fof(f414,plain,
    ( spl7_24
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f419,plain,
    ( spl7_24
    | spl7_26 ),
    inference(avatar_split_clause,[],[f405,f417,f414])).

fof(f405,plain,(
    ! [X10] :
      ( ~ r2_hidden(X10,sK1)
      | r2_hidden(sK6(k1_setfam_1(sK1),sK0),X10)
      | k1_xboole_0 = sK1 ) ),
    inference(resolution,[],[f79,f92])).

fof(f79,plain,(
    ! [X0,X7,X5] :
      ( ~ r2_hidden(X5,k1_setfam_1(X0))
      | ~ r2_hidden(X7,X0)
      | r2_hidden(X5,X7)
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X7,X5,X1] :
      ( r2_hidden(X5,X7)
      | ~ r2_hidden(X7,X0)
      | ~ r2_hidden(X5,X1)
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
