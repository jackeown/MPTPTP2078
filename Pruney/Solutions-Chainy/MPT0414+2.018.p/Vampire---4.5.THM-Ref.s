%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:20 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 172 expanded)
%              Number of leaves         :   20 (  73 expanded)
%              Depth                    :    9
%              Number of atoms          :  283 ( 734 expanded)
%              Number of equality atoms :   21 (  68 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f116,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f44,f48,f66,f79,f86,f90,f92,f98,f104,f112,f115])).

fof(f115,plain,
    ( ~ spl5_4
    | spl5_11 ),
    inference(avatar_split_clause,[],[f113,f110,f60])).

fof(f60,plain,
    ( spl5_4
  <=> r2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f110,plain,
    ( spl5_11
  <=> r2_hidden(sK4(sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f113,plain,
    ( ~ r2_xboole_0(sK1,sK2)
    | spl5_11 ),
    inference(resolution,[],[f111,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r2_hidden(sK4(X0,X1),X0)
        & r2_hidden(sK4(X0,X1),X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(sK4(X0,X1),X0)
        & r2_hidden(sK4(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).

fof(f111,plain,
    ( ~ r2_hidden(sK4(sK1,sK2),sK2)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f110])).

fof(f112,plain,
    ( spl5_9
    | ~ spl5_11
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f105,f102,f110,f96])).

fof(f96,plain,
    ( spl5_9
  <=> r2_hidden(sK4(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f102,plain,
    ( spl5_10
  <=> m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f105,plain,
    ( ~ r2_hidden(sK4(sK1,sK2),sK2)
    | r2_hidden(sK4(sK1,sK2),sK1)
    | ~ spl5_10 ),
    inference(resolution,[],[f103,f28])).

fof(f28,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(sK0))
      | ~ r2_hidden(X3,sK2)
      | r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( sK1 != sK2
    & ! [X3] :
        ( ( ( r2_hidden(X3,sK1)
            | ~ r2_hidden(X3,sK2) )
          & ( r2_hidden(X3,sK2)
            | ~ r2_hidden(X3,sK1) ) )
        | ~ m1_subset_1(X3,k1_zfmisc_1(sK0)) )
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f19,f18])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( X1 != X2
            & ! [X3] :
                ( ( ( r2_hidden(X3,X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(X3,X2)
                    | ~ r2_hidden(X3,X1) ) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ? [X2] :
          ( sK1 != X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,sK1)
                  | ~ r2_hidden(X3,X2) )
                & ( r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,sK1) ) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(sK0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X2] :
        ( sK1 != X2
        & ! [X3] :
            ( ( ( r2_hidden(X3,sK1)
                | ~ r2_hidden(X3,X2) )
              & ( r2_hidden(X3,X2)
                | ~ r2_hidden(X3,sK1) ) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(sK0)) )
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
   => ( sK1 != sK2
      & ! [X3] :
          ( ( ( r2_hidden(X3,sK1)
              | ~ r2_hidden(X3,sK2) )
            & ( r2_hidden(X3,sK2)
              | ~ r2_hidden(X3,sK1) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,X1)
                  | ~ r2_hidden(X3,X2) )
                & ( r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,X1) ) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(X0))
                 => ( r2_hidden(X3,X1)
                  <=> r2_hidden(X3,X2) ) )
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_setfam_1)).

fof(f103,plain,
    ( m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(sK0))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f102])).

fof(f104,plain,
    ( spl5_10
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f100,f60,f42,f102])).

fof(f42,plain,
    ( spl5_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f100,plain,
    ( m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(sK0))
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(resolution,[],[f93,f43])).

fof(f43,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f93,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | m1_subset_1(sK4(sK1,sK2),X0) )
    | ~ spl5_4 ),
    inference(resolution,[],[f61,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_xboole_0(X2,X0)
      | m1_subset_1(sK4(X2,X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f36,f34])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f61,plain,
    ( r2_xboole_0(sK1,sK2)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f98,plain,
    ( ~ spl5_9
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f94,f60,f96])).

fof(f94,plain,
    ( ~ r2_hidden(sK4(sK1,sK2),sK1)
    | ~ spl5_4 ),
    inference(resolution,[],[f61,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | ~ r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f92,plain,
    ( spl5_4
    | spl5_1
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f91,f84,f38,f60])).

fof(f38,plain,
    ( spl5_1
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f84,plain,
    ( spl5_8
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f91,plain,
    ( sK1 = sK2
    | r2_xboole_0(sK1,sK2)
    | ~ spl5_8 ),
    inference(resolution,[],[f85,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f85,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f84])).

fof(f90,plain,
    ( ~ spl5_3
    | ~ spl5_2
    | spl5_8
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f88,f74,f84,f42,f46])).

fof(f46,plain,
    ( spl5_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f74,plain,
    ( spl5_7
  <=> r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f88,plain,
    ( r1_tarski(sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl5_7 ),
    inference(resolution,[],[f77,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X2)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ( ~ r2_hidden(sK3(X0,X1,X2),X2)
            & r2_hidden(sK3(X0,X1,X2),X1)
            & m1_subset_1(sK3(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f11,f21])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
     => ( ~ r2_hidden(sK3(X0,X1,X2),X2)
        & r2_hidden(sK3(X0,X1,X2),X1)
        & m1_subset_1(sK3(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).

fof(f77,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK2)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f74])).

fof(f86,plain,
    ( ~ spl5_3
    | ~ spl5_2
    | spl5_8
    | spl5_6 ),
    inference(avatar_split_clause,[],[f80,f71,f84,f42,f46])).

fof(f71,plain,
    ( spl5_6
  <=> r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f80,plain,
    ( r1_tarski(sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl5_6 ),
    inference(resolution,[],[f78,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X1)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f78,plain,
    ( ~ r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK1)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f71])).

fof(f79,plain,
    ( spl5_7
    | ~ spl5_6
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f68,f64,f71,f74])).

fof(f64,plain,
    ( spl5_5
  <=> m1_subset_1(sK3(k1_zfmisc_1(sK0),sK1,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f68,plain,
    ( ~ r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK1)
    | r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK2)
    | ~ spl5_5 ),
    inference(resolution,[],[f65,f27])).

fof(f27,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(sK0))
      | ~ r2_hidden(X3,sK1)
      | r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f65,plain,
    ( m1_subset_1(sK3(k1_zfmisc_1(sK0),sK1,sK2),k1_zfmisc_1(sK0))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f64])).

fof(f66,plain,
    ( spl5_4
    | spl5_1
    | spl5_5
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f58,f46,f42,f64,f38,f60])).

fof(f58,plain,
    ( m1_subset_1(sK3(k1_zfmisc_1(sK0),sK1,sK2),k1_zfmisc_1(sK0))
    | sK1 = sK2
    | r2_xboole_0(sK1,sK2)
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(resolution,[],[f55,f47])).

fof(f47,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f46])).

fof(f55,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | m1_subset_1(sK3(k1_zfmisc_1(sK0),X0,sK2),k1_zfmisc_1(sK0))
        | sK2 = X0
        | r2_xboole_0(X0,sK2) )
    | ~ spl5_2 ),
    inference(resolution,[],[f50,f43])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(sK3(X0,X1,X2),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X1 = X2
      | r2_xboole_0(X1,X2) ) ),
    inference(resolution,[],[f30,f33])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | m1_subset_1(sK3(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f48,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f25,f46])).

fof(f25,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f44,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f26,f42])).

fof(f26,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f40,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f29,f38])).

fof(f29,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:28:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (1614)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.48  % (1614)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % (1624)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.48  % (1623)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f116,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f40,f44,f48,f66,f79,f86,f90,f92,f98,f104,f112,f115])).
% 0.22/0.48  fof(f115,plain,(
% 0.22/0.48    ~spl5_4 | spl5_11),
% 0.22/0.48    inference(avatar_split_clause,[],[f113,f110,f60])).
% 0.22/0.48  fof(f60,plain,(
% 0.22/0.48    spl5_4 <=> r2_xboole_0(sK1,sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.48  fof(f110,plain,(
% 0.22/0.48    spl5_11 <=> r2_hidden(sK4(sK1,sK2),sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.22/0.48  fof(f113,plain,(
% 0.22/0.48    ~r2_xboole_0(sK1,sK2) | spl5_11),
% 0.22/0.48    inference(resolution,[],[f111,f34])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | ~r2_xboole_0(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ! [X0,X1] : ((~r2_hidden(sK4(X0,X1),X0) & r2_hidden(sK4(X0,X1),X1)) | ~r2_xboole_0(X0,X1))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) => (~r2_hidden(sK4(X0,X1),X0) & r2_hidden(sK4(X0,X1),X1)))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | ~r2_xboole_0(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : ~(! [X2] : ~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & r2_xboole_0(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).
% 0.22/0.48  fof(f111,plain,(
% 0.22/0.48    ~r2_hidden(sK4(sK1,sK2),sK2) | spl5_11),
% 0.22/0.48    inference(avatar_component_clause,[],[f110])).
% 0.22/0.48  fof(f112,plain,(
% 0.22/0.48    spl5_9 | ~spl5_11 | ~spl5_10),
% 0.22/0.48    inference(avatar_split_clause,[],[f105,f102,f110,f96])).
% 0.22/0.48  fof(f96,plain,(
% 0.22/0.48    spl5_9 <=> r2_hidden(sK4(sK1,sK2),sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.22/0.48  fof(f102,plain,(
% 0.22/0.48    spl5_10 <=> m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.22/0.48  fof(f105,plain,(
% 0.22/0.48    ~r2_hidden(sK4(sK1,sK2),sK2) | r2_hidden(sK4(sK1,sK2),sK1) | ~spl5_10),
% 0.22/0.48    inference(resolution,[],[f103,f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(sK0)) | ~r2_hidden(X3,sK2) | r2_hidden(X3,sK1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    (sK1 != sK2 & ! [X3] : (((r2_hidden(X3,sK1) | ~r2_hidden(X3,sK2)) & (r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f19,f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ? [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : (sK1 != X2 & ! [X3] : (((r2_hidden(X3,sK1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ? [X2] : (sK1 != X2 & ! [X3] : (((r2_hidden(X3,sK1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) => (sK1 != sK2 & ! [X3] : (((r2_hidden(X3,sK1) | ~r2_hidden(X3,sK2)) & (r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ? [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.48    inference(nnf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ? [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : ((r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.48    inference(flattening,[],[f8])).
% 0.22/0.48  fof(f8,plain,(
% 0.22/0.48    ? [X0,X1] : (? [X2] : ((X1 != X2 & ! [X3] : ((r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 0.22/0.48    inference(negated_conjecture,[],[f5])).
% 0.22/0.48  fof(f5,conjecture,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_setfam_1)).
% 0.22/0.48  fof(f103,plain,(
% 0.22/0.48    m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(sK0)) | ~spl5_10),
% 0.22/0.48    inference(avatar_component_clause,[],[f102])).
% 0.22/0.48  fof(f104,plain,(
% 0.22/0.48    spl5_10 | ~spl5_2 | ~spl5_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f100,f60,f42,f102])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    spl5_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.48  fof(f100,plain,(
% 0.22/0.48    m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(sK0)) | (~spl5_2 | ~spl5_4)),
% 0.22/0.48    inference(resolution,[],[f93,f43])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl5_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f42])).
% 0.22/0.48  fof(f93,plain,(
% 0.22/0.48    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | m1_subset_1(sK4(sK1,sK2),X0)) ) | ~spl5_4),
% 0.22/0.48    inference(resolution,[],[f61,f49])).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r2_xboole_0(X2,X0) | m1_subset_1(sK4(X2,X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.48    inference(resolution,[],[f36,f34])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.48    inference(flattening,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    r2_xboole_0(sK1,sK2) | ~spl5_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f60])).
% 0.22/0.48  fof(f98,plain,(
% 0.22/0.48    ~spl5_9 | ~spl5_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f94,f60,f96])).
% 0.22/0.48  fof(f94,plain,(
% 0.22/0.48    ~r2_hidden(sK4(sK1,sK2),sK1) | ~spl5_4),
% 0.22/0.48    inference(resolution,[],[f61,f35])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | ~r2_hidden(sK4(X0,X1),X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f24])).
% 0.22/0.48  fof(f92,plain,(
% 0.22/0.48    spl5_4 | spl5_1 | ~spl5_8),
% 0.22/0.48    inference(avatar_split_clause,[],[f91,f84,f38,f60])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    spl5_1 <=> sK1 = sK2),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.48  fof(f84,plain,(
% 0.22/0.48    spl5_8 <=> r1_tarski(sK1,sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.22/0.48  fof(f91,plain,(
% 0.22/0.48    sK1 = sK2 | r2_xboole_0(sK1,sK2) | ~spl5_8),
% 0.22/0.48    inference(resolution,[],[f85,f33])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.48    inference(flattening,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,plain,(
% 0.22/0.48    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 0.22/0.48    inference(unused_predicate_definition_removal,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.22/0.48  fof(f85,plain,(
% 0.22/0.48    r1_tarski(sK1,sK2) | ~spl5_8),
% 0.22/0.48    inference(avatar_component_clause,[],[f84])).
% 0.22/0.48  fof(f90,plain,(
% 0.22/0.48    ~spl5_3 | ~spl5_2 | spl5_8 | ~spl5_7),
% 0.22/0.48    inference(avatar_split_clause,[],[f88,f74,f84,f42,f46])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    spl5_3 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.48  fof(f74,plain,(
% 0.22/0.48    spl5_7 <=> r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.48  fof(f88,plain,(
% 0.22/0.48    r1_tarski(sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl5_7),
% 0.22/0.48    inference(resolution,[],[f77,f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X2) | r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | (~r2_hidden(sK3(X0,X1,X2),X2) & r2_hidden(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f11,f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) => (~r2_hidden(sK3(X0,X1,X2),X2) & r2_hidden(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),X0)))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.48    inference(flattening,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : ((~r2_hidden(X3,X2) & r2_hidden(X3,X1)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).
% 0.22/0.48  fof(f77,plain,(
% 0.22/0.48    r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK2) | ~spl5_7),
% 0.22/0.48    inference(avatar_component_clause,[],[f74])).
% 0.22/0.48  fof(f86,plain,(
% 0.22/0.48    ~spl5_3 | ~spl5_2 | spl5_8 | spl5_6),
% 0.22/0.48    inference(avatar_split_clause,[],[f80,f71,f84,f42,f46])).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    spl5_6 <=> r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.48  fof(f80,plain,(
% 0.22/0.48    r1_tarski(sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl5_6),
% 0.22/0.48    inference(resolution,[],[f78,f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X1) | r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  fof(f78,plain,(
% 0.22/0.48    ~r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK1) | spl5_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f71])).
% 0.22/0.48  fof(f79,plain,(
% 0.22/0.48    spl5_7 | ~spl5_6 | ~spl5_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f68,f64,f71,f74])).
% 0.22/0.48  fof(f64,plain,(
% 0.22/0.48    spl5_5 <=> m1_subset_1(sK3(k1_zfmisc_1(sK0),sK1,sK2),k1_zfmisc_1(sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    ~r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK1) | r2_hidden(sK3(k1_zfmisc_1(sK0),sK1,sK2),sK2) | ~spl5_5),
% 0.22/0.48    inference(resolution,[],[f65,f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(sK0)) | ~r2_hidden(X3,sK1) | r2_hidden(X3,sK2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f20])).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    m1_subset_1(sK3(k1_zfmisc_1(sK0),sK1,sK2),k1_zfmisc_1(sK0)) | ~spl5_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f64])).
% 0.22/0.48  fof(f66,plain,(
% 0.22/0.48    spl5_4 | spl5_1 | spl5_5 | ~spl5_2 | ~spl5_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f58,f46,f42,f64,f38,f60])).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    m1_subset_1(sK3(k1_zfmisc_1(sK0),sK1,sK2),k1_zfmisc_1(sK0)) | sK1 = sK2 | r2_xboole_0(sK1,sK2) | (~spl5_2 | ~spl5_3)),
% 0.22/0.48    inference(resolution,[],[f55,f47])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl5_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f46])).
% 0.22/0.48  fof(f55,plain,(
% 0.22/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | m1_subset_1(sK3(k1_zfmisc_1(sK0),X0,sK2),k1_zfmisc_1(sK0)) | sK2 = X0 | r2_xboole_0(X0,sK2)) ) | ~spl5_2),
% 0.22/0.48    inference(resolution,[],[f50,f43])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | m1_subset_1(sK3(X0,X1,X2),X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | X1 = X2 | r2_xboole_0(X1,X2)) )),
% 0.22/0.48    inference(resolution,[],[f30,f33])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | m1_subset_1(sK3(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    spl5_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f25,f46])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.48    inference(cnf_transformation,[],[f20])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    spl5_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f26,f42])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.48    inference(cnf_transformation,[],[f20])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    ~spl5_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f29,f38])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    sK1 != sK2),
% 0.22/0.48    inference(cnf_transformation,[],[f20])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (1614)------------------------------
% 0.22/0.48  % (1614)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (1614)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (1614)Memory used [KB]: 10618
% 0.22/0.48  % (1614)Time elapsed: 0.056 s
% 0.22/0.48  % (1614)------------------------------
% 0.22/0.48  % (1614)------------------------------
% 0.22/0.48  % (1615)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.49  % (1606)Success in time 0.122 s
%------------------------------------------------------------------------------
