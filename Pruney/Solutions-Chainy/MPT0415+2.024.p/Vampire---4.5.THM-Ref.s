%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 230 expanded)
%              Number of leaves         :   11 (  60 expanded)
%              Depth                    :   22
%              Number of atoms          :  277 ( 966 expanded)
%              Number of equality atoms :   47 ( 317 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f375,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f228,f330,f334,f368])).

fof(f368,plain,
    ( spl3_6
    | ~ spl3_8 ),
    inference(avatar_contradiction_clause,[],[f357])).

fof(f357,plain,
    ( $false
    | spl3_6
    | ~ spl3_8 ),
    inference(resolution,[],[f350,f213])).

fof(f213,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,sK1),sK1)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f212])).

fof(f212,plain,
    ( spl3_6
  <=> r2_hidden(sK2(sK0,sK1,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f350,plain,
    ( ! [X0] : r2_hidden(sK2(sK0,sK1,sK1),X0)
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f347,f31])).

fof(f31,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f347,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(sK0,sK1,sK1),X0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )
    | ~ spl3_8 ),
    inference(resolution,[],[f223,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f223,plain,
    ( r2_hidden(sK2(sK0,sK1,sK1),k1_xboole_0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl3_8
  <=> r2_hidden(sK2(sK0,sK1,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f334,plain,
    ( spl3_6
    | spl3_9 ),
    inference(avatar_split_clause,[],[f333,f225,f212])).

fof(f225,plain,
    ( spl3_9
  <=> r2_hidden(k3_subset_1(sK0,sK2(sK0,sK1,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f333,plain,
    ( r2_hidden(k3_subset_1(sK0,sK2(sK0,sK1,sK1)),sK1)
    | r2_hidden(sK2(sK0,sK1,sK1),sK1) ),
    inference(subsumption_resolution,[],[f308,f23])).

fof(f23,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( k1_xboole_0 = k7_setfam_1(sK0,sK1)
    & k1_xboole_0 != sK1
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f15])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 = k7_setfam_1(X0,X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( k1_xboole_0 = k7_setfam_1(sK0,sK1)
      & k1_xboole_0 != sK1
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k7_setfam_1(X0,X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k7_setfam_1(X0,X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
            & k1_xboole_0 != X1 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).

fof(f308,plain,
    ( r2_hidden(k3_subset_1(sK0,sK2(sK0,sK1,sK1)),sK1)
    | r2_hidden(sK2(sK0,sK1,sK1),sK1)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f74,f22])).

fof(f22,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f74,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | r2_hidden(k3_subset_1(sK0,sK2(sK0,sK1,X1)),sK1)
      | r2_hidden(sK2(sK0,sK1,X1),X1)
      | k1_xboole_0 = X1 ) ),
    inference(subsumption_resolution,[],[f63,f22])).

fof(f63,plain,(
    ! [X1] :
      ( k1_xboole_0 = X1
      | r2_hidden(k3_subset_1(sK0,sK2(sK0,sK1,X1)),sK1)
      | r2_hidden(sK2(sK0,sK1,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    inference(superposition,[],[f24,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k7_setfam_1(X0,X1) = X2
      | r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1)
                  | ~ r2_hidden(sK2(X0,X1,X2),X2) )
                & ( r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1)
                  | r2_hidden(sK2(X0,X1,X2),X2) )
                & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(X0)) ) )
            & ( ! [X4] :
                  ( ( ( r2_hidden(X4,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X4),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X4),X1)
                      | ~ r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f20])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(k3_subset_1(X0,X3),X1)
            | r2_hidden(X3,X2) )
          & m1_subset_1(X3,k1_zfmisc_1(X0)) )
     => ( ( ~ r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1)
          | r2_hidden(sK2(X0,X1,X2),X2) )
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ? [X3] :
                  ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(k3_subset_1(X0,X3),X1)
                    | r2_hidden(X3,X2) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
            & ( ! [X4] :
                  ( ( ( r2_hidden(X4,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X4),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X4),X1)
                      | ~ r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ? [X3] :
                  ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(k3_subset_1(X0,X3),X1)
                    | r2_hidden(X3,X2) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
            & ( ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X3),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X3),X1)
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ? [X3] :
                  ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(k3_subset_1(X0,X3),X1)
                    | r2_hidden(X3,X2) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
            & ( ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X3),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X3),X1)
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).

fof(f24,plain,(
    k1_xboole_0 = k7_setfam_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f330,plain,(
    ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f329])).

fof(f329,plain,
    ( $false
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f328,f23])).

fof(f328,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f327,f24])).

fof(f327,plain,
    ( sK1 = k7_setfam_1(sK0,sK1)
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f326,f22])).

fof(f326,plain,
    ( sK1 = k7_setfam_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f324,f214])).

fof(f214,plain,
    ( r2_hidden(sK2(sK0,sK1,sK1),sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f212])).

fof(f324,plain,
    ( sK1 = k7_setfam_1(sK0,sK1)
    | ~ r2_hidden(sK2(sK0,sK1,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_6 ),
    inference(duplicate_literal_removal,[],[f313])).

fof(f313,plain,
    ( sK1 = k7_setfam_1(sK0,sK1)
    | ~ r2_hidden(sK2(sK0,sK1,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_6 ),
    inference(resolution,[],[f304,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k7_setfam_1(X0,X1) = X2
      | ~ r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f304,plain,
    ( ! [X0] : r2_hidden(k3_subset_1(sK0,sK2(sK0,sK1,sK1)),X0)
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f297,f31])).

fof(f297,plain,
    ( ! [X0] :
        ( r2_hidden(k3_subset_1(sK0,sK2(sK0,sK1,sK1)),X0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )
    | ~ spl3_6 ),
    inference(resolution,[],[f265,f33])).

fof(f265,plain,
    ( r2_hidden(k3_subset_1(sK0,sK2(sK0,sK1,sK1)),k1_xboole_0)
    | ~ spl3_6 ),
    inference(resolution,[],[f214,f199])).

fof(f199,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK1)
      | r2_hidden(k3_subset_1(sK0,X5),k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f110,f46])).

fof(f46,plain,(
    ! [X9] :
      ( ~ r2_hidden(X9,sK1)
      | m1_subset_1(X9,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f22,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f110,plain,(
    ! [X5] :
      ( r2_hidden(k3_subset_1(sK0,X5),k1_xboole_0)
      | ~ r2_hidden(X5,sK1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f109,f31])).

fof(f109,plain,(
    ! [X5] :
      ( r2_hidden(k3_subset_1(sK0,X5),k1_xboole_0)
      | ~ r2_hidden(X5,sK1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(sK0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f97,f22])).

fof(f97,plain,(
    ! [X5] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | r2_hidden(k3_subset_1(sK0,X5),k1_xboole_0)
      | ~ r2_hidden(X5,sK1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(sK0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    inference(superposition,[],[f35,f79])).

fof(f79,plain,(
    sK1 = k7_setfam_1(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f68,f22])).

fof(f68,plain,
    ( sK1 = k7_setfam_1(sK0,k1_xboole_0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(superposition,[],[f30,f24])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(f35,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ r2_hidden(X4,k7_setfam_1(X0,X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | k7_setfam_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f228,plain,
    ( spl3_8
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f206,f225,f221])).

fof(f206,plain,
    ( ~ r2_hidden(k3_subset_1(sK0,sK2(sK0,sK1,sK1)),sK1)
    | r2_hidden(sK2(sK0,sK1,sK1),k1_xboole_0) ),
    inference(resolution,[],[f204,f81])).

fof(f81,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(sK0))
      | ~ r2_hidden(k3_subset_1(sK0,X3),sK1)
      | r2_hidden(X3,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f80,f22])).

fof(f80,plain,(
    ! [X3] :
      ( r2_hidden(X3,k1_xboole_0)
      | ~ r2_hidden(k3_subset_1(sK0,X3),sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f69,f31])).

fof(f69,plain,(
    ! [X3] :
      ( r2_hidden(X3,k1_xboole_0)
      | ~ r2_hidden(k3_subset_1(sK0,X3),sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(sK0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    inference(superposition,[],[f34,f24])).

fof(f34,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k7_setfam_1(X0,X1))
      | ~ r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | k7_setfam_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f204,plain,(
    m1_subset_1(sK2(sK0,sK1,sK1),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f200,f23])).

fof(f200,plain,
    ( m1_subset_1(sK2(sK0,sK1,sK1),k1_zfmisc_1(sK0))
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f73,f22])).

fof(f73,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | m1_subset_1(sK2(sK0,sK1,X0),k1_zfmisc_1(sK0))
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f62,f22])).

fof(f62,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | m1_subset_1(sK2(sK0,sK1,X0),k1_zfmisc_1(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    inference(superposition,[],[f24,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k7_setfam_1(X0,X1) = X2
      | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:41:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.43  % (15570)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.44  % (15587)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.45  % (15587)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f375,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f228,f330,f334,f368])).
% 0.21/0.45  fof(f368,plain,(
% 0.21/0.45    spl3_6 | ~spl3_8),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f357])).
% 0.21/0.45  fof(f357,plain,(
% 0.21/0.45    $false | (spl3_6 | ~spl3_8)),
% 0.21/0.45    inference(resolution,[],[f350,f213])).
% 0.21/0.45  fof(f213,plain,(
% 0.21/0.45    ~r2_hidden(sK2(sK0,sK1,sK1),sK1) | spl3_6),
% 0.21/0.45    inference(avatar_component_clause,[],[f212])).
% 0.21/0.45  fof(f212,plain,(
% 0.21/0.45    spl3_6 <=> r2_hidden(sK2(sK0,sK1,sK1),sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.45  fof(f350,plain,(
% 0.21/0.45    ( ! [X0] : (r2_hidden(sK2(sK0,sK1,sK1),X0)) ) | ~spl3_8),
% 0.21/0.45    inference(subsumption_resolution,[],[f347,f31])).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.45  fof(f347,plain,(
% 0.21/0.45    ( ! [X0] : (r2_hidden(sK2(sK0,sK1,sK1),X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl3_8),
% 0.21/0.45    inference(resolution,[],[f223,f33])).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f14])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.45  fof(f223,plain,(
% 0.21/0.45    r2_hidden(sK2(sK0,sK1,sK1),k1_xboole_0) | ~spl3_8),
% 0.21/0.45    inference(avatar_component_clause,[],[f221])).
% 0.21/0.45  fof(f221,plain,(
% 0.21/0.45    spl3_8 <=> r2_hidden(sK2(sK0,sK1,sK1),k1_xboole_0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.45  fof(f334,plain,(
% 0.21/0.45    spl3_6 | spl3_9),
% 0.21/0.45    inference(avatar_split_clause,[],[f333,f225,f212])).
% 0.21/0.45  fof(f225,plain,(
% 0.21/0.45    spl3_9 <=> r2_hidden(k3_subset_1(sK0,sK2(sK0,sK1,sK1)),sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.45  fof(f333,plain,(
% 0.21/0.45    r2_hidden(k3_subset_1(sK0,sK2(sK0,sK1,sK1)),sK1) | r2_hidden(sK2(sK0,sK1,sK1),sK1)),
% 0.21/0.45    inference(subsumption_resolution,[],[f308,f23])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    k1_xboole_0 != sK1),
% 0.21/0.45    inference(cnf_transformation,[],[f16])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    k1_xboole_0 = k7_setfam_1(sK0,sK1) & k1_xboole_0 != sK1 & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ? [X0,X1] : (k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (k1_xboole_0 = k7_setfam_1(sK0,sK1) & k1_xboole_0 != sK1 & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f9,plain,(
% 0.21/0.45    ? [X0,X1] : (k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.45    inference(flattening,[],[f8])).
% 0.21/0.45  fof(f8,plain,(
% 0.21/0.45    ? [X0,X1] : ((k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.45    inference(ennf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,negated_conjecture,(
% 0.21/0.45    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1))),
% 0.21/0.45    inference(negated_conjecture,[],[f6])).
% 0.21/0.45  fof(f6,conjecture,(
% 0.21/0.45    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).
% 0.21/0.45  fof(f308,plain,(
% 0.21/0.45    r2_hidden(k3_subset_1(sK0,sK2(sK0,sK1,sK1)),sK1) | r2_hidden(sK2(sK0,sK1,sK1),sK1) | k1_xboole_0 = sK1),
% 0.21/0.45    inference(resolution,[],[f74,f22])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.45    inference(cnf_transformation,[],[f16])).
% 0.21/0.45  fof(f74,plain,(
% 0.21/0.45    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | r2_hidden(k3_subset_1(sK0,sK2(sK0,sK1,X1)),sK1) | r2_hidden(sK2(sK0,sK1,X1),X1) | k1_xboole_0 = X1) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f63,f22])).
% 0.21/0.45  fof(f63,plain,(
% 0.21/0.45    ( ! [X1] : (k1_xboole_0 = X1 | r2_hidden(k3_subset_1(sK0,sK2(sK0,sK1,X1)),sK1) | r2_hidden(sK2(sK0,sK1,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))) )),
% 0.21/0.45    inference(superposition,[],[f24,f28])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k7_setfam_1(X0,X1) = X2 | r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1) | r2_hidden(sK2(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f21])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ((~r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1) | r2_hidden(sK2(X0,X1,X2),X2)) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(X0)))) & (! [X4] : (((r2_hidden(X4,X2) | ~r2_hidden(k3_subset_1(X0,X4),X1)) & (r2_hidden(k3_subset_1(X0,X4),X1) | ~r2_hidden(X4,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f20])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0))) => ((~r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1) | r2_hidden(sK2(X0,X1,X2),X2)) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(X0))))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X4] : (((r2_hidden(X4,X2) | ~r2_hidden(k3_subset_1(X0,X4),X1)) & (r2_hidden(k3_subset_1(X0,X4),X1) | ~r2_hidden(X4,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.45    inference(rectify,[],[f18])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(k3_subset_1(X0,X3),X1)) & (r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.45    inference(flattening,[],[f17])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(k3_subset_1(X0,X3),X1)) & (r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.45    inference(nnf_transformation,[],[f10])).
% 0.21/0.45  fof(f10,plain,(
% 0.21/0.45    ! [X0,X1] : (! [X2] : ((k7_setfam_1(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.45    inference(ennf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k7_setfam_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1))))))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    k1_xboole_0 = k7_setfam_1(sK0,sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f16])).
% 0.21/0.45  fof(f330,plain,(
% 0.21/0.45    ~spl3_6),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f329])).
% 0.21/0.45  fof(f329,plain,(
% 0.21/0.45    $false | ~spl3_6),
% 0.21/0.45    inference(subsumption_resolution,[],[f328,f23])).
% 0.21/0.45  fof(f328,plain,(
% 0.21/0.45    k1_xboole_0 = sK1 | ~spl3_6),
% 0.21/0.45    inference(forward_demodulation,[],[f327,f24])).
% 0.21/0.45  fof(f327,plain,(
% 0.21/0.45    sK1 = k7_setfam_1(sK0,sK1) | ~spl3_6),
% 0.21/0.45    inference(subsumption_resolution,[],[f326,f22])).
% 0.21/0.45  fof(f326,plain,(
% 0.21/0.45    sK1 = k7_setfam_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_6),
% 0.21/0.45    inference(subsumption_resolution,[],[f324,f214])).
% 0.21/0.45  fof(f214,plain,(
% 0.21/0.45    r2_hidden(sK2(sK0,sK1,sK1),sK1) | ~spl3_6),
% 0.21/0.45    inference(avatar_component_clause,[],[f212])).
% 0.21/0.45  fof(f324,plain,(
% 0.21/0.45    sK1 = k7_setfam_1(sK0,sK1) | ~r2_hidden(sK2(sK0,sK1,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_6),
% 0.21/0.45    inference(duplicate_literal_removal,[],[f313])).
% 0.21/0.45  fof(f313,plain,(
% 0.21/0.45    sK1 = k7_setfam_1(sK0,sK1) | ~r2_hidden(sK2(sK0,sK1,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_6),
% 0.21/0.45    inference(resolution,[],[f304,f29])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k7_setfam_1(X0,X1) = X2 | ~r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1) | ~r2_hidden(sK2(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f21])).
% 0.21/0.45  fof(f304,plain,(
% 0.21/0.45    ( ! [X0] : (r2_hidden(k3_subset_1(sK0,sK2(sK0,sK1,sK1)),X0)) ) | ~spl3_6),
% 0.21/0.45    inference(subsumption_resolution,[],[f297,f31])).
% 0.21/0.45  fof(f297,plain,(
% 0.21/0.45    ( ! [X0] : (r2_hidden(k3_subset_1(sK0,sK2(sK0,sK1,sK1)),X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl3_6),
% 0.21/0.45    inference(resolution,[],[f265,f33])).
% 0.21/0.45  fof(f265,plain,(
% 0.21/0.45    r2_hidden(k3_subset_1(sK0,sK2(sK0,sK1,sK1)),k1_xboole_0) | ~spl3_6),
% 0.21/0.45    inference(resolution,[],[f214,f199])).
% 0.21/0.45  fof(f199,plain,(
% 0.21/0.45    ( ! [X5] : (~r2_hidden(X5,sK1) | r2_hidden(k3_subset_1(sK0,X5),k1_xboole_0)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f110,f46])).
% 0.21/0.45  fof(f46,plain,(
% 0.21/0.45    ( ! [X9] : (~r2_hidden(X9,sK1) | m1_subset_1(X9,k1_zfmisc_1(sK0))) )),
% 0.21/0.45    inference(resolution,[],[f22,f32])).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f13])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.45    inference(flattening,[],[f12])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.45    inference(ennf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.45  fof(f110,plain,(
% 0.21/0.45    ( ! [X5] : (r2_hidden(k3_subset_1(sK0,X5),k1_xboole_0) | ~r2_hidden(X5,sK1) | ~m1_subset_1(X5,k1_zfmisc_1(sK0))) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f109,f31])).
% 0.21/0.45  fof(f109,plain,(
% 0.21/0.45    ( ! [X5] : (r2_hidden(k3_subset_1(sK0,X5),k1_xboole_0) | ~r2_hidden(X5,sK1) | ~m1_subset_1(X5,k1_zfmisc_1(sK0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f97,f22])).
% 0.21/0.45  fof(f97,plain,(
% 0.21/0.45    ( ! [X5] : (~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | r2_hidden(k3_subset_1(sK0,X5),k1_xboole_0) | ~r2_hidden(X5,sK1) | ~m1_subset_1(X5,k1_zfmisc_1(sK0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))) )),
% 0.21/0.45    inference(superposition,[],[f35,f79])).
% 0.21/0.45  fof(f79,plain,(
% 0.21/0.45    sK1 = k7_setfam_1(sK0,k1_xboole_0)),
% 0.21/0.45    inference(subsumption_resolution,[],[f68,f22])).
% 0.21/0.45  fof(f68,plain,(
% 0.21/0.45    sK1 = k7_setfam_1(sK0,k1_xboole_0) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.45    inference(superposition,[],[f30,f24])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f11])).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.45    inference(ennf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    ( ! [X4,X0,X1] : (r2_hidden(k3_subset_1(X0,X4),X1) | ~r2_hidden(X4,k7_setfam_1(X0,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(X0)) | ~m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.45    inference(equality_resolution,[],[f25])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ( ! [X4,X2,X0,X1] : (r2_hidden(k3_subset_1(X0,X4),X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,k1_zfmisc_1(X0)) | k7_setfam_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f21])).
% 0.21/0.45  fof(f228,plain,(
% 0.21/0.45    spl3_8 | ~spl3_9),
% 0.21/0.45    inference(avatar_split_clause,[],[f206,f225,f221])).
% 0.21/0.45  fof(f206,plain,(
% 0.21/0.45    ~r2_hidden(k3_subset_1(sK0,sK2(sK0,sK1,sK1)),sK1) | r2_hidden(sK2(sK0,sK1,sK1),k1_xboole_0)),
% 0.21/0.45    inference(resolution,[],[f204,f81])).
% 0.21/0.45  fof(f81,plain,(
% 0.21/0.45    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(sK0)) | ~r2_hidden(k3_subset_1(sK0,X3),sK1) | r2_hidden(X3,k1_xboole_0)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f80,f22])).
% 0.21/0.45  fof(f80,plain,(
% 0.21/0.45    ( ! [X3] : (r2_hidden(X3,k1_xboole_0) | ~r2_hidden(k3_subset_1(sK0,X3),sK1) | ~m1_subset_1(X3,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f69,f31])).
% 0.21/0.45  fof(f69,plain,(
% 0.21/0.45    ( ! [X3] : (r2_hidden(X3,k1_xboole_0) | ~r2_hidden(k3_subset_1(sK0,X3),sK1) | ~m1_subset_1(X3,k1_zfmisc_1(sK0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))) )),
% 0.21/0.45    inference(superposition,[],[f34,f24])).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    ( ! [X4,X0,X1] : (r2_hidden(X4,k7_setfam_1(X0,X1)) | ~r2_hidden(k3_subset_1(X0,X4),X1) | ~m1_subset_1(X4,k1_zfmisc_1(X0)) | ~m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.45    inference(equality_resolution,[],[f26])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(k3_subset_1(X0,X4),X1) | ~m1_subset_1(X4,k1_zfmisc_1(X0)) | k7_setfam_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f21])).
% 0.21/0.45  fof(f204,plain,(
% 0.21/0.45    m1_subset_1(sK2(sK0,sK1,sK1),k1_zfmisc_1(sK0))),
% 0.21/0.45    inference(subsumption_resolution,[],[f200,f23])).
% 0.21/0.45  fof(f200,plain,(
% 0.21/0.45    m1_subset_1(sK2(sK0,sK1,sK1),k1_zfmisc_1(sK0)) | k1_xboole_0 = sK1),
% 0.21/0.45    inference(resolution,[],[f73,f22])).
% 0.21/0.45  fof(f73,plain,(
% 0.21/0.45    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | m1_subset_1(sK2(sK0,sK1,X0),k1_zfmisc_1(sK0)) | k1_xboole_0 = X0) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f62,f22])).
% 0.21/0.45  fof(f62,plain,(
% 0.21/0.45    ( ! [X0] : (k1_xboole_0 = X0 | m1_subset_1(sK2(sK0,sK1,X0),k1_zfmisc_1(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))) )),
% 0.21/0.45    inference(superposition,[],[f24,f27])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k7_setfam_1(X0,X1) = X2 | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f21])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (15587)------------------------------
% 0.21/0.45  % (15587)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (15587)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (15587)Memory used [KB]: 6268
% 0.21/0.45  % (15587)Time elapsed: 0.049 s
% 0.21/0.45  % (15587)------------------------------
% 0.21/0.45  % (15587)------------------------------
% 0.21/0.45  % (15567)Success in time 0.09 s
%------------------------------------------------------------------------------
