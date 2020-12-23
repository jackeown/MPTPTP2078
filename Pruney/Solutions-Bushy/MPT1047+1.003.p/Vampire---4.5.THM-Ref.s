%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1047+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:09 EST 2020

% Result     : Theorem 1.67s
% Output     : Refutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 536 expanded)
%              Number of leaves         :   17 ( 168 expanded)
%              Depth                    :   29
%              Number of atoms          :  545 (3099 expanded)
%              Number of equality atoms :   87 ( 489 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1210,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1209,f91])).

fof(f91,plain,(
    sP2(sK5,sK3,k1_tarski(sK4)) ),
    inference(subsumption_resolution,[],[f89,f48])).

fof(f48,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( k5_partfun1(sK3,k1_tarski(sK4),sK5) != k1_tarski(sK6)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4))))
    & v1_funct_2(sK6,sK3,k1_tarski(sK4))
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4))))
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f13,f31,f30])).

fof(f30,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k1_tarski(X3) != k5_partfun1(sK3,k1_tarski(sK4),sK5)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4))))
          & v1_funct_2(X3,sK3,k1_tarski(sK4))
          & v1_funct_1(X3) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4))))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X3] :
        ( k1_tarski(X3) != k5_partfun1(sK3,k1_tarski(sK4),sK5)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4))))
        & v1_funct_2(X3,sK3,k1_tarski(sK4))
        & v1_funct_1(X3) )
   => ( k5_partfun1(sK3,k1_tarski(sK4),sK5) != k1_tarski(sK6)
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4))))
      & v1_funct_2(sK6,sK3,k1_tarski(sK4))
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
              & v1_funct_2(X3,X0,k1_tarski(X1))
              & v1_funct_1(X3) )
           => k5_partfun1(X0,k1_tarski(X1),X2) = k1_tarski(X3) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
         => k5_partfun1(X0,k1_tarski(X1),X2) = k1_tarski(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_2)).

fof(f89,plain,
    ( sP2(sK5,sK3,k1_tarski(sK4))
    | ~ v1_funct_1(sK5) ),
    inference(resolution,[],[f77,f49])).

fof(f49,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4)))) ),
    inference(cnf_transformation,[],[f32])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( sP2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f21,f28,f27,f26])).

fof(f26,plain,(
    ! [X2,X0,X4,X1] :
      ( sP0(X2,X0,X4,X1)
    <=> ? [X5] :
          ( r1_partfun1(X2,X5)
          & v1_partfun1(X5,X0)
          & X4 = X5
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X5) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f27,plain,(
    ! [X1,X0,X2,X3] :
      ( sP1(X1,X0,X2,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> sP0(X2,X0,X4,X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> sP1(X1,X0,X2,X3) )
      | ~ sP2(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_partfun1)).

fof(f1209,plain,(
    ~ sP2(sK5,sK3,k1_tarski(sK4)) ),
    inference(subsumption_resolution,[],[f1208,f53])).

fof(f53,plain,(
    k5_partfun1(sK3,k1_tarski(sK4),sK5) != k1_tarski(sK6) ),
    inference(cnf_transformation,[],[f32])).

fof(f1208,plain,
    ( k5_partfun1(sK3,k1_tarski(sK4),sK5) = k1_tarski(sK6)
    | ~ sP2(sK5,sK3,k1_tarski(sK4)) ),
    inference(resolution,[],[f1202,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP1(X2,X1,X0,X3)
      | k5_partfun1(X1,X2,X0) = X3
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X1,X2,X0) = X3
            | ~ sP1(X2,X1,X0,X3) )
          & ( sP1(X2,X1,X0,X3)
            | k5_partfun1(X1,X2,X0) != X3 ) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ! [X3] :
          ( ( k5_partfun1(X0,X1,X2) = X3
            | ~ sP1(X1,X0,X2,X3) )
          & ( sP1(X1,X0,X2,X3)
            | k5_partfun1(X0,X1,X2) != X3 ) )
      | ~ sP2(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f1202,plain,(
    sP1(k1_tarski(sK4),sK3,sK5,k1_tarski(sK6)) ),
    inference(subsumption_resolution,[],[f1201,f169])).

fof(f169,plain,(
    sP0(sK5,sK3,sK6,k1_tarski(sK4)) ),
    inference(subsumption_resolution,[],[f168,f102])).

fof(f102,plain,(
    v1_partfun1(sK6,sK3) ),
    inference(subsumption_resolution,[],[f101,f54])).

fof(f54,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f101,plain,
    ( v1_partfun1(sK6,sK3)
    | v1_xboole_0(k1_tarski(sK4)) ),
    inference(subsumption_resolution,[],[f100,f52])).

fof(f52,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4)))) ),
    inference(cnf_transformation,[],[f32])).

fof(f100,plain,
    ( v1_partfun1(sK6,sK3)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4))))
    | v1_xboole_0(k1_tarski(sK4)) ),
    inference(subsumption_resolution,[],[f99,f50])).

fof(f50,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f32])).

fof(f99,plain,
    ( v1_partfun1(sK6,sK3)
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4))))
    | v1_xboole_0(k1_tarski(sK4)) ),
    inference(resolution,[],[f56,f51])).

fof(f51,plain,(
    v1_funct_2(sK6,sK3,k1_tarski(sK4)) ),
    inference(cnf_transformation,[],[f32])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f168,plain,
    ( ~ v1_partfun1(sK6,sK3)
    | sP0(sK5,sK3,sK6,k1_tarski(sK4)) ),
    inference(resolution,[],[f167,f52])).

fof(f167,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(sK6,X0)
      | sP0(sK5,X0,sK6,X1) ) ),
    inference(subsumption_resolution,[],[f166,f50])).

fof(f166,plain,(
    ! [X0,X1] :
      ( sP0(sK5,X0,sK6,X1)
      | ~ v1_partfun1(sK6,X0)
      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(sK6) ) ),
    inference(resolution,[],[f159,f85])).

fof(f85,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r1_partfun1(X0,X4)
      | sP0(X0,X1,X4,X3)
      | ~ v1_partfun1(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | ~ r1_partfun1(X0,X4)
      | ~ v1_partfun1(X4,X1)
      | X2 != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ! [X4] :
            ( ~ r1_partfun1(X0,X4)
            | ~ v1_partfun1(X4,X1)
            | X2 != X4
            | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
            | ~ v1_funct_1(X4) ) )
      & ( ( r1_partfun1(X0,sK9(X0,X1,X2,X3))
          & v1_partfun1(sK9(X0,X1,X2,X3),X1)
          & sK9(X0,X1,X2,X3) = X2
          & m1_subset_1(sK9(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
          & v1_funct_1(sK9(X0,X1,X2,X3)) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f44,f45])).

fof(f45,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r1_partfun1(X0,X5)
          & v1_partfun1(X5,X1)
          & X2 = X5
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
          & v1_funct_1(X5) )
     => ( r1_partfun1(X0,sK9(X0,X1,X2,X3))
        & v1_partfun1(sK9(X0,X1,X2,X3),X1)
        & sK9(X0,X1,X2,X3) = X2
        & m1_subset_1(sK9(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
        & v1_funct_1(sK9(X0,X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ! [X4] :
            ( ~ r1_partfun1(X0,X4)
            | ~ v1_partfun1(X4,X1)
            | X2 != X4
            | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
            | ~ v1_funct_1(X4) ) )
      & ( ? [X5] :
            ( r1_partfun1(X0,X5)
            & v1_partfun1(X5,X1)
            & X2 = X5
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
            & v1_funct_1(X5) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X4,X1] :
      ( ( sP0(X2,X0,X4,X1)
        | ! [X5] :
            ( ~ r1_partfun1(X2,X5)
            | ~ v1_partfun1(X5,X0)
            | X4 != X5
            | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            | ~ v1_funct_1(X5) ) )
      & ( ? [X5] :
            ( r1_partfun1(X2,X5)
            & v1_partfun1(X5,X0)
            & X4 = X5
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X5) )
        | ~ sP0(X2,X0,X4,X1) ) ) ),
    inference(nnf_transformation,[],[f26])).

% (30289)Refutation not found, incomplete strategy% (30289)------------------------------
% (30289)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (30289)Termination reason: Refutation not found, incomplete strategy

% (30289)Memory used [KB]: 6140
% (30289)Time elapsed: 0.177 s
% (30289)------------------------------
% (30289)------------------------------
fof(f159,plain,(
    r1_partfun1(sK5,sK6) ),
    inference(subsumption_resolution,[],[f157,f50])).

fof(f157,plain,
    ( ~ v1_funct_1(sK6)
    | r1_partfun1(sK5,sK6) ),
    inference(resolution,[],[f154,f52])).

fof(f154,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4))))
      | ~ v1_funct_1(X0)
      | r1_partfun1(sK5,X0) ) ),
    inference(resolution,[],[f151,f49])).

fof(f151,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2))))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2))))
      | r1_partfun1(sK5,X0) ) ),
    inference(resolution,[],[f78,f48])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | r1_partfun1(X2,X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_1(X3) )
         => r1_partfun1(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_partfun1)).

fof(f1201,plain,
    ( ~ sP0(sK5,sK3,sK6,k1_tarski(sK4))
    | sP1(k1_tarski(sK4),sK3,sK5,k1_tarski(sK6)) ),
    inference(subsumption_resolution,[],[f1198,f82])).

fof(f82,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK7(X0,X1) != X0
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( sK7(X0,X1) = X0
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f34,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK7(X0,X1) != X0
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( sK7(X0,X1) = X0
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f1198,plain,
    ( ~ r2_hidden(sK6,k1_tarski(sK6))
    | ~ sP0(sK5,sK3,sK6,k1_tarski(sK4))
    | sP1(k1_tarski(sK4),sK3,sK5,k1_tarski(sK6)) ),
    inference(superposition,[],[f70,f1165])).

fof(f1165,plain,(
    sK6 = sK8(k1_tarski(sK4),sK3,sK5,k1_tarski(sK6)) ),
    inference(subsumption_resolution,[],[f1164,f53])).

fof(f1164,plain,
    ( sK6 = sK8(k1_tarski(sK4),sK3,sK5,k1_tarski(sK6))
    | k5_partfun1(sK3,k1_tarski(sK4),sK5) = k1_tarski(sK6) ),
    inference(equality_resolution,[],[f1156])).

fof(f1156,plain,(
    ! [X0] :
      ( sK6 != X0
      | sK8(k1_tarski(sK4),sK3,sK5,k1_tarski(X0)) = X0
      | k1_tarski(X0) = k5_partfun1(sK3,k1_tarski(sK4),sK5) ) ),
    inference(equality_factoring,[],[f349])).

fof(f349,plain,(
    ! [X6] :
      ( sK6 = sK8(k1_tarski(sK4),sK3,sK5,k1_tarski(X6))
      | sK8(k1_tarski(sK4),sK3,sK5,k1_tarski(X6)) = X6
      | k5_partfun1(sK3,k1_tarski(sK4),sK5) = k1_tarski(X6) ) ),
    inference(subsumption_resolution,[],[f347,f91])).

fof(f347,plain,(
    ! [X6] :
      ( sK6 = sK8(k1_tarski(sK4),sK3,sK5,k1_tarski(X6))
      | sK8(k1_tarski(sK4),sK3,sK5,k1_tarski(X6)) = X6
      | k5_partfun1(sK3,k1_tarski(sK4),sK5) = k1_tarski(X6)
      | ~ sP2(sK5,sK3,k1_tarski(sK4)) ) ),
    inference(resolution,[],[f332,f66])).

fof(f332,plain,(
    ! [X5] :
      ( sP1(k1_tarski(sK4),sK3,sK5,k1_tarski(X5))
      | sK6 = sK8(k1_tarski(sK4),sK3,sK5,k1_tarski(X5))
      | sK8(k1_tarski(sK4),sK3,sK5,k1_tarski(X5)) = X5 ) ),
    inference(resolution,[],[f327,f83])).

fof(f83,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f327,plain,(
    ! [X0] :
      ( r2_hidden(sK8(k1_tarski(sK4),sK3,sK5,X0),X0)
      | sP1(k1_tarski(sK4),sK3,sK5,X0)
      | sK6 = sK8(k1_tarski(sK4),sK3,sK5,X0) ) ),
    inference(subsumption_resolution,[],[f326,f261])).

fof(f261,plain,(
    ! [X0] :
      ( r2_hidden(sK8(k1_tarski(sK4),sK3,sK5,X0),X0)
      | m1_subset_1(sK8(k1_tarski(sK4),sK3,sK5,X0),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4))))
      | sP1(k1_tarski(sK4),sK3,sK5,X0) ) ),
    inference(subsumption_resolution,[],[f260,f48])).

fof(f260,plain,(
    ! [X0] :
      ( r2_hidden(sK8(k1_tarski(sK4),sK3,sK5,X0),X0)
      | sP1(k1_tarski(sK4),sK3,sK5,X0)
      | m1_subset_1(sK8(k1_tarski(sK4),sK3,sK5,X0),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4))))
      | ~ v1_funct_1(sK5) ) ),
    inference(subsumption_resolution,[],[f243,f49])).

fof(f243,plain,(
    ! [X0] :
      ( r2_hidden(sK8(k1_tarski(sK4),sK3,sK5,X0),X0)
      | sP1(k1_tarski(sK4),sK3,sK5,X0)
      | m1_subset_1(sK8(k1_tarski(sK4),sK3,sK5,X0),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4))))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4))))
      | ~ v1_funct_1(sK5) ) ),
    inference(resolution,[],[f240,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
         => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_2)).

fof(f240,plain,(
    ! [X0] :
      ( r2_hidden(sK8(k1_tarski(sK4),sK3,sK5,X0),k5_partfun1(sK3,k1_tarski(sK4),sK5))
      | r2_hidden(sK8(k1_tarski(sK4),sK3,sK5,X0),X0)
      | sP1(k1_tarski(sK4),sK3,sK5,X0) ) ),
    inference(resolution,[],[f222,f91])).

fof(f222,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP2(X2,X1,X0)
      | r2_hidden(sK8(X0,X1,X2,X3),k5_partfun1(X1,X0,X2))
      | r2_hidden(sK8(X0,X1,X2,X3),X3)
      | sP1(X0,X1,X2,X3) ) ),
    inference(resolution,[],[f140,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X1,X0,k5_partfun1(X1,X2,X0))
      | ~ sP2(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X2,X1,X0,X3)
      | k5_partfun1(X1,X2,X0) != X3
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f140,plain,(
    ! [X6,X4,X8,X7,X5] :
      ( ~ sP1(X4,X5,X6,X8)
      | sP1(X4,X5,X6,X7)
      | r2_hidden(sK8(X4,X5,X6,X7),X8)
      | r2_hidden(sK8(X4,X5,X6,X7),X7) ) ),
    inference(resolution,[],[f69,f68])).

fof(f68,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP0(X2,X1,X5,X0)
      | r2_hidden(X5,X3)
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ( ( ~ sP0(X2,X1,sK8(X0,X1,X2,X3),X0)
            | ~ r2_hidden(sK8(X0,X1,X2,X3),X3) )
          & ( sP0(X2,X1,sK8(X0,X1,X2,X3),X0)
            | r2_hidden(sK8(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP0(X2,X1,X5,X0) )
            & ( sP0(X2,X1,X5,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f40,f41])).

fof(f41,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ sP0(X2,X1,X4,X0)
            | ~ r2_hidden(X4,X3) )
          & ( sP0(X2,X1,X4,X0)
            | r2_hidden(X4,X3) ) )
     => ( ( ~ sP0(X2,X1,sK8(X0,X1,X2,X3),X0)
          | ~ r2_hidden(sK8(X0,X1,X2,X3),X3) )
        & ( sP0(X2,X1,sK8(X0,X1,X2,X3),X0)
          | r2_hidden(sK8(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ sP0(X2,X1,X4,X0)
              | ~ r2_hidden(X4,X3) )
            & ( sP0(X2,X1,X4,X0)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP0(X2,X1,X5,X0) )
            & ( sP0(X2,X1,X5,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X1,X0,X2,X3] :
      ( ( sP1(X1,X0,X2,X3)
        | ? [X4] :
            ( ( ~ sP0(X2,X0,X4,X1)
              | ~ r2_hidden(X4,X3) )
            & ( sP0(X2,X0,X4,X1)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ~ sP0(X2,X0,X4,X1) )
            & ( sP0(X2,X0,X4,X1)
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP1(X1,X0,X2,X3) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,sK8(X0,X1,X2,X3),X0)
      | r2_hidden(sK8(X0,X1,X2,X3),X3)
      | sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f326,plain,(
    ! [X0] :
      ( r2_hidden(sK8(k1_tarski(sK4),sK3,sK5,X0),X0)
      | sP1(k1_tarski(sK4),sK3,sK5,X0)
      | sK6 = sK8(k1_tarski(sK4),sK3,sK5,X0)
      | ~ m1_subset_1(sK8(k1_tarski(sK4),sK3,sK5,X0),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4)))) ) ),
    inference(subsumption_resolution,[],[f324,f52])).

fof(f324,plain,(
    ! [X0] :
      ( r2_hidden(sK8(k1_tarski(sK4),sK3,sK5,X0),X0)
      | sP1(k1_tarski(sK4),sK3,sK5,X0)
      | sK6 = sK8(k1_tarski(sK4),sK3,sK5,X0)
      | ~ m1_subset_1(sK8(k1_tarski(sK4),sK3,sK5,X0),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4))))
      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4)))) ) ),
    inference(resolution,[],[f291,f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f291,plain,(
    ! [X0] :
      ( r2_hidden(sK8(k1_tarski(sK4),sK3,sK5,X0),X0)
      | r2_relset_1(sK3,k1_tarski(sK4),sK6,sK8(k1_tarski(sK4),sK3,sK5,X0))
      | sP1(k1_tarski(sK4),sK3,sK5,X0) ) ),
    inference(subsumption_resolution,[],[f290,f261])).

fof(f290,plain,(
    ! [X0] :
      ( r2_hidden(sK8(k1_tarski(sK4),sK3,sK5,X0),X0)
      | sP1(k1_tarski(sK4),sK3,sK5,X0)
      | ~ m1_subset_1(sK8(k1_tarski(sK4),sK3,sK5,X0),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4))))
      | r2_relset_1(sK3,k1_tarski(sK4),sK6,sK8(k1_tarski(sK4),sK3,sK5,X0)) ) ),
    inference(subsumption_resolution,[],[f286,f265])).

fof(f265,plain,(
    ! [X2] :
      ( r2_hidden(sK8(k1_tarski(sK4),sK3,sK5,X2),X2)
      | sP1(k1_tarski(sK4),sK3,sK5,X2)
      | v1_funct_1(sK8(k1_tarski(sK4),sK3,sK5,X2)) ) ),
    inference(subsumption_resolution,[],[f264,f48])).

fof(f264,plain,(
    ! [X2] :
      ( r2_hidden(sK8(k1_tarski(sK4),sK3,sK5,X2),X2)
      | sP1(k1_tarski(sK4),sK3,sK5,X2)
      | v1_funct_1(sK8(k1_tarski(sK4),sK3,sK5,X2))
      | ~ v1_funct_1(sK5) ) ),
    inference(subsumption_resolution,[],[f245,f49])).

fof(f245,plain,(
    ! [X2] :
      ( r2_hidden(sK8(k1_tarski(sK4),sK3,sK5,X2),X2)
      | sP1(k1_tarski(sK4),sK3,sK5,X2)
      | v1_funct_1(sK8(k1_tarski(sK4),sK3,sK5,X2))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4))))
      | ~ v1_funct_1(sK5) ) ),
    inference(resolution,[],[f240,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f286,plain,(
    ! [X0] :
      ( r2_hidden(sK8(k1_tarski(sK4),sK3,sK5,X0),X0)
      | sP1(k1_tarski(sK4),sK3,sK5,X0)
      | ~ m1_subset_1(sK8(k1_tarski(sK4),sK3,sK5,X0),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4))))
      | ~ v1_funct_1(sK8(k1_tarski(sK4),sK3,sK5,X0))
      | r2_relset_1(sK3,k1_tarski(sK4),sK6,sK8(k1_tarski(sK4),sK3,sK5,X0)) ) ),
    inference(resolution,[],[f263,f165])).

fof(f165,plain,(
    ! [X0] :
      ( ~ v1_funct_2(X0,sK3,k1_tarski(sK4))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4))))
      | ~ v1_funct_1(X0)
      | r2_relset_1(sK3,k1_tarski(sK4),sK6,X0) ) ),
    inference(subsumption_resolution,[],[f164,f50])).

fof(f164,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4))))
      | ~ v1_funct_2(X0,sK3,k1_tarski(sK4))
      | ~ v1_funct_1(X0)
      | r2_relset_1(sK3,k1_tarski(sK4),sK6,X0)
      | ~ v1_funct_1(sK6) ) ),
    inference(subsumption_resolution,[],[f162,f52])).

fof(f162,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4))))
      | ~ v1_funct_2(X0,sK3,k1_tarski(sK4))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4))))
      | r2_relset_1(sK3,k1_tarski(sK4),sK6,X0)
      | ~ v1_funct_1(sK6) ) ),
    inference(resolution,[],[f61,f51])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,X0,k1_tarski(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_2(X3,X0,k1_tarski(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | r2_relset_1(X0,k1_tarski(X1),X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,k1_tarski(X1),X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_2(X3,X0,k1_tarski(X1))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_2(X2,X0,k1_tarski(X1))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,k1_tarski(X1),X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_2(X3,X0,k1_tarski(X1))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_2(X2,X0,k1_tarski(X1))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X2,X0,k1_tarski(X1))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
         => r2_relset_1(X0,k1_tarski(X1),X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_funct_2)).

fof(f263,plain,(
    ! [X1] :
      ( r2_hidden(sK8(k1_tarski(sK4),sK3,sK5,X1),X1)
      | v1_funct_2(sK8(k1_tarski(sK4),sK3,sK5,X1),sK3,k1_tarski(sK4))
      | sP1(k1_tarski(sK4),sK3,sK5,X1) ) ),
    inference(subsumption_resolution,[],[f262,f48])).

fof(f262,plain,(
    ! [X1] :
      ( r2_hidden(sK8(k1_tarski(sK4),sK3,sK5,X1),X1)
      | sP1(k1_tarski(sK4),sK3,sK5,X1)
      | v1_funct_2(sK8(k1_tarski(sK4),sK3,sK5,X1),sK3,k1_tarski(sK4))
      | ~ v1_funct_1(sK5) ) ),
    inference(subsumption_resolution,[],[f244,f49])).

fof(f244,plain,(
    ! [X1] :
      ( r2_hidden(sK8(k1_tarski(sK4),sK3,sK5,X1),X1)
      | sP1(k1_tarski(sK4),sK3,sK5,X1)
      | v1_funct_2(sK8(k1_tarski(sK4),sK3,sK5,X1),sK3,k1_tarski(sK4))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4))))
      | ~ v1_funct_1(sK5) ) ),
    inference(resolution,[],[f240,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK8(X0,X1,X2,X3),X3)
      | ~ sP0(X2,X1,sK8(X0,X1,X2,X3),X0)
      | sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f42])).

%------------------------------------------------------------------------------
