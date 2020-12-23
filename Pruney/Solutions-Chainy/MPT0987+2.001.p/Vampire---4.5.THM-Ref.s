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
% DateTime   : Thu Dec  3 13:02:26 EST 2020

% Result     : Theorem 1.40s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 690 expanded)
%              Number of leaves         :   29 ( 275 expanded)
%              Depth                    :   19
%              Number of atoms          :  653 (5967 expanded)
%              Number of equality atoms :  104 ( 239 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1244,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f151,f177,f180,f184,f376,f535,f577,f606,f621,f660,f1046,f1057,f1240])).

fof(f1240,plain,
    ( ~ spl6_10
    | ~ spl6_24
    | ~ spl6_25
    | ~ spl6_41 ),
    inference(avatar_contradiction_clause,[],[f1239])).

fof(f1239,plain,
    ( $false
    | ~ spl6_10
    | ~ spl6_24
    | ~ spl6_25
    | ~ spl6_41 ),
    inference(subsumption_resolution,[],[f1238,f739])).

fof(f739,plain,
    ( v1_relat_1(k5_relat_1(sK3,k1_xboole_0))
    | ~ spl6_24
    | ~ spl6_41 ),
    inference(backward_demodulation,[],[f370,f659])).

fof(f659,plain,
    ( k1_xboole_0 = sK4
    | ~ spl6_41 ),
    inference(avatar_component_clause,[],[f657])).

fof(f657,plain,
    ( spl6_41
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f370,plain,
    ( v1_relat_1(k5_relat_1(sK3,sK4))
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f369])).

fof(f369,plain,
    ( spl6_24
  <=> v1_relat_1(k5_relat_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f1238,plain,
    ( ~ v1_relat_1(k5_relat_1(sK3,k1_xboole_0))
    | ~ spl6_10
    | ~ spl6_24
    | ~ spl6_25
    | ~ spl6_41 ),
    inference(subsumption_resolution,[],[f1237,f1075])).

fof(f1075,plain,
    ( ~ v2_funct_2(k5_relat_1(sK3,k1_xboole_0),k1_xboole_0)
    | ~ spl6_10
    | ~ spl6_41 ),
    inference(backward_demodulation,[],[f636,f659])).

fof(f636,plain,
    ( ~ v2_funct_2(k5_relat_1(sK3,sK4),k1_xboole_0)
    | ~ spl6_10 ),
    inference(backward_demodulation,[],[f329,f171])).

fof(f171,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl6_10
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f329,plain,(
    ~ v2_funct_2(k5_relat_1(sK3,sK4),sK2) ),
    inference(backward_demodulation,[],[f63,f290])).

fof(f290,plain,(
    k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(subsumption_resolution,[],[f287,f55])).

fof(f55,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ~ v2_funct_2(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4),sK2)
    & v2_funct_2(sK4,sK2)
    & v2_funct_2(sK3,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3)
    & ~ v1_xboole_0(sK2)
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f22,f43,f42,f41,f40])).

fof(f40,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ~ v2_funct_2(k1_partfun1(X0,X1,X1,X2,X3,X4),X2)
                    & v2_funct_2(X4,X2)
                    & v2_funct_2(X3,X1)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                    & v1_funct_2(X4,X1,X2)
                    & v1_funct_1(X4) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X3,X0,X1)
                & v1_funct_1(X3) )
            & ~ v1_xboole_0(X2) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ v2_funct_2(k1_partfun1(sK0,sK1,sK1,X2,X3,X4),X2)
                  & v2_funct_2(X4,X2)
                  & v2_funct_2(X3,sK1)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
                  & v1_funct_2(X4,sK1,X2)
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
              & v1_funct_2(X3,sK0,sK1)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ~ v2_funct_2(k1_partfun1(sK0,sK1,sK1,X2,X3,X4),X2)
                & v2_funct_2(X4,X2)
                & v2_funct_2(X3,sK1)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
                & v1_funct_2(X4,sK1,X2)
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
            & v1_funct_2(X3,sK0,sK1)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ~ v2_funct_2(k1_partfun1(sK0,sK1,sK1,sK2,X3,X4),sK2)
              & v2_funct_2(X4,sK2)
              & v2_funct_2(X3,sK1)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
              & v1_funct_2(X4,sK1,sK2)
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_2(X3,sK0,sK1)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ~ v2_funct_2(k1_partfun1(sK0,sK1,sK1,sK2,X3,X4),sK2)
            & v2_funct_2(X4,sK2)
            & v2_funct_2(X3,sK1)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
            & v1_funct_2(X4,sK1,sK2)
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        & v1_funct_2(X3,sK0,sK1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ~ v2_funct_2(k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4),sK2)
          & v2_funct_2(X4,sK2)
          & v2_funct_2(sK3,sK1)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X4,sK1,sK2)
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X4] :
        ( ~ v2_funct_2(k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4),sK2)
        & v2_funct_2(X4,sK2)
        & v2_funct_2(sK3,sK1)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        & v1_funct_2(X4,sK1,sK2)
        & v1_funct_1(X4) )
   => ( ~ v2_funct_2(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4),sK2)
      & v2_funct_2(sK4,sK2)
      & v2_funct_2(sK3,sK1)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK4,sK1,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ v2_funct_2(k1_partfun1(X0,X1,X1,X2,X3,X4),X2)
                  & v2_funct_2(X4,X2)
                  & v2_funct_2(X3,X1)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & v1_funct_2(X4,X1,X2)
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ v2_funct_2(k1_partfun1(X0,X1,X1,X2,X3,X4),X2)
                  & v2_funct_2(X4,X2)
                  & v2_funct_2(X3,X1)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & v1_funct_2(X4,X1,X2)
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X3,X0,X1)
                  & v1_funct_1(X3) )
               => ! [X4] :
                    ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                      & v1_funct_2(X4,X1,X2)
                      & v1_funct_1(X4) )
                   => ( ( v2_funct_2(X4,X2)
                        & v2_funct_2(X3,X1) )
                     => v2_funct_2(k1_partfun1(X0,X1,X1,X2,X3,X4),X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X3,X0,X1)
                & v1_funct_1(X3) )
             => ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                    & v1_funct_2(X4,X1,X2)
                    & v1_funct_1(X4) )
                 => ( ( v2_funct_2(X4,X2)
                      & v2_funct_2(X3,X1) )
                   => v2_funct_2(k1_partfun1(X0,X1,X1,X2,X3,X4),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_funct_2)).

fof(f287,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f162,f57])).

fof(f57,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f162,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | k1_partfun1(X3,X4,sK1,sK2,X5,sK4) = k5_relat_1(X5,sK4)
      | ~ v1_funct_1(X5) ) ),
    inference(subsumption_resolution,[],[f154,f58])).

fof(f58,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f154,plain,(
    ! [X4,X5,X3] :
      ( k1_partfun1(X3,X4,sK1,sK2,X5,sK4) = k5_relat_1(X5,sK4)
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X5) ) ),
    inference(resolution,[],[f60,f88])).

fof(f88,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f60,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f44])).

fof(f63,plain,(
    ~ v2_funct_2(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4),sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f1237,plain,
    ( v2_funct_2(k5_relat_1(sK3,k1_xboole_0),k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(sK3,k1_xboole_0))
    | ~ spl6_10
    | ~ spl6_24
    | ~ spl6_25
    | ~ spl6_41 ),
    inference(subsumption_resolution,[],[f1234,f1077])).

fof(f1077,plain,
    ( v5_relat_1(k5_relat_1(sK3,k1_xboole_0),k1_xboole_0)
    | ~ spl6_10
    | ~ spl6_25
    | ~ spl6_41 ),
    inference(backward_demodulation,[],[f1033,f659])).

fof(f1033,plain,
    ( v5_relat_1(k5_relat_1(sK3,sK4),k1_xboole_0)
    | ~ spl6_10
    | ~ spl6_25 ),
    inference(forward_demodulation,[],[f374,f171])).

fof(f374,plain,
    ( v5_relat_1(k5_relat_1(sK3,sK4),sK2)
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f373])).

fof(f373,plain,
    ( spl6_25
  <=> v5_relat_1(k5_relat_1(sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f1234,plain,
    ( ~ v5_relat_1(k5_relat_1(sK3,k1_xboole_0),k1_xboole_0)
    | v2_funct_2(k5_relat_1(sK3,k1_xboole_0),k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(sK3,k1_xboole_0))
    | ~ spl6_10
    | ~ spl6_24
    | ~ spl6_25
    | ~ spl6_41 ),
    inference(superposition,[],[f91,f1222])).

fof(f1222,plain,
    ( k1_xboole_0 = k2_relat_1(k5_relat_1(sK3,k1_xboole_0))
    | ~ spl6_10
    | ~ spl6_24
    | ~ spl6_25
    | ~ spl6_41 ),
    inference(subsumption_resolution,[],[f1221,f64])).

fof(f64,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f1221,plain,
    ( k1_xboole_0 = k2_relat_1(k5_relat_1(sK3,k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k2_relat_1(k5_relat_1(sK3,k1_xboole_0)))
    | ~ spl6_10
    | ~ spl6_24
    | ~ spl6_25
    | ~ spl6_41 ),
    inference(resolution,[],[f1173,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1173,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK3,k1_xboole_0)),k1_xboole_0)
    | ~ spl6_10
    | ~ spl6_24
    | ~ spl6_25
    | ~ spl6_41 ),
    inference(subsumption_resolution,[],[f1172,f739])).

fof(f1172,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK3,k1_xboole_0)),k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(sK3,k1_xboole_0))
    | ~ spl6_10
    | ~ spl6_25
    | ~ spl6_41 ),
    inference(resolution,[],[f1077,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f91,plain,(
    ! [X1] :
      ( ~ v5_relat_1(X1,k2_relat_1(X1))
      | v2_funct_2(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f1057,plain,
    ( ~ spl6_2
    | spl6_3
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f1056,f101,f109,f105])).

fof(f105,plain,
    ( spl6_2
  <=> v5_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f109,plain,
    ( spl6_3
  <=> sK1 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f101,plain,
    ( spl6_1
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f1056,plain,
    ( sK1 = k2_relat_1(sK3)
    | ~ v5_relat_1(sK3,sK1)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f1055,f102])).

fof(f102,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f101])).

fof(f1055,plain,
    ( sK1 = k2_relat_1(sK3)
    | ~ v5_relat_1(sK3,sK1)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f61,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_2(X1,X0)
      | k2_relat_1(X1) = X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f61,plain,(
    v2_funct_2(sK3,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f1046,plain,
    ( ~ spl6_8
    | spl6_9
    | ~ spl6_10 ),
    inference(avatar_contradiction_clause,[],[f1045])).

fof(f1045,plain,
    ( $false
    | ~ spl6_8
    | spl6_9
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f1026,f973])).

fof(f973,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK4)
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f963,f866])).

fof(f866,plain,
    ( v1_funct_2(sK4,k1_xboole_0,k1_xboole_0)
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(backward_demodulation,[],[f627,f145])).

fof(f145,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl6_8
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f627,plain,
    ( v1_funct_2(sK4,sK1,k1_xboole_0)
    | ~ spl6_10 ),
    inference(backward_demodulation,[],[f59,f171])).

fof(f59,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f963,plain,
    ( ~ v1_funct_2(sK4,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK4)
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(resolution,[],[f943,f98])).

fof(f98,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f943,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f628,f145])).

fof(f628,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | ~ spl6_10 ),
    inference(backward_demodulation,[],[f60,f171])).

fof(f1026,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK4)
    | ~ spl6_8
    | spl6_9
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f1025,f145])).

fof(f1025,plain,
    ( sK1 != k1_relset_1(sK1,k1_xboole_0,sK4)
    | spl6_9
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f166,f171])).

fof(f166,plain,
    ( sK1 != k1_relset_1(sK1,sK2,sK4)
    | spl6_9 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl6_9
  <=> sK1 = k1_relset_1(sK1,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f660,plain,
    ( spl6_41
    | spl6_8
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f655,f169,f143,f657])).

fof(f655,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK4
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f644,f627])).

fof(f644,plain,
    ( ~ v1_funct_2(sK4,sK1,k1_xboole_0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK4
    | ~ spl6_10 ),
    inference(resolution,[],[f628,f96])).

fof(f96,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2 ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f621,plain,(
    spl6_25 ),
    inference(avatar_contradiction_clause,[],[f620])).

fof(f620,plain,
    ( $false
    | spl6_25 ),
    inference(subsumption_resolution,[],[f506,f375])).

fof(f375,plain,
    ( ~ v5_relat_1(k5_relat_1(sK3,sK4),sK2)
    | spl6_25 ),
    inference(avatar_component_clause,[],[f373])).

fof(f506,plain,(
    v5_relat_1(k5_relat_1(sK3,sK4),sK2) ),
    inference(resolution,[],[f334,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f334,plain,(
    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f333,f55])).

fof(f333,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f332,f57])).

fof(f332,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f331,f58])).

fof(f331,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f330,f60])).

fof(f330,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3) ),
    inference(superposition,[],[f90,f290])).

fof(f90,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f606,plain,
    ( spl6_9
    | spl6_10 ),
    inference(avatar_split_clause,[],[f605,f169,f165])).

fof(f605,plain,
    ( k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK4) ),
    inference(subsumption_resolution,[],[f597,f59])).

fof(f597,plain,
    ( ~ v1_funct_2(sK4,sK1,sK2)
    | k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK4) ),
    inference(resolution,[],[f60,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f577,plain,
    ( ~ spl6_5
    | spl6_6
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f576,f115,f123,f119])).

fof(f119,plain,
    ( spl6_5
  <=> v5_relat_1(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f123,plain,
    ( spl6_6
  <=> sK2 = k2_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f115,plain,
    ( spl6_4
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f576,plain,
    ( sK2 = k2_relat_1(sK4)
    | ~ v5_relat_1(sK4,sK2)
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f575,f116])).

fof(f116,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f115])).

fof(f575,plain,
    ( sK2 = k2_relat_1(sK4)
    | ~ v5_relat_1(sK4,sK2)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f62,f71])).

fof(f62,plain,(
    v2_funct_2(sK4,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f535,plain,(
    spl6_24 ),
    inference(avatar_contradiction_clause,[],[f534])).

fof(f534,plain,
    ( $false
    | spl6_24 ),
    inference(subsumption_resolution,[],[f533,f68])).

fof(f68,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f533,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK2))
    | spl6_24 ),
    inference(subsumption_resolution,[],[f515,f371])).

fof(f371,plain,
    ( ~ v1_relat_1(k5_relat_1(sK3,sK4))
    | spl6_24 ),
    inference(avatar_component_clause,[],[f369])).

fof(f515,plain,
    ( v1_relat_1(k5_relat_1(sK3,sK4))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK2)) ),
    inference(resolution,[],[f334,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f376,plain,
    ( ~ spl6_24
    | ~ spl6_25
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f367,f165,f123,f115,f109,f101,f373,f369])).

fof(f367,plain,
    ( ~ v5_relat_1(k5_relat_1(sK3,sK4),sK2)
    | ~ v1_relat_1(k5_relat_1(sK3,sK4))
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f364,f329])).

fof(f364,plain,
    ( ~ v5_relat_1(k5_relat_1(sK3,sK4),sK2)
    | v2_funct_2(k5_relat_1(sK3,sK4),sK2)
    | ~ v1_relat_1(k5_relat_1(sK3,sK4))
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_9 ),
    inference(superposition,[],[f91,f351])).

fof(f351,plain,
    ( sK2 = k2_relat_1(k5_relat_1(sK3,sK4))
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f350,f102])).

fof(f350,plain,
    ( sK2 = k2_relat_1(k5_relat_1(sK3,sK4))
    | ~ v1_relat_1(sK3)
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f348,f93])).

fof(f93,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f348,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK2 = k2_relat_1(k5_relat_1(sK3,sK4))
    | ~ v1_relat_1(sK3)
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_9 ),
    inference(superposition,[],[f236,f111])).

fof(f111,plain,
    ( sK1 = k2_relat_1(sK3)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f109])).

fof(f236,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,k2_relat_1(X0))
        | sK2 = k2_relat_1(k5_relat_1(X0,sK4))
        | ~ v1_relat_1(X0) )
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f235,f125])).

fof(f125,plain,
    ( sK2 = k2_relat_1(sK4)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f123])).

fof(f235,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,k2_relat_1(X0))
        | k2_relat_1(sK4) = k2_relat_1(k5_relat_1(X0,sK4))
        | ~ v1_relat_1(X0) )
    | ~ spl6_4
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f234,f116])).

fof(f234,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,k2_relat_1(X0))
        | k2_relat_1(sK4) = k2_relat_1(k5_relat_1(X0,sK4))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(sK4) )
    | ~ spl6_9 ),
    inference(superposition,[],[f65,f233])).

fof(f233,plain,
    ( sK1 = k1_relat_1(sK4)
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f157,f167])).

fof(f167,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK4)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f165])).

fof(f157,plain,(
    k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(resolution,[],[f60,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0)
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0)
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

fof(f184,plain,(
    spl6_5 ),
    inference(avatar_contradiction_clause,[],[f183])).

fof(f183,plain,
    ( $false
    | spl6_5 ),
    inference(subsumption_resolution,[],[f156,f121])).

fof(f121,plain,
    ( ~ v5_relat_1(sK4,sK2)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f119])).

fof(f156,plain,(
    v5_relat_1(sK4,sK2) ),
    inference(resolution,[],[f60,f81])).

fof(f180,plain,(
    spl6_2 ),
    inference(avatar_contradiction_clause,[],[f179])).

fof(f179,plain,
    ( $false
    | spl6_2 ),
    inference(subsumption_resolution,[],[f130,f107])).

fof(f107,plain,
    ( ~ v5_relat_1(sK3,sK1)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f105])).

fof(f130,plain,(
    v5_relat_1(sK3,sK1) ),
    inference(resolution,[],[f57,f81])).

fof(f177,plain,(
    spl6_4 ),
    inference(avatar_contradiction_clause,[],[f176])).

fof(f176,plain,
    ( $false
    | spl6_4 ),
    inference(subsumption_resolution,[],[f175,f68])).

fof(f175,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | spl6_4 ),
    inference(subsumption_resolution,[],[f160,f117])).

fof(f117,plain,
    ( ~ v1_relat_1(sK4)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f115])).

fof(f160,plain,
    ( v1_relat_1(sK4)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution,[],[f60,f66])).

fof(f151,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f150])).

fof(f150,plain,
    ( $false
    | spl6_1 ),
    inference(subsumption_resolution,[],[f149,f68])).

fof(f149,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl6_1 ),
    inference(subsumption_resolution,[],[f134,f103])).

fof(f103,plain,
    ( ~ v1_relat_1(sK3)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f101])).

fof(f134,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f57,f66])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:29:25 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.44  % (14193)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.48  % (14200)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.49  % (14185)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (14191)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.50  % (14188)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (14184)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (14186)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (14204)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (14202)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.51  % (14206)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (14203)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.51  % (14198)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (14201)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.51  % (14194)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.51  % (14190)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.52  % (14192)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.52  % (14208)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.52  % (14189)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.52  % (14209)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.52  % (14196)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.53  % (14199)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.53  % (14197)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (14205)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.53  % (14207)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.40/0.54  % (14187)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.40/0.54  % (14195)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.40/0.54  % (14185)Refutation found. Thanks to Tanya!
% 1.40/0.54  % SZS status Theorem for theBenchmark
% 1.40/0.54  % SZS output start Proof for theBenchmark
% 1.40/0.54  fof(f1244,plain,(
% 1.40/0.54    $false),
% 1.40/0.54    inference(avatar_sat_refutation,[],[f151,f177,f180,f184,f376,f535,f577,f606,f621,f660,f1046,f1057,f1240])).
% 1.40/0.54  fof(f1240,plain,(
% 1.40/0.54    ~spl6_10 | ~spl6_24 | ~spl6_25 | ~spl6_41),
% 1.40/0.54    inference(avatar_contradiction_clause,[],[f1239])).
% 1.40/0.54  fof(f1239,plain,(
% 1.40/0.54    $false | (~spl6_10 | ~spl6_24 | ~spl6_25 | ~spl6_41)),
% 1.40/0.54    inference(subsumption_resolution,[],[f1238,f739])).
% 1.40/0.54  fof(f739,plain,(
% 1.40/0.54    v1_relat_1(k5_relat_1(sK3,k1_xboole_0)) | (~spl6_24 | ~spl6_41)),
% 1.40/0.54    inference(backward_demodulation,[],[f370,f659])).
% 1.40/0.54  fof(f659,plain,(
% 1.40/0.54    k1_xboole_0 = sK4 | ~spl6_41),
% 1.40/0.54    inference(avatar_component_clause,[],[f657])).
% 1.40/0.54  fof(f657,plain,(
% 1.40/0.54    spl6_41 <=> k1_xboole_0 = sK4),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 1.40/0.54  fof(f370,plain,(
% 1.40/0.54    v1_relat_1(k5_relat_1(sK3,sK4)) | ~spl6_24),
% 1.40/0.54    inference(avatar_component_clause,[],[f369])).
% 1.40/0.55  fof(f369,plain,(
% 1.40/0.55    spl6_24 <=> v1_relat_1(k5_relat_1(sK3,sK4))),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 1.40/0.55  fof(f1238,plain,(
% 1.40/0.55    ~v1_relat_1(k5_relat_1(sK3,k1_xboole_0)) | (~spl6_10 | ~spl6_24 | ~spl6_25 | ~spl6_41)),
% 1.40/0.55    inference(subsumption_resolution,[],[f1237,f1075])).
% 1.40/0.55  fof(f1075,plain,(
% 1.40/0.55    ~v2_funct_2(k5_relat_1(sK3,k1_xboole_0),k1_xboole_0) | (~spl6_10 | ~spl6_41)),
% 1.40/0.55    inference(backward_demodulation,[],[f636,f659])).
% 1.40/0.55  fof(f636,plain,(
% 1.40/0.55    ~v2_funct_2(k5_relat_1(sK3,sK4),k1_xboole_0) | ~spl6_10),
% 1.40/0.55    inference(backward_demodulation,[],[f329,f171])).
% 1.40/0.55  fof(f171,plain,(
% 1.40/0.55    k1_xboole_0 = sK2 | ~spl6_10),
% 1.40/0.55    inference(avatar_component_clause,[],[f169])).
% 1.40/0.55  fof(f169,plain,(
% 1.40/0.55    spl6_10 <=> k1_xboole_0 = sK2),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.40/0.55  fof(f329,plain,(
% 1.40/0.55    ~v2_funct_2(k5_relat_1(sK3,sK4),sK2)),
% 1.40/0.55    inference(backward_demodulation,[],[f63,f290])).
% 1.40/0.55  fof(f290,plain,(
% 1.40/0.55    k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)),
% 1.40/0.55    inference(subsumption_resolution,[],[f287,f55])).
% 1.40/0.55  fof(f55,plain,(
% 1.40/0.55    v1_funct_1(sK3)),
% 1.40/0.55    inference(cnf_transformation,[],[f44])).
% 1.40/0.55  fof(f44,plain,(
% 1.40/0.55    (((~v2_funct_2(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4),sK2) & v2_funct_2(sK4,sK2) & v2_funct_2(sK3,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)),
% 1.40/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f22,f43,f42,f41,f40])).
% 1.40/0.55  fof(f40,plain,(
% 1.40/0.55    ? [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (~v2_funct_2(k1_partfun1(X0,X1,X1,X2,X3,X4),X2) & v2_funct_2(X4,X2) & v2_funct_2(X3,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (~v2_funct_2(k1_partfun1(sK0,sK1,sK1,X2,X3,X4),X2) & v2_funct_2(X4,X2) & v2_funct_2(X3,sK1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) & v1_funct_2(X4,sK1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))),
% 1.40/0.55    introduced(choice_axiom,[])).
% 1.40/0.55  fof(f41,plain,(
% 1.40/0.55    ? [X2] : (? [X3] : (? [X4] : (~v2_funct_2(k1_partfun1(sK0,sK1,sK1,X2,X3,X4),X2) & v2_funct_2(X4,X2) & v2_funct_2(X3,sK1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) & v1_funct_2(X4,sK1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (~v2_funct_2(k1_partfun1(sK0,sK1,sK1,sK2,X3,X4),sK2) & v2_funct_2(X4,sK2) & v2_funct_2(X3,sK1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X4,sK1,sK2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) & ~v1_xboole_0(sK2))),
% 1.40/0.55    introduced(choice_axiom,[])).
% 1.40/0.55  fof(f42,plain,(
% 1.40/0.55    ? [X3] : (? [X4] : (~v2_funct_2(k1_partfun1(sK0,sK1,sK1,sK2,X3,X4),sK2) & v2_funct_2(X4,sK2) & v2_funct_2(X3,sK1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X4,sK1,sK2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) => (? [X4] : (~v2_funct_2(k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4),sK2) & v2_funct_2(X4,sK2) & v2_funct_2(sK3,sK1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X4,sK1,sK2) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.40/0.55    introduced(choice_axiom,[])).
% 1.40/0.55  fof(f43,plain,(
% 1.40/0.55    ? [X4] : (~v2_funct_2(k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4),sK2) & v2_funct_2(X4,sK2) & v2_funct_2(sK3,sK1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X4,sK1,sK2) & v1_funct_1(X4)) => (~v2_funct_2(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4),sK2) & v2_funct_2(sK4,sK2) & v2_funct_2(sK3,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 1.40/0.55    introduced(choice_axiom,[])).
% 1.40/0.55  fof(f22,plain,(
% 1.40/0.55    ? [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (~v2_funct_2(k1_partfun1(X0,X1,X1,X2,X3,X4),X2) & v2_funct_2(X4,X2) & v2_funct_2(X3,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 1.40/0.55    inference(flattening,[],[f21])).
% 1.40/0.55  fof(f21,plain,(
% 1.40/0.55    ? [X0,X1] : (? [X2] : (? [X3] : (? [X4] : ((~v2_funct_2(k1_partfun1(X0,X1,X1,X2,X3,X4),X2) & (v2_funct_2(X4,X2) & v2_funct_2(X3,X1))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 1.40/0.55    inference(ennf_transformation,[],[f18])).
% 1.40/0.55  fof(f18,negated_conjecture,(
% 1.40/0.55    ~! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_2(X4,X2) & v2_funct_2(X3,X1)) => v2_funct_2(k1_partfun1(X0,X1,X1,X2,X3,X4),X2))))))),
% 1.40/0.55    inference(negated_conjecture,[],[f17])).
% 1.40/0.55  fof(f17,conjecture,(
% 1.40/0.55    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_2(X4,X2) & v2_funct_2(X3,X1)) => v2_funct_2(k1_partfun1(X0,X1,X1,X2,X3,X4),X2))))))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_funct_2)).
% 1.40/0.55  fof(f287,plain,(
% 1.40/0.55    k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) | ~v1_funct_1(sK3)),
% 1.40/0.55    inference(resolution,[],[f162,f57])).
% 1.40/0.55  fof(f57,plain,(
% 1.40/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.40/0.55    inference(cnf_transformation,[],[f44])).
% 1.40/0.55  fof(f162,plain,(
% 1.40/0.55    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k1_partfun1(X3,X4,sK1,sK2,X5,sK4) = k5_relat_1(X5,sK4) | ~v1_funct_1(X5)) )),
% 1.40/0.55    inference(subsumption_resolution,[],[f154,f58])).
% 1.40/0.55  fof(f58,plain,(
% 1.40/0.55    v1_funct_1(sK4)),
% 1.40/0.55    inference(cnf_transformation,[],[f44])).
% 1.40/0.55  fof(f154,plain,(
% 1.40/0.55    ( ! [X4,X5,X3] : (k1_partfun1(X3,X4,sK1,sK2,X5,sK4) = k5_relat_1(X5,sK4) | ~v1_funct_1(sK4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X5)) )),
% 1.40/0.55    inference(resolution,[],[f60,f88])).
% 1.40/0.55  fof(f88,plain,(
% 1.40/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f37])).
% 1.40/0.55  fof(f37,plain,(
% 1.40/0.55    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.40/0.55    inference(flattening,[],[f36])).
% 1.40/0.55  fof(f36,plain,(
% 1.40/0.55    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.40/0.55    inference(ennf_transformation,[],[f16])).
% 1.40/0.55  fof(f16,axiom,(
% 1.40/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.40/0.55  fof(f60,plain,(
% 1.40/0.55    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.40/0.55    inference(cnf_transformation,[],[f44])).
% 1.40/0.55  fof(f63,plain,(
% 1.40/0.55    ~v2_funct_2(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4),sK2)),
% 1.40/0.55    inference(cnf_transformation,[],[f44])).
% 1.40/0.55  fof(f1237,plain,(
% 1.40/0.55    v2_funct_2(k5_relat_1(sK3,k1_xboole_0),k1_xboole_0) | ~v1_relat_1(k5_relat_1(sK3,k1_xboole_0)) | (~spl6_10 | ~spl6_24 | ~spl6_25 | ~spl6_41)),
% 1.40/0.55    inference(subsumption_resolution,[],[f1234,f1077])).
% 1.40/0.55  fof(f1077,plain,(
% 1.40/0.55    v5_relat_1(k5_relat_1(sK3,k1_xboole_0),k1_xboole_0) | (~spl6_10 | ~spl6_25 | ~spl6_41)),
% 1.40/0.55    inference(backward_demodulation,[],[f1033,f659])).
% 1.40/0.55  fof(f1033,plain,(
% 1.40/0.55    v5_relat_1(k5_relat_1(sK3,sK4),k1_xboole_0) | (~spl6_10 | ~spl6_25)),
% 1.40/0.55    inference(forward_demodulation,[],[f374,f171])).
% 1.40/0.55  fof(f374,plain,(
% 1.40/0.55    v5_relat_1(k5_relat_1(sK3,sK4),sK2) | ~spl6_25),
% 1.40/0.55    inference(avatar_component_clause,[],[f373])).
% 1.40/0.55  fof(f373,plain,(
% 1.40/0.55    spl6_25 <=> v5_relat_1(k5_relat_1(sK3,sK4),sK2)),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 1.40/0.55  fof(f1234,plain,(
% 1.40/0.55    ~v5_relat_1(k5_relat_1(sK3,k1_xboole_0),k1_xboole_0) | v2_funct_2(k5_relat_1(sK3,k1_xboole_0),k1_xboole_0) | ~v1_relat_1(k5_relat_1(sK3,k1_xboole_0)) | (~spl6_10 | ~spl6_24 | ~spl6_25 | ~spl6_41)),
% 1.40/0.55    inference(superposition,[],[f91,f1222])).
% 1.40/0.55  fof(f1222,plain,(
% 1.40/0.55    k1_xboole_0 = k2_relat_1(k5_relat_1(sK3,k1_xboole_0)) | (~spl6_10 | ~spl6_24 | ~spl6_25 | ~spl6_41)),
% 1.40/0.55    inference(subsumption_resolution,[],[f1221,f64])).
% 1.40/0.55  fof(f64,plain,(
% 1.40/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f3])).
% 1.40/0.55  fof(f3,axiom,(
% 1.40/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.40/0.55  fof(f1221,plain,(
% 1.40/0.55    k1_xboole_0 = k2_relat_1(k5_relat_1(sK3,k1_xboole_0)) | ~r1_tarski(k1_xboole_0,k2_relat_1(k5_relat_1(sK3,k1_xboole_0))) | (~spl6_10 | ~spl6_24 | ~spl6_25 | ~spl6_41)),
% 1.40/0.55    inference(resolution,[],[f1173,f75])).
% 1.40/0.55  fof(f75,plain,(
% 1.40/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f50])).
% 1.40/0.55  fof(f50,plain,(
% 1.40/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.40/0.55    inference(flattening,[],[f49])).
% 1.40/0.55  fof(f49,plain,(
% 1.40/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.40/0.55    inference(nnf_transformation,[],[f2])).
% 1.40/0.55  fof(f2,axiom,(
% 1.40/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.40/0.55  fof(f1173,plain,(
% 1.40/0.55    r1_tarski(k2_relat_1(k5_relat_1(sK3,k1_xboole_0)),k1_xboole_0) | (~spl6_10 | ~spl6_24 | ~spl6_25 | ~spl6_41)),
% 1.40/0.55    inference(subsumption_resolution,[],[f1172,f739])).
% 1.40/0.55  fof(f1172,plain,(
% 1.40/0.55    r1_tarski(k2_relat_1(k5_relat_1(sK3,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(k5_relat_1(sK3,k1_xboole_0)) | (~spl6_10 | ~spl6_25 | ~spl6_41)),
% 1.40/0.55    inference(resolution,[],[f1077,f69])).
% 1.40/0.55  fof(f69,plain,(
% 1.40/0.55    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f47])).
% 1.40/0.55  fof(f47,plain,(
% 1.40/0.55    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.40/0.55    inference(nnf_transformation,[],[f27])).
% 1.40/0.55  fof(f27,plain,(
% 1.40/0.55    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.40/0.55    inference(ennf_transformation,[],[f6])).
% 1.40/0.55  fof(f6,axiom,(
% 1.40/0.55    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.40/0.55  fof(f91,plain,(
% 1.40/0.55    ( ! [X1] : (~v5_relat_1(X1,k2_relat_1(X1)) | v2_funct_2(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.40/0.55    inference(equality_resolution,[],[f72])).
% 1.40/0.55  fof(f72,plain,(
% 1.40/0.55    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f48])).
% 1.40/0.55  fof(f48,plain,(
% 1.40/0.55    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.40/0.55    inference(nnf_transformation,[],[f29])).
% 1.40/0.55  fof(f29,plain,(
% 1.40/0.55    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.40/0.55    inference(flattening,[],[f28])).
% 1.40/0.55  fof(f28,plain,(
% 1.40/0.55    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.40/0.55    inference(ennf_transformation,[],[f14])).
% 1.40/0.55  fof(f14,axiom,(
% 1.40/0.55    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 1.40/0.55  fof(f1057,plain,(
% 1.40/0.55    ~spl6_2 | spl6_3 | ~spl6_1),
% 1.40/0.55    inference(avatar_split_clause,[],[f1056,f101,f109,f105])).
% 1.40/0.55  fof(f105,plain,(
% 1.40/0.55    spl6_2 <=> v5_relat_1(sK3,sK1)),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.40/0.55  fof(f109,plain,(
% 1.40/0.55    spl6_3 <=> sK1 = k2_relat_1(sK3)),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.40/0.55  fof(f101,plain,(
% 1.40/0.55    spl6_1 <=> v1_relat_1(sK3)),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.40/0.55  fof(f1056,plain,(
% 1.40/0.55    sK1 = k2_relat_1(sK3) | ~v5_relat_1(sK3,sK1) | ~spl6_1),
% 1.40/0.55    inference(subsumption_resolution,[],[f1055,f102])).
% 1.40/0.55  fof(f102,plain,(
% 1.40/0.55    v1_relat_1(sK3) | ~spl6_1),
% 1.40/0.55    inference(avatar_component_clause,[],[f101])).
% 1.40/0.55  fof(f1055,plain,(
% 1.40/0.55    sK1 = k2_relat_1(sK3) | ~v5_relat_1(sK3,sK1) | ~v1_relat_1(sK3)),
% 1.40/0.55    inference(resolution,[],[f61,f71])).
% 1.40/0.55  fof(f71,plain,(
% 1.40/0.55    ( ! [X0,X1] : (~v2_funct_2(X1,X0) | k2_relat_1(X1) = X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f48])).
% 1.40/0.55  fof(f61,plain,(
% 1.40/0.55    v2_funct_2(sK3,sK1)),
% 1.40/0.55    inference(cnf_transformation,[],[f44])).
% 1.40/0.55  fof(f1046,plain,(
% 1.40/0.55    ~spl6_8 | spl6_9 | ~spl6_10),
% 1.40/0.55    inference(avatar_contradiction_clause,[],[f1045])).
% 1.40/0.55  fof(f1045,plain,(
% 1.40/0.55    $false | (~spl6_8 | spl6_9 | ~spl6_10)),
% 1.40/0.55    inference(subsumption_resolution,[],[f1026,f973])).
% 1.40/0.55  fof(f973,plain,(
% 1.40/0.55    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) | (~spl6_8 | ~spl6_10)),
% 1.40/0.55    inference(subsumption_resolution,[],[f963,f866])).
% 1.40/0.55  fof(f866,plain,(
% 1.40/0.55    v1_funct_2(sK4,k1_xboole_0,k1_xboole_0) | (~spl6_8 | ~spl6_10)),
% 1.40/0.55    inference(backward_demodulation,[],[f627,f145])).
% 1.40/0.55  fof(f145,plain,(
% 1.40/0.55    k1_xboole_0 = sK1 | ~spl6_8),
% 1.40/0.55    inference(avatar_component_clause,[],[f143])).
% 1.40/0.55  fof(f143,plain,(
% 1.40/0.55    spl6_8 <=> k1_xboole_0 = sK1),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.40/0.55  fof(f627,plain,(
% 1.40/0.55    v1_funct_2(sK4,sK1,k1_xboole_0) | ~spl6_10),
% 1.40/0.55    inference(backward_demodulation,[],[f59,f171])).
% 1.40/0.55  fof(f59,plain,(
% 1.40/0.55    v1_funct_2(sK4,sK1,sK2)),
% 1.40/0.55    inference(cnf_transformation,[],[f44])).
% 1.40/0.55  fof(f963,plain,(
% 1.40/0.55    ~v1_funct_2(sK4,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) | (~spl6_8 | ~spl6_10)),
% 1.40/0.55    inference(resolution,[],[f943,f98])).
% 1.40/0.55  fof(f98,plain,(
% 1.40/0.55    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)) )),
% 1.40/0.55    inference(equality_resolution,[],[f83])).
% 1.40/0.55  fof(f83,plain,(
% 1.40/0.55    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.40/0.55    inference(cnf_transformation,[],[f52])).
% 1.40/0.55  fof(f52,plain,(
% 1.40/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.55    inference(nnf_transformation,[],[f35])).
% 1.40/0.55  fof(f35,plain,(
% 1.40/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.55    inference(flattening,[],[f34])).
% 1.40/0.55  fof(f34,plain,(
% 1.40/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.55    inference(ennf_transformation,[],[f13])).
% 1.40/0.55  fof(f13,axiom,(
% 1.40/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.40/0.55  fof(f943,plain,(
% 1.40/0.55    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl6_8 | ~spl6_10)),
% 1.40/0.55    inference(forward_demodulation,[],[f628,f145])).
% 1.40/0.55  fof(f628,plain,(
% 1.40/0.55    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) | ~spl6_10),
% 1.40/0.55    inference(backward_demodulation,[],[f60,f171])).
% 1.40/0.55  fof(f1026,plain,(
% 1.40/0.55    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) | (~spl6_8 | spl6_9 | ~spl6_10)),
% 1.40/0.55    inference(forward_demodulation,[],[f1025,f145])).
% 1.40/0.55  fof(f1025,plain,(
% 1.40/0.55    sK1 != k1_relset_1(sK1,k1_xboole_0,sK4) | (spl6_9 | ~spl6_10)),
% 1.40/0.55    inference(forward_demodulation,[],[f166,f171])).
% 1.40/0.55  fof(f166,plain,(
% 1.40/0.55    sK1 != k1_relset_1(sK1,sK2,sK4) | spl6_9),
% 1.40/0.55    inference(avatar_component_clause,[],[f165])).
% 1.40/0.55  fof(f165,plain,(
% 1.40/0.55    spl6_9 <=> sK1 = k1_relset_1(sK1,sK2,sK4)),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 1.40/0.55  fof(f660,plain,(
% 1.40/0.55    spl6_41 | spl6_8 | ~spl6_10),
% 1.40/0.55    inference(avatar_split_clause,[],[f655,f169,f143,f657])).
% 1.40/0.55  fof(f655,plain,(
% 1.40/0.55    k1_xboole_0 = sK1 | k1_xboole_0 = sK4 | ~spl6_10),
% 1.40/0.55    inference(subsumption_resolution,[],[f644,f627])).
% 1.40/0.55  fof(f644,plain,(
% 1.40/0.55    ~v1_funct_2(sK4,sK1,k1_xboole_0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK4 | ~spl6_10),
% 1.40/0.55    inference(resolution,[],[f628,f96])).
% 1.40/0.55  fof(f96,plain,(
% 1.40/0.55    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2) )),
% 1.40/0.55    inference(equality_resolution,[],[f86])).
% 1.40/0.55  fof(f86,plain,(
% 1.40/0.55    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.40/0.55    inference(cnf_transformation,[],[f52])).
% 1.40/0.55  fof(f621,plain,(
% 1.40/0.55    spl6_25),
% 1.40/0.55    inference(avatar_contradiction_clause,[],[f620])).
% 1.40/0.55  fof(f620,plain,(
% 1.40/0.55    $false | spl6_25),
% 1.40/0.55    inference(subsumption_resolution,[],[f506,f375])).
% 1.40/0.55  fof(f375,plain,(
% 1.40/0.55    ~v5_relat_1(k5_relat_1(sK3,sK4),sK2) | spl6_25),
% 1.40/0.55    inference(avatar_component_clause,[],[f373])).
% 1.40/0.55  fof(f506,plain,(
% 1.40/0.55    v5_relat_1(k5_relat_1(sK3,sK4),sK2)),
% 1.40/0.55    inference(resolution,[],[f334,f81])).
% 1.40/0.55  fof(f81,plain,(
% 1.40/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f33])).
% 1.40/0.55  fof(f33,plain,(
% 1.40/0.55    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.55    inference(ennf_transformation,[],[f20])).
% 1.40/0.55  fof(f20,plain,(
% 1.40/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.40/0.55    inference(pure_predicate_removal,[],[f11])).
% 1.40/0.55  fof(f11,axiom,(
% 1.40/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.40/0.55  fof(f334,plain,(
% 1.40/0.55    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.40/0.55    inference(subsumption_resolution,[],[f333,f55])).
% 1.40/0.55  fof(f333,plain,(
% 1.40/0.55    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK3)),
% 1.40/0.55    inference(subsumption_resolution,[],[f332,f57])).
% 1.40/0.55  fof(f332,plain,(
% 1.40/0.55    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)),
% 1.40/0.55    inference(subsumption_resolution,[],[f331,f58])).
% 1.40/0.55  fof(f331,plain,(
% 1.40/0.55    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)),
% 1.40/0.55    inference(subsumption_resolution,[],[f330,f60])).
% 1.40/0.55  fof(f330,plain,(
% 1.40/0.55    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)),
% 1.40/0.55    inference(superposition,[],[f90,f290])).
% 1.40/0.55  fof(f90,plain,(
% 1.40/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f39])).
% 1.40/0.55  fof(f39,plain,(
% 1.40/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.40/0.55    inference(flattening,[],[f38])).
% 1.40/0.55  fof(f38,plain,(
% 1.40/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.40/0.55    inference(ennf_transformation,[],[f15])).
% 1.40/0.55  fof(f15,axiom,(
% 1.40/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.40/0.55  fof(f606,plain,(
% 1.40/0.55    spl6_9 | spl6_10),
% 1.40/0.55    inference(avatar_split_clause,[],[f605,f169,f165])).
% 1.40/0.55  fof(f605,plain,(
% 1.40/0.55    k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK4)),
% 1.40/0.55    inference(subsumption_resolution,[],[f597,f59])).
% 1.40/0.55  fof(f597,plain,(
% 1.40/0.55    ~v1_funct_2(sK4,sK1,sK2) | k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK4)),
% 1.40/0.55    inference(resolution,[],[f60,f82])).
% 1.40/0.55  fof(f82,plain,(
% 1.40/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.40/0.55    inference(cnf_transformation,[],[f52])).
% 1.40/0.55  fof(f577,plain,(
% 1.40/0.55    ~spl6_5 | spl6_6 | ~spl6_4),
% 1.40/0.55    inference(avatar_split_clause,[],[f576,f115,f123,f119])).
% 1.40/0.55  fof(f119,plain,(
% 1.40/0.55    spl6_5 <=> v5_relat_1(sK4,sK2)),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.40/0.55  fof(f123,plain,(
% 1.40/0.55    spl6_6 <=> sK2 = k2_relat_1(sK4)),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.40/0.55  fof(f115,plain,(
% 1.40/0.55    spl6_4 <=> v1_relat_1(sK4)),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.40/0.55  fof(f576,plain,(
% 1.40/0.55    sK2 = k2_relat_1(sK4) | ~v5_relat_1(sK4,sK2) | ~spl6_4),
% 1.40/0.55    inference(subsumption_resolution,[],[f575,f116])).
% 1.40/0.55  fof(f116,plain,(
% 1.40/0.55    v1_relat_1(sK4) | ~spl6_4),
% 1.40/0.55    inference(avatar_component_clause,[],[f115])).
% 1.40/0.55  fof(f575,plain,(
% 1.40/0.55    sK2 = k2_relat_1(sK4) | ~v5_relat_1(sK4,sK2) | ~v1_relat_1(sK4)),
% 1.40/0.55    inference(resolution,[],[f62,f71])).
% 1.40/0.55  fof(f62,plain,(
% 1.40/0.55    v2_funct_2(sK4,sK2)),
% 1.40/0.55    inference(cnf_transformation,[],[f44])).
% 1.40/0.55  fof(f535,plain,(
% 1.40/0.55    spl6_24),
% 1.40/0.55    inference(avatar_contradiction_clause,[],[f534])).
% 1.40/0.55  fof(f534,plain,(
% 1.40/0.55    $false | spl6_24),
% 1.40/0.55    inference(subsumption_resolution,[],[f533,f68])).
% 1.40/0.55  fof(f68,plain,(
% 1.40/0.55    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.40/0.55    inference(cnf_transformation,[],[f7])).
% 1.40/0.55  fof(f7,axiom,(
% 1.40/0.55    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.40/0.55  fof(f533,plain,(
% 1.40/0.55    ~v1_relat_1(k2_zfmisc_1(sK0,sK2)) | spl6_24),
% 1.40/0.55    inference(subsumption_resolution,[],[f515,f371])).
% 1.40/0.55  fof(f371,plain,(
% 1.40/0.55    ~v1_relat_1(k5_relat_1(sK3,sK4)) | spl6_24),
% 1.40/0.55    inference(avatar_component_clause,[],[f369])).
% 1.40/0.55  fof(f515,plain,(
% 1.40/0.55    v1_relat_1(k5_relat_1(sK3,sK4)) | ~v1_relat_1(k2_zfmisc_1(sK0,sK2))),
% 1.40/0.55    inference(resolution,[],[f334,f66])).
% 1.40/0.55  fof(f66,plain,(
% 1.40/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f25])).
% 1.40/0.55  fof(f25,plain,(
% 1.40/0.55    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.40/0.55    inference(ennf_transformation,[],[f5])).
% 1.40/0.55  fof(f5,axiom,(
% 1.40/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.40/0.55  fof(f376,plain,(
% 1.40/0.55    ~spl6_24 | ~spl6_25 | ~spl6_1 | ~spl6_3 | ~spl6_4 | ~spl6_6 | ~spl6_9),
% 1.40/0.55    inference(avatar_split_clause,[],[f367,f165,f123,f115,f109,f101,f373,f369])).
% 1.40/0.55  fof(f367,plain,(
% 1.40/0.55    ~v5_relat_1(k5_relat_1(sK3,sK4),sK2) | ~v1_relat_1(k5_relat_1(sK3,sK4)) | (~spl6_1 | ~spl6_3 | ~spl6_4 | ~spl6_6 | ~spl6_9)),
% 1.40/0.55    inference(subsumption_resolution,[],[f364,f329])).
% 1.40/0.55  fof(f364,plain,(
% 1.40/0.55    ~v5_relat_1(k5_relat_1(sK3,sK4),sK2) | v2_funct_2(k5_relat_1(sK3,sK4),sK2) | ~v1_relat_1(k5_relat_1(sK3,sK4)) | (~spl6_1 | ~spl6_3 | ~spl6_4 | ~spl6_6 | ~spl6_9)),
% 1.40/0.55    inference(superposition,[],[f91,f351])).
% 1.40/0.55  fof(f351,plain,(
% 1.40/0.55    sK2 = k2_relat_1(k5_relat_1(sK3,sK4)) | (~spl6_1 | ~spl6_3 | ~spl6_4 | ~spl6_6 | ~spl6_9)),
% 1.40/0.55    inference(subsumption_resolution,[],[f350,f102])).
% 1.40/0.55  fof(f350,plain,(
% 1.40/0.55    sK2 = k2_relat_1(k5_relat_1(sK3,sK4)) | ~v1_relat_1(sK3) | (~spl6_3 | ~spl6_4 | ~spl6_6 | ~spl6_9)),
% 1.40/0.55    inference(subsumption_resolution,[],[f348,f93])).
% 1.40/0.55  fof(f93,plain,(
% 1.40/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.40/0.55    inference(equality_resolution,[],[f73])).
% 1.40/0.55  fof(f73,plain,(
% 1.40/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.40/0.55    inference(cnf_transformation,[],[f50])).
% 1.40/0.55  fof(f348,plain,(
% 1.40/0.55    ~r1_tarski(sK1,sK1) | sK2 = k2_relat_1(k5_relat_1(sK3,sK4)) | ~v1_relat_1(sK3) | (~spl6_3 | ~spl6_4 | ~spl6_6 | ~spl6_9)),
% 1.40/0.55    inference(superposition,[],[f236,f111])).
% 1.40/0.55  fof(f111,plain,(
% 1.40/0.55    sK1 = k2_relat_1(sK3) | ~spl6_3),
% 1.40/0.55    inference(avatar_component_clause,[],[f109])).
% 1.40/0.55  fof(f236,plain,(
% 1.40/0.55    ( ! [X0] : (~r1_tarski(sK1,k2_relat_1(X0)) | sK2 = k2_relat_1(k5_relat_1(X0,sK4)) | ~v1_relat_1(X0)) ) | (~spl6_4 | ~spl6_6 | ~spl6_9)),
% 1.40/0.55    inference(forward_demodulation,[],[f235,f125])).
% 1.40/0.55  fof(f125,plain,(
% 1.40/0.55    sK2 = k2_relat_1(sK4) | ~spl6_6),
% 1.40/0.55    inference(avatar_component_clause,[],[f123])).
% 1.40/0.55  fof(f235,plain,(
% 1.40/0.55    ( ! [X0] : (~r1_tarski(sK1,k2_relat_1(X0)) | k2_relat_1(sK4) = k2_relat_1(k5_relat_1(X0,sK4)) | ~v1_relat_1(X0)) ) | (~spl6_4 | ~spl6_9)),
% 1.40/0.55    inference(subsumption_resolution,[],[f234,f116])).
% 1.40/0.55  fof(f234,plain,(
% 1.40/0.55    ( ! [X0] : (~r1_tarski(sK1,k2_relat_1(X0)) | k2_relat_1(sK4) = k2_relat_1(k5_relat_1(X0,sK4)) | ~v1_relat_1(X0) | ~v1_relat_1(sK4)) ) | ~spl6_9),
% 1.40/0.55    inference(superposition,[],[f65,f233])).
% 1.40/0.55  fof(f233,plain,(
% 1.40/0.55    sK1 = k1_relat_1(sK4) | ~spl6_9),
% 1.40/0.55    inference(forward_demodulation,[],[f157,f167])).
% 1.40/0.55  fof(f167,plain,(
% 1.40/0.55    sK1 = k1_relset_1(sK1,sK2,sK4) | ~spl6_9),
% 1.40/0.55    inference(avatar_component_clause,[],[f165])).
% 1.40/0.55  fof(f157,plain,(
% 1.40/0.55    k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4)),
% 1.40/0.55    inference(resolution,[],[f60,f80])).
% 1.40/0.55  fof(f80,plain,(
% 1.40/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f32])).
% 1.40/0.55  fof(f32,plain,(
% 1.40/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.55    inference(ennf_transformation,[],[f12])).
% 1.40/0.55  fof(f12,axiom,(
% 1.40/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.40/0.55  fof(f65,plain,(
% 1.40/0.55    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f24])).
% 1.40/0.55  fof(f24,plain,(
% 1.40/0.55    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.40/0.55    inference(flattening,[],[f23])).
% 1.40/0.55  fof(f23,plain,(
% 1.40/0.55    ! [X0] : (! [X1] : ((k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.40/0.55    inference(ennf_transformation,[],[f8])).
% 1.40/0.55  fof(f8,axiom,(
% 1.40/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0))))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).
% 1.40/0.55  fof(f184,plain,(
% 1.40/0.55    spl6_5),
% 1.40/0.55    inference(avatar_contradiction_clause,[],[f183])).
% 1.40/0.55  fof(f183,plain,(
% 1.40/0.55    $false | spl6_5),
% 1.40/0.55    inference(subsumption_resolution,[],[f156,f121])).
% 1.40/0.55  fof(f121,plain,(
% 1.40/0.55    ~v5_relat_1(sK4,sK2) | spl6_5),
% 1.40/0.55    inference(avatar_component_clause,[],[f119])).
% 1.40/0.55  fof(f156,plain,(
% 1.40/0.55    v5_relat_1(sK4,sK2)),
% 1.40/0.55    inference(resolution,[],[f60,f81])).
% 1.40/0.55  fof(f180,plain,(
% 1.40/0.55    spl6_2),
% 1.40/0.55    inference(avatar_contradiction_clause,[],[f179])).
% 1.40/0.55  fof(f179,plain,(
% 1.40/0.55    $false | spl6_2),
% 1.40/0.55    inference(subsumption_resolution,[],[f130,f107])).
% 1.40/0.55  fof(f107,plain,(
% 1.40/0.55    ~v5_relat_1(sK3,sK1) | spl6_2),
% 1.40/0.55    inference(avatar_component_clause,[],[f105])).
% 1.40/0.55  fof(f130,plain,(
% 1.40/0.55    v5_relat_1(sK3,sK1)),
% 1.40/0.55    inference(resolution,[],[f57,f81])).
% 1.40/0.55  fof(f177,plain,(
% 1.40/0.55    spl6_4),
% 1.40/0.55    inference(avatar_contradiction_clause,[],[f176])).
% 1.40/0.55  fof(f176,plain,(
% 1.40/0.55    $false | spl6_4),
% 1.40/0.55    inference(subsumption_resolution,[],[f175,f68])).
% 1.40/0.55  fof(f175,plain,(
% 1.40/0.55    ~v1_relat_1(k2_zfmisc_1(sK1,sK2)) | spl6_4),
% 1.40/0.55    inference(subsumption_resolution,[],[f160,f117])).
% 1.40/0.55  fof(f117,plain,(
% 1.40/0.55    ~v1_relat_1(sK4) | spl6_4),
% 1.40/0.55    inference(avatar_component_clause,[],[f115])).
% 1.40/0.55  fof(f160,plain,(
% 1.40/0.55    v1_relat_1(sK4) | ~v1_relat_1(k2_zfmisc_1(sK1,sK2))),
% 1.40/0.55    inference(resolution,[],[f60,f66])).
% 1.40/0.55  fof(f151,plain,(
% 1.40/0.55    spl6_1),
% 1.40/0.55    inference(avatar_contradiction_clause,[],[f150])).
% 1.40/0.55  fof(f150,plain,(
% 1.40/0.55    $false | spl6_1),
% 1.40/0.55    inference(subsumption_resolution,[],[f149,f68])).
% 1.40/0.55  fof(f149,plain,(
% 1.40/0.55    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl6_1),
% 1.40/0.55    inference(subsumption_resolution,[],[f134,f103])).
% 1.40/0.55  fof(f103,plain,(
% 1.40/0.55    ~v1_relat_1(sK3) | spl6_1),
% 1.40/0.55    inference(avatar_component_clause,[],[f101])).
% 1.40/0.55  fof(f134,plain,(
% 1.40/0.55    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.40/0.55    inference(resolution,[],[f57,f66])).
% 1.40/0.55  % SZS output end Proof for theBenchmark
% 1.40/0.55  % (14185)------------------------------
% 1.40/0.55  % (14185)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (14185)Termination reason: Refutation
% 1.40/0.55  
% 1.40/0.55  % (14185)Memory used [KB]: 11129
% 1.40/0.55  % (14185)Time elapsed: 0.144 s
% 1.40/0.55  % (14185)------------------------------
% 1.40/0.55  % (14185)------------------------------
% 1.40/0.55  % (14183)Success in time 0.195 s
%------------------------------------------------------------------------------
