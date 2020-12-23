%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:32 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 405 expanded)
%              Number of leaves         :   15 ( 141 expanded)
%              Depth                    :   15
%              Number of atoms          :  383 (3487 expanded)
%              Number of equality atoms :   73 (1062 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f466,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f153,f173,f241,f465])).

fof(f465,plain,
    ( ~ spl12_1
    | spl12_2
    | ~ spl12_3 ),
    inference(avatar_contradiction_clause,[],[f464])).

fof(f464,plain,
    ( $false
    | ~ spl12_1
    | spl12_2
    | ~ spl12_3 ),
    inference(subsumption_resolution,[],[f453,f329])).

fof(f329,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK6(sK0,sK1,sK2)),sK1)
    | ~ spl12_1
    | spl12_2 ),
    inference(unit_resulting_resolution,[],[f148,f227])).

fof(f227,plain,
    ( ! [X8] :
        ( v1_funct_2(sK2,sK0,X8)
        | ~ r2_hidden(k1_funct_1(sK2,sK6(sK0,X8,sK2)),X8) )
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f226,f172])).

fof(f172,plain,(
    v1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f154,f156])).

fof(f156,plain,(
    sK2 = sK9(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f71,f138])).

fof(f138,plain,(
    ! [X6,X0,X1] :
      ( sK9(X0,X1,X6) = X6
      | ~ r2_hidden(X6,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f108])).

fof(f108,plain,(
    ! [X6,X2,X0,X1] :
      ( sK9(X0,X1,X6) = X6
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ( ( ! [X4] :
                ( ~ r1_tarski(k2_relat_1(X4),X1)
                | k1_relat_1(X4) != X0
                | sK7(X0,X1,X2) != X4
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( ( r1_tarski(k2_relat_1(sK8(X0,X1,X2)),X1)
              & k1_relat_1(sK8(X0,X1,X2)) = X0
              & sK7(X0,X1,X2) = sK8(X0,X1,X2)
              & v1_funct_1(sK8(X0,X1,X2))
              & v1_relat_1(sK8(X0,X1,X2)) )
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r1_tarski(k2_relat_1(X7),X1)
                  | k1_relat_1(X7) != X0
                  | X6 != X7
                  | ~ v1_funct_1(X7)
                  | ~ v1_relat_1(X7) ) )
            & ( ( r1_tarski(k2_relat_1(sK9(X0,X1,X6)),X1)
                & k1_relat_1(sK9(X0,X1,X6)) = X0
                & sK9(X0,X1,X6) = X6
                & v1_funct_1(sK9(X0,X1,X6))
                & v1_relat_1(sK9(X0,X1,X6)) )
              | ~ r2_hidden(X6,X2) ) )
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f64,f67,f66,f65])).

fof(f65,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r1_tarski(k2_relat_1(X4),X1)
                | k1_relat_1(X4) != X0
                | X3 != X4
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r1_tarski(k2_relat_1(X5),X1)
                & k1_relat_1(X5) = X0
                & X3 = X5
                & v1_funct_1(X5)
                & v1_relat_1(X5) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r1_tarski(k2_relat_1(X4),X1)
              | k1_relat_1(X4) != X0
              | sK7(X0,X1,X2) != X4
              | ~ v1_funct_1(X4)
              | ~ v1_relat_1(X4) )
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r1_tarski(k2_relat_1(X5),X1)
              & k1_relat_1(X5) = X0
              & sK7(X0,X1,X2) = X5
              & v1_funct_1(X5)
              & v1_relat_1(X5) )
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r1_tarski(k2_relat_1(X5),X1)
          & k1_relat_1(X5) = X0
          & sK7(X0,X1,X2) = X5
          & v1_funct_1(X5)
          & v1_relat_1(X5) )
     => ( r1_tarski(k2_relat_1(sK8(X0,X1,X2)),X1)
        & k1_relat_1(sK8(X0,X1,X2)) = X0
        & sK7(X0,X1,X2) = sK8(X0,X1,X2)
        & v1_funct_1(sK8(X0,X1,X2))
        & v1_relat_1(sK8(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r1_tarski(k2_relat_1(X8),X1)
          & k1_relat_1(X8) = X0
          & X6 = X8
          & v1_funct_1(X8)
          & v1_relat_1(X8) )
     => ( r1_tarski(k2_relat_1(sK9(X0,X1,X6)),X1)
        & k1_relat_1(sK9(X0,X1,X6)) = X0
        & sK9(X0,X1,X6) = X6
        & v1_funct_1(sK9(X0,X1,X6))
        & v1_relat_1(sK9(X0,X1,X6)) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r1_tarski(k2_relat_1(X4),X1)
                  | k1_relat_1(X4) != X0
                  | X3 != X4
                  | ~ v1_funct_1(X4)
                  | ~ v1_relat_1(X4) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X5] :
                  ( r1_tarski(k2_relat_1(X5),X1)
                  & k1_relat_1(X5) = X0
                  & X3 = X5
                  & v1_funct_1(X5)
                  & v1_relat_1(X5) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r1_tarski(k2_relat_1(X7),X1)
                  | k1_relat_1(X7) != X0
                  | X6 != X7
                  | ~ v1_funct_1(X7)
                  | ~ v1_relat_1(X7) ) )
            & ( ? [X8] :
                  ( r1_tarski(k2_relat_1(X8),X1)
                  & k1_relat_1(X8) = X0
                  & X6 = X8
                  & v1_funct_1(X8)
                  & v1_relat_1(X8) )
              | ~ r2_hidden(X6,X2) ) )
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r1_tarski(k2_relat_1(X4),X1)
                  | k1_relat_1(X4) != X0
                  | X3 != X4
                  | ~ v1_funct_1(X4)
                  | ~ v1_relat_1(X4) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4] :
                  ( r1_tarski(k2_relat_1(X4),X1)
                  & k1_relat_1(X4) = X0
                  & X3 = X4
                  & v1_funct_1(X4)
                  & v1_relat_1(X4) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4] :
                  ( ~ r1_tarski(k2_relat_1(X4),X1)
                  | k1_relat_1(X4) != X0
                  | X3 != X4
                  | ~ v1_funct_1(X4)
                  | ~ v1_relat_1(X4) ) )
            & ( ? [X4] :
                  ( r1_tarski(k2_relat_1(X4),X1)
                  & k1_relat_1(X4) = X0
                  & X3 = X4
                  & v1_funct_1(X4)
                  & v1_relat_1(X4) )
              | ~ r2_hidden(X3,X2) ) )
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( k1_funct_2(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r1_tarski(k2_relat_1(X4),X1)
              & k1_relat_1(X4) = X0
              & X3 = X4
              & v1_funct_1(X4)
              & v1_relat_1(X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_funct_2)).

fof(f71,plain,(
    r2_hidden(sK2,k1_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) )
    & r2_hidden(sK2,k1_funct_2(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f44])).

fof(f44,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2) )
        & r2_hidden(X2,k1_funct_2(X0,X1)) )
   => ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(sK2) )
      & r2_hidden(sK2,k1_funct_2(sK0,sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X2,k1_funct_2(X0,X1))
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_2)).

fof(f154,plain,(
    v1_relat_1(sK9(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f71,f140])).

fof(f140,plain,(
    ! [X6,X0,X1] :
      ( v1_relat_1(sK9(X0,X1,X6))
      | ~ r2_hidden(X6,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f106])).

fof(f106,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_relat_1(sK9(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f68])).

fof(f226,plain,
    ( ! [X8] :
        ( ~ r2_hidden(k1_funct_1(sK2,sK6(sK0,X8,sK2)),X8)
        | v1_funct_2(sK2,sK0,X8)
        | ~ v1_relat_1(sK2) )
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f211,f143])).

fof(f143,plain,
    ( v1_funct_1(sK2)
    | ~ spl12_1 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl12_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f211,plain,(
    ! [X8] :
      ( ~ r2_hidden(k1_funct_1(sK2,sK6(sK0,X8,sK2)),X8)
      | v1_funct_2(sK2,sK0,X8)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f128,f167])).

fof(f167,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f157,f156])).

fof(f157,plain,(
    sK0 = k1_relat_1(sK9(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f71,f137])).

fof(f137,plain,(
    ! [X6,X0,X1] :
      ( k1_relat_1(sK9(X0,X1,X6)) = X0
      | ~ r2_hidden(X6,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f109])).

fof(f109,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_relat_1(sK9(X0,X1,X6)) = X0
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f68])).

fof(f128,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_relat_1(X2),X1)
      | ~ r2_hidden(k1_funct_1(X2,sK6(k1_relat_1(X2),X1,X2)),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ r2_hidden(k1_funct_1(X2,sK6(X0,X1,X2)),X1)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ( ~ r2_hidden(k1_funct_1(X2,sK6(X0,X1,X2)),X1)
        & r2_hidden(sK6(X0,X1,X2),X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f39,f61])).

fof(f61,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(k1_funct_1(X2,sK6(X0,X1,X2)),X1)
        & r2_hidden(sK6(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( ! [X3] :
              ( r2_hidden(X3,X0)
             => r2_hidden(k1_funct_1(X2,X3),X1) )
          & k1_relat_1(X2) = X0 )
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).

fof(f148,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl12_2 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl12_2
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f453,plain,
    ( r2_hidden(k1_funct_1(sK2,sK6(sK0,sK1,sK2)),sK1)
    | ~ spl12_1
    | spl12_2
    | ~ spl12_3 ),
    inference(unit_resulting_resolution,[],[f244,f318,f220])).

fof(f220,plain,
    ( ! [X0,X1] :
        ( ~ v5_relat_1(sK2,X1)
        | r2_hidden(k1_funct_1(sK2,X0),X1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f219,f172])).

fof(f219,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(k1_funct_1(sK2,X0),X1)
        | ~ v5_relat_1(sK2,X1)
        | ~ v1_relat_1(sK2) )
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f205,f143])).

fof(f205,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(k1_funct_1(sK2,X0),X1)
      | ~ v1_funct_1(sK2)
      | ~ v5_relat_1(sK2,X1)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f83,f167])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X2),X0)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

fof(f318,plain,
    ( r2_hidden(sK6(sK0,sK1,sK2),sK0)
    | ~ spl12_1
    | spl12_2 ),
    inference(unit_resulting_resolution,[],[f148,f229])).

fof(f229,plain,
    ( ! [X10] :
        ( v1_funct_2(sK2,sK0,X10)
        | r2_hidden(sK6(sK0,X10,sK2),sK0) )
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f228,f172])).

fof(f228,plain,
    ( ! [X10] :
        ( r2_hidden(sK6(sK0,X10,sK2),sK0)
        | v1_funct_2(sK2,sK0,X10)
        | ~ v1_relat_1(sK2) )
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f213,f143])).

fof(f213,plain,(
    ! [X10] :
      ( r2_hidden(sK6(sK0,X10,sK2),sK0)
      | v1_funct_2(sK2,sK0,X10)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f129,f167])).

fof(f129,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_relat_1(X2),X1)
      | r2_hidden(sK6(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | r2_hidden(sK6(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f244,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl12_3 ),
    inference(unit_resulting_resolution,[],[f151,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f151,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl12_3 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl12_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f241,plain,(
    spl12_3 ),
    inference(avatar_split_clause,[],[f240,f150])).

fof(f240,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f235,f167])).

fof(f235,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) ),
    inference(unit_resulting_resolution,[],[f172,f123,f168,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f168,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(backward_demodulation,[],[f158,f156])).

fof(f158,plain,(
    r1_tarski(k2_relat_1(sK9(sK0,sK1,sK2)),sK1) ),
    inference(unit_resulting_resolution,[],[f71,f136])).

fof(f136,plain,(
    ! [X6,X0,X1] :
      ( r1_tarski(k2_relat_1(sK9(X0,X1,X6)),X1)
      | ~ r2_hidden(X6,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f110])).

fof(f110,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_tarski(k2_relat_1(sK9(X0,X1,X6)),X1)
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f68])).

fof(f123,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f173,plain,(
    spl12_1 ),
    inference(avatar_split_clause,[],[f169,f142])).

fof(f169,plain,(
    v1_funct_1(sK2) ),
    inference(forward_demodulation,[],[f155,f156])).

fof(f155,plain,(
    v1_funct_1(sK9(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f71,f139])).

fof(f139,plain,(
    ! [X6,X0,X1] :
      ( v1_funct_1(sK9(X0,X1,X6))
      | ~ r2_hidden(X6,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f107])).

fof(f107,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_funct_1(sK9(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f68])).

fof(f153,plain,
    ( ~ spl12_1
    | ~ spl12_2
    | ~ spl12_3 ),
    inference(avatar_split_clause,[],[f72,f150,f146,f142])).

fof(f72,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:48:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.52  % (32737)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (32730)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (32722)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (32720)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (32721)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (32715)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (32718)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.55  % (32741)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  % (32716)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.55  % (32724)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.43/0.55  % (32736)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.43/0.55  % (32738)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.43/0.56  % (32725)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.43/0.56  % (32743)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.43/0.56  % (32717)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.43/0.56  % (32734)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.43/0.56  % (32731)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.43/0.56  % (32727)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.43/0.56  % (32739)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.43/0.57  % (32733)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.43/0.57  % (32728)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.43/0.57  % (32723)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.43/0.57  % (32726)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.43/0.57  % (32735)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.43/0.57  % (32740)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.43/0.57  % (32732)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.57/0.58  % (32741)Refutation found. Thanks to Tanya!
% 1.57/0.58  % SZS status Theorem for theBenchmark
% 1.57/0.58  % SZS output start Proof for theBenchmark
% 1.57/0.58  fof(f466,plain,(
% 1.57/0.58    $false),
% 1.57/0.58    inference(avatar_sat_refutation,[],[f153,f173,f241,f465])).
% 1.57/0.58  fof(f465,plain,(
% 1.57/0.58    ~spl12_1 | spl12_2 | ~spl12_3),
% 1.57/0.58    inference(avatar_contradiction_clause,[],[f464])).
% 1.57/0.58  fof(f464,plain,(
% 1.57/0.58    $false | (~spl12_1 | spl12_2 | ~spl12_3)),
% 1.57/0.58    inference(subsumption_resolution,[],[f453,f329])).
% 1.57/0.58  fof(f329,plain,(
% 1.57/0.58    ~r2_hidden(k1_funct_1(sK2,sK6(sK0,sK1,sK2)),sK1) | (~spl12_1 | spl12_2)),
% 1.57/0.58    inference(unit_resulting_resolution,[],[f148,f227])).
% 1.57/0.58  fof(f227,plain,(
% 1.57/0.58    ( ! [X8] : (v1_funct_2(sK2,sK0,X8) | ~r2_hidden(k1_funct_1(sK2,sK6(sK0,X8,sK2)),X8)) ) | ~spl12_1),
% 1.57/0.58    inference(subsumption_resolution,[],[f226,f172])).
% 1.57/0.58  fof(f172,plain,(
% 1.57/0.58    v1_relat_1(sK2)),
% 1.57/0.58    inference(forward_demodulation,[],[f154,f156])).
% 1.57/0.58  fof(f156,plain,(
% 1.57/0.58    sK2 = sK9(sK0,sK1,sK2)),
% 1.57/0.58    inference(unit_resulting_resolution,[],[f71,f138])).
% 1.57/0.58  fof(f138,plain,(
% 1.57/0.58    ( ! [X6,X0,X1] : (sK9(X0,X1,X6) = X6 | ~r2_hidden(X6,k1_funct_2(X0,X1))) )),
% 1.57/0.58    inference(equality_resolution,[],[f108])).
% 1.57/0.58  fof(f108,plain,(
% 1.57/0.58    ( ! [X6,X2,X0,X1] : (sK9(X0,X1,X6) = X6 | ~r2_hidden(X6,X2) | k1_funct_2(X0,X1) != X2) )),
% 1.57/0.58    inference(cnf_transformation,[],[f68])).
% 1.57/0.58  fof(f68,plain,(
% 1.57/0.58    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | sK7(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK7(X0,X1,X2),X2)) & ((r1_tarski(k2_relat_1(sK8(X0,X1,X2)),X1) & k1_relat_1(sK8(X0,X1,X2)) = X0 & sK7(X0,X1,X2) = sK8(X0,X1,X2) & v1_funct_1(sK8(X0,X1,X2)) & v1_relat_1(sK8(X0,X1,X2))) | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X1) | k1_relat_1(X7) != X0 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & ((r1_tarski(k2_relat_1(sK9(X0,X1,X6)),X1) & k1_relat_1(sK9(X0,X1,X6)) = X0 & sK9(X0,X1,X6) = X6 & v1_funct_1(sK9(X0,X1,X6)) & v1_relat_1(sK9(X0,X1,X6))) | ~r2_hidden(X6,X2))) | k1_funct_2(X0,X1) != X2))),
% 1.57/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f64,f67,f66,f65])).
% 1.57/0.58  fof(f65,plain,(
% 1.57/0.58    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X1) & k1_relat_1(X5) = X0 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2))) => ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | sK7(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X1) & k1_relat_1(X5) = X0 & sK7(X0,X1,X2) = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(sK7(X0,X1,X2),X2))))),
% 1.57/0.58    introduced(choice_axiom,[])).
% 1.57/0.58  fof(f66,plain,(
% 1.57/0.58    ! [X2,X1,X0] : (? [X5] : (r1_tarski(k2_relat_1(X5),X1) & k1_relat_1(X5) = X0 & sK7(X0,X1,X2) = X5 & v1_funct_1(X5) & v1_relat_1(X5)) => (r1_tarski(k2_relat_1(sK8(X0,X1,X2)),X1) & k1_relat_1(sK8(X0,X1,X2)) = X0 & sK7(X0,X1,X2) = sK8(X0,X1,X2) & v1_funct_1(sK8(X0,X1,X2)) & v1_relat_1(sK8(X0,X1,X2))))),
% 1.57/0.58    introduced(choice_axiom,[])).
% 1.57/0.58  fof(f67,plain,(
% 1.57/0.58    ! [X6,X1,X0] : (? [X8] : (r1_tarski(k2_relat_1(X8),X1) & k1_relat_1(X8) = X0 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) => (r1_tarski(k2_relat_1(sK9(X0,X1,X6)),X1) & k1_relat_1(sK9(X0,X1,X6)) = X0 & sK9(X0,X1,X6) = X6 & v1_funct_1(sK9(X0,X1,X6)) & v1_relat_1(sK9(X0,X1,X6))))),
% 1.57/0.58    introduced(choice_axiom,[])).
% 1.57/0.58  fof(f64,plain,(
% 1.57/0.58    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X1) & k1_relat_1(X5) = X0 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X1) | k1_relat_1(X7) != X0 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & (? [X8] : (r1_tarski(k2_relat_1(X8),X1) & k1_relat_1(X8) = X0 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) | ~r2_hidden(X6,X2))) | k1_funct_2(X0,X1) != X2))),
% 1.57/0.58    inference(rectify,[],[f63])).
% 1.57/0.58  fof(f63,plain,(
% 1.57/0.58    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4))) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | ~r2_hidden(X3,X2))) | k1_funct_2(X0,X1) != X2))),
% 1.57/0.58    inference(nnf_transformation,[],[f17])).
% 1.57/0.58  fof(f17,axiom,(
% 1.57/0.58    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 1.57/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_funct_2)).
% 1.57/0.58  fof(f71,plain,(
% 1.57/0.58    r2_hidden(sK2,k1_funct_2(sK0,sK1))),
% 1.57/0.58    inference(cnf_transformation,[],[f45])).
% 1.57/0.58  fof(f45,plain,(
% 1.57/0.58    (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) & r2_hidden(sK2,k1_funct_2(sK0,sK1))),
% 1.57/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f44])).
% 1.57/0.58  fof(f44,plain,(
% 1.57/0.58    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1))) => ((~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) & r2_hidden(sK2,k1_funct_2(sK0,sK1)))),
% 1.57/0.58    introduced(choice_axiom,[])).
% 1.57/0.58  fof(f23,plain,(
% 1.57/0.58    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1)))),
% 1.57/0.58    inference(ennf_transformation,[],[f21])).
% 1.57/0.58  fof(f21,negated_conjecture,(
% 1.57/0.58    ~! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.57/0.58    inference(negated_conjecture,[],[f20])).
% 1.57/0.58  fof(f20,conjecture,(
% 1.57/0.58    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.57/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_2)).
% 1.57/0.58  fof(f154,plain,(
% 1.57/0.58    v1_relat_1(sK9(sK0,sK1,sK2))),
% 1.57/0.58    inference(unit_resulting_resolution,[],[f71,f140])).
% 1.57/0.58  fof(f140,plain,(
% 1.57/0.58    ( ! [X6,X0,X1] : (v1_relat_1(sK9(X0,X1,X6)) | ~r2_hidden(X6,k1_funct_2(X0,X1))) )),
% 1.57/0.58    inference(equality_resolution,[],[f106])).
% 1.57/0.58  fof(f106,plain,(
% 1.57/0.58    ( ! [X6,X2,X0,X1] : (v1_relat_1(sK9(X0,X1,X6)) | ~r2_hidden(X6,X2) | k1_funct_2(X0,X1) != X2) )),
% 1.57/0.58    inference(cnf_transformation,[],[f68])).
% 1.57/0.58  fof(f226,plain,(
% 1.57/0.58    ( ! [X8] : (~r2_hidden(k1_funct_1(sK2,sK6(sK0,X8,sK2)),X8) | v1_funct_2(sK2,sK0,X8) | ~v1_relat_1(sK2)) ) | ~spl12_1),
% 1.57/0.58    inference(subsumption_resolution,[],[f211,f143])).
% 1.57/0.58  fof(f143,plain,(
% 1.57/0.58    v1_funct_1(sK2) | ~spl12_1),
% 1.57/0.58    inference(avatar_component_clause,[],[f142])).
% 1.57/0.58  fof(f142,plain,(
% 1.57/0.58    spl12_1 <=> v1_funct_1(sK2)),
% 1.57/0.58    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).
% 1.57/0.58  fof(f211,plain,(
% 1.57/0.58    ( ! [X8] : (~r2_hidden(k1_funct_1(sK2,sK6(sK0,X8,sK2)),X8) | v1_funct_2(sK2,sK0,X8) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 1.57/0.58    inference(superposition,[],[f128,f167])).
% 1.57/0.58  fof(f167,plain,(
% 1.57/0.58    sK0 = k1_relat_1(sK2)),
% 1.57/0.58    inference(backward_demodulation,[],[f157,f156])).
% 1.57/0.58  fof(f157,plain,(
% 1.57/0.58    sK0 = k1_relat_1(sK9(sK0,sK1,sK2))),
% 1.57/0.58    inference(unit_resulting_resolution,[],[f71,f137])).
% 1.57/0.58  fof(f137,plain,(
% 1.57/0.58    ( ! [X6,X0,X1] : (k1_relat_1(sK9(X0,X1,X6)) = X0 | ~r2_hidden(X6,k1_funct_2(X0,X1))) )),
% 1.57/0.58    inference(equality_resolution,[],[f109])).
% 1.57/0.58  fof(f109,plain,(
% 1.57/0.58    ( ! [X6,X2,X0,X1] : (k1_relat_1(sK9(X0,X1,X6)) = X0 | ~r2_hidden(X6,X2) | k1_funct_2(X0,X1) != X2) )),
% 1.57/0.58    inference(cnf_transformation,[],[f68])).
% 1.57/0.58  fof(f128,plain,(
% 1.57/0.58    ( ! [X2,X1] : (v1_funct_2(X2,k1_relat_1(X2),X1) | ~r2_hidden(k1_funct_1(X2,sK6(k1_relat_1(X2),X1,X2)),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.57/0.58    inference(equality_resolution,[],[f103])).
% 1.57/0.58  fof(f103,plain,(
% 1.57/0.58    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~r2_hidden(k1_funct_1(X2,sK6(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.57/0.58    inference(cnf_transformation,[],[f62])).
% 1.57/0.58  fof(f62,plain,(
% 1.57/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~r2_hidden(k1_funct_1(X2,sK6(X0,X1,X2)),X1) & r2_hidden(sK6(X0,X1,X2),X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.57/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f39,f61])).
% 1.57/0.58  fof(f61,plain,(
% 1.57/0.58    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) => (~r2_hidden(k1_funct_1(X2,sK6(X0,X1,X2)),X1) & r2_hidden(sK6(X0,X1,X2),X0)))),
% 1.57/0.58    introduced(choice_axiom,[])).
% 1.57/0.58  fof(f39,plain,(
% 1.57/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.57/0.58    inference(flattening,[],[f38])).
% 1.57/0.58  fof(f38,plain,(
% 1.57/0.58    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.57/0.58    inference(ennf_transformation,[],[f19])).
% 1.57/0.58  fof(f19,axiom,(
% 1.57/0.58    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 1.57/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).
% 1.57/0.58  fof(f148,plain,(
% 1.57/0.58    ~v1_funct_2(sK2,sK0,sK1) | spl12_2),
% 1.57/0.58    inference(avatar_component_clause,[],[f146])).
% 1.57/0.58  fof(f146,plain,(
% 1.57/0.58    spl12_2 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.57/0.58    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).
% 1.57/0.58  fof(f453,plain,(
% 1.57/0.58    r2_hidden(k1_funct_1(sK2,sK6(sK0,sK1,sK2)),sK1) | (~spl12_1 | spl12_2 | ~spl12_3)),
% 1.57/0.58    inference(unit_resulting_resolution,[],[f244,f318,f220])).
% 1.57/0.58  fof(f220,plain,(
% 1.57/0.58    ( ! [X0,X1] : (~v5_relat_1(sK2,X1) | r2_hidden(k1_funct_1(sK2,X0),X1) | ~r2_hidden(X0,sK0)) ) | ~spl12_1),
% 1.57/0.58    inference(subsumption_resolution,[],[f219,f172])).
% 1.57/0.58  fof(f219,plain,(
% 1.57/0.58    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK2,X0),X1) | ~v5_relat_1(sK2,X1) | ~v1_relat_1(sK2)) ) | ~spl12_1),
% 1.57/0.58    inference(subsumption_resolution,[],[f205,f143])).
% 1.57/0.58  fof(f205,plain,(
% 1.57/0.58    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK2,X0),X1) | ~v1_funct_1(sK2) | ~v5_relat_1(sK2,X1) | ~v1_relat_1(sK2)) )),
% 1.57/0.58    inference(superposition,[],[f83,f167])).
% 1.57/0.58  fof(f83,plain,(
% 1.57/0.58    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.57/0.58    inference(cnf_transformation,[],[f30])).
% 1.57/0.58  fof(f30,plain,(
% 1.57/0.58    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.57/0.58    inference(flattening,[],[f29])).
% 1.57/0.58  fof(f29,plain,(
% 1.57/0.58    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.57/0.58    inference(ennf_transformation,[],[f8])).
% 1.57/0.58  fof(f8,axiom,(
% 1.57/0.58    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 1.57/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).
% 1.57/0.58  fof(f318,plain,(
% 1.57/0.58    r2_hidden(sK6(sK0,sK1,sK2),sK0) | (~spl12_1 | spl12_2)),
% 1.57/0.58    inference(unit_resulting_resolution,[],[f148,f229])).
% 1.57/0.58  fof(f229,plain,(
% 1.57/0.58    ( ! [X10] : (v1_funct_2(sK2,sK0,X10) | r2_hidden(sK6(sK0,X10,sK2),sK0)) ) | ~spl12_1),
% 1.57/0.58    inference(subsumption_resolution,[],[f228,f172])).
% 1.57/0.58  fof(f228,plain,(
% 1.57/0.58    ( ! [X10] : (r2_hidden(sK6(sK0,X10,sK2),sK0) | v1_funct_2(sK2,sK0,X10) | ~v1_relat_1(sK2)) ) | ~spl12_1),
% 1.57/0.58    inference(subsumption_resolution,[],[f213,f143])).
% 1.57/0.58  fof(f213,plain,(
% 1.57/0.58    ( ! [X10] : (r2_hidden(sK6(sK0,X10,sK2),sK0) | v1_funct_2(sK2,sK0,X10) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 1.57/0.58    inference(superposition,[],[f129,f167])).
% 1.57/0.58  fof(f129,plain,(
% 1.57/0.58    ( ! [X2,X1] : (v1_funct_2(X2,k1_relat_1(X2),X1) | r2_hidden(sK6(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.57/0.58    inference(equality_resolution,[],[f102])).
% 1.57/0.58  fof(f102,plain,(
% 1.57/0.58    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | r2_hidden(sK6(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.57/0.58    inference(cnf_transformation,[],[f62])).
% 1.57/0.58  fof(f244,plain,(
% 1.57/0.58    v5_relat_1(sK2,sK1) | ~spl12_3),
% 1.57/0.58    inference(unit_resulting_resolution,[],[f151,f97])).
% 1.57/0.58  fof(f97,plain,(
% 1.57/0.58    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.57/0.58    inference(cnf_transformation,[],[f35])).
% 1.57/0.58  fof(f35,plain,(
% 1.57/0.58    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.57/0.58    inference(ennf_transformation,[],[f22])).
% 1.57/0.58  fof(f22,plain,(
% 1.57/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.57/0.58    inference(pure_predicate_removal,[],[f10])).
% 1.57/0.58  fof(f10,axiom,(
% 1.57/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.57/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.57/0.58  fof(f151,plain,(
% 1.57/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl12_3),
% 1.57/0.58    inference(avatar_component_clause,[],[f150])).
% 1.57/0.58  fof(f150,plain,(
% 1.57/0.58    spl12_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.57/0.58    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).
% 1.57/0.58  fof(f241,plain,(
% 1.57/0.58    spl12_3),
% 1.57/0.58    inference(avatar_split_clause,[],[f240,f150])).
% 1.57/0.58  fof(f240,plain,(
% 1.57/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.57/0.58    inference(forward_demodulation,[],[f235,f167])).
% 1.57/0.58  fof(f235,plain,(
% 1.57/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))),
% 1.57/0.58    inference(unit_resulting_resolution,[],[f172,f123,f168,f95])).
% 1.57/0.58  fof(f95,plain,(
% 1.57/0.58    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 1.57/0.58    inference(cnf_transformation,[],[f33])).
% 1.57/0.58  fof(f33,plain,(
% 1.57/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.57/0.58    inference(flattening,[],[f32])).
% 1.57/0.58  fof(f32,plain,(
% 1.57/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.57/0.58    inference(ennf_transformation,[],[f12])).
% 1.57/0.58  fof(f12,axiom,(
% 1.57/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.57/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 1.57/0.58  fof(f168,plain,(
% 1.57/0.58    r1_tarski(k2_relat_1(sK2),sK1)),
% 1.57/0.58    inference(backward_demodulation,[],[f158,f156])).
% 1.57/0.58  fof(f158,plain,(
% 1.57/0.58    r1_tarski(k2_relat_1(sK9(sK0,sK1,sK2)),sK1)),
% 1.57/0.58    inference(unit_resulting_resolution,[],[f71,f136])).
% 1.57/0.58  fof(f136,plain,(
% 1.57/0.58    ( ! [X6,X0,X1] : (r1_tarski(k2_relat_1(sK9(X0,X1,X6)),X1) | ~r2_hidden(X6,k1_funct_2(X0,X1))) )),
% 1.57/0.58    inference(equality_resolution,[],[f110])).
% 1.57/0.58  fof(f110,plain,(
% 1.57/0.58    ( ! [X6,X2,X0,X1] : (r1_tarski(k2_relat_1(sK9(X0,X1,X6)),X1) | ~r2_hidden(X6,X2) | k1_funct_2(X0,X1) != X2) )),
% 1.57/0.58    inference(cnf_transformation,[],[f68])).
% 1.57/0.58  fof(f123,plain,(
% 1.57/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.57/0.58    inference(equality_resolution,[],[f84])).
% 1.57/0.58  fof(f84,plain,(
% 1.57/0.58    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.57/0.58    inference(cnf_transformation,[],[f53])).
% 1.57/0.58  fof(f53,plain,(
% 1.57/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.57/0.58    inference(flattening,[],[f52])).
% 1.57/0.58  fof(f52,plain,(
% 1.57/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.57/0.58    inference(nnf_transformation,[],[f4])).
% 1.57/0.58  fof(f4,axiom,(
% 1.57/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.57/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.57/0.58  fof(f173,plain,(
% 1.57/0.58    spl12_1),
% 1.57/0.58    inference(avatar_split_clause,[],[f169,f142])).
% 1.57/0.58  fof(f169,plain,(
% 1.57/0.58    v1_funct_1(sK2)),
% 1.57/0.58    inference(forward_demodulation,[],[f155,f156])).
% 1.57/0.58  fof(f155,plain,(
% 1.57/0.58    v1_funct_1(sK9(sK0,sK1,sK2))),
% 1.57/0.58    inference(unit_resulting_resolution,[],[f71,f139])).
% 1.57/0.58  fof(f139,plain,(
% 1.57/0.58    ( ! [X6,X0,X1] : (v1_funct_1(sK9(X0,X1,X6)) | ~r2_hidden(X6,k1_funct_2(X0,X1))) )),
% 1.57/0.58    inference(equality_resolution,[],[f107])).
% 1.57/0.58  fof(f107,plain,(
% 1.57/0.58    ( ! [X6,X2,X0,X1] : (v1_funct_1(sK9(X0,X1,X6)) | ~r2_hidden(X6,X2) | k1_funct_2(X0,X1) != X2) )),
% 1.57/0.58    inference(cnf_transformation,[],[f68])).
% 1.57/0.58  fof(f153,plain,(
% 1.57/0.58    ~spl12_1 | ~spl12_2 | ~spl12_3),
% 1.57/0.58    inference(avatar_split_clause,[],[f72,f150,f146,f142])).
% 1.57/0.58  fof(f72,plain,(
% 1.57/0.58    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.57/0.58    inference(cnf_transformation,[],[f45])).
% 1.57/0.58  % SZS output end Proof for theBenchmark
% 1.57/0.58  % (32741)------------------------------
% 1.57/0.58  % (32741)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.58  % (32741)Termination reason: Refutation
% 1.57/0.58  
% 1.57/0.58  % (32741)Memory used [KB]: 11001
% 1.57/0.58  % (32741)Time elapsed: 0.162 s
% 1.57/0.58  % (32741)------------------------------
% 1.57/0.58  % (32741)------------------------------
% 1.57/0.59  % (32742)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.57/0.59  % (32719)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.57/0.59  % (32744)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.57/0.60  % (32714)Success in time 0.231 s
%------------------------------------------------------------------------------
