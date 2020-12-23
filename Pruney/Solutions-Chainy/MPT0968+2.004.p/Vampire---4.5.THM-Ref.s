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
% DateTime   : Thu Dec  3 13:00:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  110 (3430 expanded)
%              Number of leaves         :   15 ( 861 expanded)
%              Depth                    :   27
%              Number of atoms          :  410 (19275 expanded)
%              Number of equality atoms :  164 (7055 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f701,plain,(
    $false ),
    inference(resolution,[],[f559,f506])).

fof(f506,plain,(
    ~ r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f340,f504])).

fof(f504,plain,(
    k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f503])).

fof(f503,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f69,f263])).

fof(f263,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f254,f70])).

fof(f70,plain,(
    ~ r2_hidden(sK2,k1_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ~ r2_hidden(sK2,k1_funct_2(sK0,sK1))
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f38])).

fof(f38,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X2,k1_funct_2(X0,X1))
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ~ r2_hidden(sK2,k1_funct_2(sK0,sK1))
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X2,k1_funct_2(X0,X1))
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X2,k1_funct_2(X0,X1))
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => r2_hidden(X2,k1_funct_2(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => r2_hidden(X2,k1_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_funct_2)).

fof(f254,plain,
    ( r2_hidden(sK2,k1_funct_2(sK0,sK1))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f195,f237])).

fof(f237,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f236,f68])).

fof(f68,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f39])).

fof(f236,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f234,f67])).

fof(f67,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f234,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f166,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f166,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f68,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f195,plain,(
    r2_hidden(sK2,k1_funct_2(k1_relat_1(sK2),sK1)) ),
    inference(subsumption_resolution,[],[f194,f167])).

fof(f167,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f68,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f194,plain,
    ( r2_hidden(sK2,k1_funct_2(k1_relat_1(sK2),sK1))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f188,f66])).

fof(f66,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f188,plain,
    ( r2_hidden(sK2,k1_funct_2(k1_relat_1(sK2),sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f187,f145])).

fof(f145,plain,(
    ! [X7,X1] :
      ( r2_hidden(X7,k1_funct_2(k1_relat_1(X7),X1))
      | ~ r1_tarski(k2_relat_1(X7),X1)
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7) ) ),
    inference(equality_resolution,[],[f144])).

fof(f144,plain,(
    ! [X2,X7,X1] :
      ( r2_hidden(X7,X2)
      | ~ r1_tarski(k2_relat_1(X7),X1)
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7)
      | k1_funct_2(k1_relat_1(X7),X1) != X2 ) ),
    inference(equality_resolution,[],[f143])).

fof(f143,plain,(
    ! [X6,X2,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r1_tarski(k2_relat_1(X7),X1)
      | X6 != X7
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7)
      | k1_funct_2(k1_relat_1(X7),X1) != X2 ) ),
    inference(equality_resolution,[],[f122])).

fof(f122,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r1_tarski(k2_relat_1(X7),X1)
      | k1_relat_1(X7) != X0
      | X6 != X7
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f61,f64,f63,f62])).

fof(f62,plain,(
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

fof(f63,plain,(
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

fof(f64,plain,(
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

fof(f61,plain,(
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
    inference(rectify,[],[f60])).

fof(f60,plain,(
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

fof(f187,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(resolution,[],[f170,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f170,plain,(
    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    inference(backward_demodulation,[],[f164,f165])).

fof(f165,plain,(
    k2_relat_1(sK2) = k2_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f68,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f164,plain,(
    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f68,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f69,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f39])).

fof(f340,plain,(
    ~ r2_hidden(k1_xboole_0,k1_funct_2(sK0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f266,f318])).

fof(f318,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f317,f71])).

fof(f71,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f317,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f316,f131])).

fof(f131,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f316,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK2)
    | k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f315,f263])).

fof(f315,plain,
    ( k1_xboole_0 = sK2
    | ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) ),
    inference(forward_demodulation,[],[f282,f131])).

fof(f282,plain,
    ( sK2 = k2_zfmisc_1(sK0,k1_xboole_0)
    | ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) ),
    inference(backward_demodulation,[],[f185,f263])).

fof(f185,plain,
    ( sK2 = k2_zfmisc_1(sK0,sK1)
    | ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) ),
    inference(resolution,[],[f169,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f169,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f68,f89])).

fof(f266,plain,(
    ~ r2_hidden(sK2,k1_funct_2(sK0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f70,f263])).

fof(f559,plain,(
    ! [X0] : r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,X0)) ),
    inference(backward_demodulation,[],[f406,f551])).

fof(f551,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f550,f348])).

fof(f348,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f307,f318])).

fof(f307,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f265,f131])).

fof(f265,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f68,f263])).

fof(f550,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f549,f131])).

fof(f549,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f535,f508])).

fof(f508,plain,(
    k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f343,f504])).

fof(f343,plain,(
    k1_relat_1(k1_xboole_0) = k1_relset_1(sK0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f275,f318])).

fof(f275,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f166,f263])).

fof(f535,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(resolution,[],[f505,f141])).

fof(f141,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f505,plain,(
    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f339,f504])).

fof(f339,plain,(
    v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f264,f318])).

fof(f264,plain,(
    v1_funct_2(sK2,sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f67,f263])).

fof(f406,plain,(
    ! [X0] : r2_hidden(k1_xboole_0,k1_funct_2(k1_relat_1(k1_xboole_0),X0)) ),
    inference(subsumption_resolution,[],[f405,f324])).

fof(f324,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f167,f318])).

fof(f405,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,k1_funct_2(k1_relat_1(k1_xboole_0),X0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f392,f71])).

fof(f392,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | r2_hidden(k1_xboole_0,k1_funct_2(k1_relat_1(k1_xboole_0),X0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(backward_demodulation,[],[f357,f387])).

fof(f387,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f386,f71])).

fof(f386,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(k1_xboole_0))
    | k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f385,f263])).

fof(f385,plain,
    ( ~ r1_tarski(sK1,k2_relat_1(k1_xboole_0))
    | k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f384,f318])).

fof(f384,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ r1_tarski(sK1,k2_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f285,f318])).

fof(f285,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ r1_tarski(sK1,k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f192,f263])).

fof(f192,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ r1_tarski(sK1,k2_relat_1(sK2)) ),
    inference(resolution,[],[f187,f85])).

fof(f357,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(k1_xboole_0),X0)
      | r2_hidden(k1_xboole_0,k1_funct_2(k1_relat_1(k1_xboole_0),X0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f356,f318])).

fof(f356,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,k1_funct_2(k1_relat_1(k1_xboole_0),X0))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k2_relat_1(sK2),X0) ) ),
    inference(forward_demodulation,[],[f320,f318])).

fof(f320,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k1_xboole_0)
      | r2_hidden(sK2,k1_funct_2(k1_relat_1(sK2),X0))
      | ~ r1_tarski(k2_relat_1(sK2),X0) ) ),
    inference(backward_demodulation,[],[f151,f318])).

fof(f151,plain,(
    ! [X0] :
      ( r2_hidden(sK2,k1_funct_2(k1_relat_1(sK2),X0))
      | ~ r1_tarski(k2_relat_1(sK2),X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f66,f145])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:54:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (13628)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.48  % (13645)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.48  % (13636)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.51  % (13618)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (13617)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (13622)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (13637)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (13634)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (13629)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (13615)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (13616)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (13620)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (13619)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (13633)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (13623)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (13638)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (13631)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (13621)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (13643)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (13637)Refutation not found, incomplete strategy% (13637)------------------------------
% 0.21/0.54  % (13637)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (13637)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (13637)Memory used [KB]: 10874
% 0.21/0.54  % (13637)Time elapsed: 0.076 s
% 0.21/0.54  % (13637)------------------------------
% 0.21/0.54  % (13637)------------------------------
% 0.21/0.54  % (13644)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (13639)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (13641)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (13625)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (13632)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (13617)Refutation not found, incomplete strategy% (13617)------------------------------
% 0.21/0.54  % (13617)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (13617)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (13617)Memory used [KB]: 11001
% 0.21/0.54  % (13617)Time elapsed: 0.139 s
% 0.21/0.54  % (13617)------------------------------
% 0.21/0.54  % (13617)------------------------------
% 0.21/0.54  % (13626)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (13630)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (13624)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (13627)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (13635)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (13642)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.56  % (13638)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.58  % SZS output start Proof for theBenchmark
% 0.21/0.58  fof(f701,plain,(
% 0.21/0.58    $false),
% 0.21/0.58    inference(resolution,[],[f559,f506])).
% 0.21/0.58  fof(f506,plain,(
% 0.21/0.58    ~r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,k1_xboole_0))),
% 0.21/0.58    inference(backward_demodulation,[],[f340,f504])).
% 0.21/0.58  fof(f504,plain,(
% 0.21/0.58    k1_xboole_0 = sK0),
% 0.21/0.58    inference(trivial_inequality_removal,[],[f503])).
% 0.21/0.58  fof(f503,plain,(
% 0.21/0.58    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0),
% 0.21/0.58    inference(superposition,[],[f69,f263])).
% 0.21/0.58  fof(f263,plain,(
% 0.21/0.58    k1_xboole_0 = sK1),
% 0.21/0.58    inference(subsumption_resolution,[],[f254,f70])).
% 0.21/0.58  fof(f70,plain,(
% 0.21/0.58    ~r2_hidden(sK2,k1_funct_2(sK0,sK1))),
% 0.21/0.58    inference(cnf_transformation,[],[f39])).
% 0.21/0.58  fof(f39,plain,(
% 0.21/0.58    ~r2_hidden(sK2,k1_funct_2(sK0,sK1)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.21/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f38])).
% 0.21/0.58  fof(f38,plain,(
% 0.21/0.58    ? [X0,X1,X2] : (~r2_hidden(X2,k1_funct_2(X0,X1)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (~r2_hidden(sK2,k1_funct_2(sK0,sK1)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f23,plain,(
% 0.21/0.58    ? [X0,X1,X2] : (~r2_hidden(X2,k1_funct_2(X0,X1)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.58    inference(flattening,[],[f22])).
% 0.21/0.58  fof(f22,plain,(
% 0.21/0.58    ? [X0,X1,X2] : ((~r2_hidden(X2,k1_funct_2(X0,X1)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.58    inference(ennf_transformation,[],[f21])).
% 0.21/0.58  fof(f21,negated_conjecture,(
% 0.21/0.58    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => r2_hidden(X2,k1_funct_2(X0,X1))))),
% 0.21/0.58    inference(negated_conjecture,[],[f20])).
% 0.21/0.58  fof(f20,conjecture,(
% 0.21/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => r2_hidden(X2,k1_funct_2(X0,X1))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_funct_2)).
% 0.21/0.58  fof(f254,plain,(
% 0.21/0.58    r2_hidden(sK2,k1_funct_2(sK0,sK1)) | k1_xboole_0 = sK1),
% 0.21/0.58    inference(superposition,[],[f195,f237])).
% 0.21/0.58  fof(f237,plain,(
% 0.21/0.58    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1),
% 0.21/0.58    inference(subsumption_resolution,[],[f236,f68])).
% 0.21/0.58  fof(f68,plain,(
% 0.21/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.58    inference(cnf_transformation,[],[f39])).
% 0.21/0.58  fof(f236,plain,(
% 0.21/0.58    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.58    inference(subsumption_resolution,[],[f234,f67])).
% 0.21/0.58  fof(f67,plain,(
% 0.21/0.58    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.58    inference(cnf_transformation,[],[f39])).
% 0.21/0.58  fof(f234,plain,(
% 0.21/0.58    sK0 = k1_relat_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.58    inference(superposition,[],[f166,f111])).
% 0.21/0.58  fof(f111,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f59])).
% 0.21/0.58  fof(f59,plain,(
% 0.21/0.58    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.58    inference(nnf_transformation,[],[f37])).
% 0.21/0.58  fof(f37,plain,(
% 0.21/0.58    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.58    inference(flattening,[],[f36])).
% 0.21/0.58  fof(f36,plain,(
% 0.21/0.58    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.58    inference(ennf_transformation,[],[f16])).
% 0.21/0.58  fof(f16,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.58  fof(f166,plain,(
% 0.21/0.58    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.58    inference(resolution,[],[f68,f108])).
% 0.21/0.58  fof(f108,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f33])).
% 0.21/0.58  fof(f33,plain,(
% 0.21/0.58    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.58    inference(ennf_transformation,[],[f14])).
% 0.21/0.58  fof(f14,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.58  fof(f195,plain,(
% 0.21/0.58    r2_hidden(sK2,k1_funct_2(k1_relat_1(sK2),sK1))),
% 0.21/0.58    inference(subsumption_resolution,[],[f194,f167])).
% 0.21/0.58  fof(f167,plain,(
% 0.21/0.58    v1_relat_1(sK2)),
% 0.21/0.58    inference(resolution,[],[f68,f107])).
% 0.21/0.58  fof(f107,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f32])).
% 0.21/0.58  fof(f32,plain,(
% 0.21/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.58    inference(ennf_transformation,[],[f11])).
% 0.21/0.58  fof(f11,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.58  fof(f194,plain,(
% 0.21/0.58    r2_hidden(sK2,k1_funct_2(k1_relat_1(sK2),sK1)) | ~v1_relat_1(sK2)),
% 0.21/0.58    inference(subsumption_resolution,[],[f188,f66])).
% 0.21/0.58  fof(f66,plain,(
% 0.21/0.58    v1_funct_1(sK2)),
% 0.21/0.58    inference(cnf_transformation,[],[f39])).
% 0.21/0.58  fof(f188,plain,(
% 0.21/0.58    r2_hidden(sK2,k1_funct_2(k1_relat_1(sK2),sK1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.21/0.58    inference(resolution,[],[f187,f145])).
% 0.21/0.58  fof(f145,plain,(
% 0.21/0.58    ( ! [X7,X1] : (r2_hidden(X7,k1_funct_2(k1_relat_1(X7),X1)) | ~r1_tarski(k2_relat_1(X7),X1) | ~v1_funct_1(X7) | ~v1_relat_1(X7)) )),
% 0.21/0.58    inference(equality_resolution,[],[f144])).
% 0.21/0.58  fof(f144,plain,(
% 0.21/0.58    ( ! [X2,X7,X1] : (r2_hidden(X7,X2) | ~r1_tarski(k2_relat_1(X7),X1) | ~v1_funct_1(X7) | ~v1_relat_1(X7) | k1_funct_2(k1_relat_1(X7),X1) != X2) )),
% 0.21/0.58    inference(equality_resolution,[],[f143])).
% 0.21/0.58  fof(f143,plain,(
% 0.21/0.58    ( ! [X6,X2,X7,X1] : (r2_hidden(X6,X2) | ~r1_tarski(k2_relat_1(X7),X1) | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7) | k1_funct_2(k1_relat_1(X7),X1) != X2) )),
% 0.21/0.58    inference(equality_resolution,[],[f122])).
% 0.21/0.58  fof(f122,plain,(
% 0.21/0.58    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | ~r1_tarski(k2_relat_1(X7),X1) | k1_relat_1(X7) != X0 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7) | k1_funct_2(X0,X1) != X2) )),
% 0.21/0.58    inference(cnf_transformation,[],[f65])).
% 0.21/0.58  fof(f65,plain,(
% 0.21/0.58    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | sK7(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK7(X0,X1,X2),X2)) & ((r1_tarski(k2_relat_1(sK8(X0,X1,X2)),X1) & k1_relat_1(sK8(X0,X1,X2)) = X0 & sK7(X0,X1,X2) = sK8(X0,X1,X2) & v1_funct_1(sK8(X0,X1,X2)) & v1_relat_1(sK8(X0,X1,X2))) | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X1) | k1_relat_1(X7) != X0 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & ((r1_tarski(k2_relat_1(sK9(X0,X1,X6)),X1) & k1_relat_1(sK9(X0,X1,X6)) = X0 & sK9(X0,X1,X6) = X6 & v1_funct_1(sK9(X0,X1,X6)) & v1_relat_1(sK9(X0,X1,X6))) | ~r2_hidden(X6,X2))) | k1_funct_2(X0,X1) != X2))),
% 0.21/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f61,f64,f63,f62])).
% 0.21/0.58  fof(f62,plain,(
% 0.21/0.58    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X1) & k1_relat_1(X5) = X0 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2))) => ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | sK7(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X1) & k1_relat_1(X5) = X0 & sK7(X0,X1,X2) = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(sK7(X0,X1,X2),X2))))),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f63,plain,(
% 0.21/0.58    ! [X2,X1,X0] : (? [X5] : (r1_tarski(k2_relat_1(X5),X1) & k1_relat_1(X5) = X0 & sK7(X0,X1,X2) = X5 & v1_funct_1(X5) & v1_relat_1(X5)) => (r1_tarski(k2_relat_1(sK8(X0,X1,X2)),X1) & k1_relat_1(sK8(X0,X1,X2)) = X0 & sK7(X0,X1,X2) = sK8(X0,X1,X2) & v1_funct_1(sK8(X0,X1,X2)) & v1_relat_1(sK8(X0,X1,X2))))),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f64,plain,(
% 0.21/0.58    ! [X6,X1,X0] : (? [X8] : (r1_tarski(k2_relat_1(X8),X1) & k1_relat_1(X8) = X0 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) => (r1_tarski(k2_relat_1(sK9(X0,X1,X6)),X1) & k1_relat_1(sK9(X0,X1,X6)) = X0 & sK9(X0,X1,X6) = X6 & v1_funct_1(sK9(X0,X1,X6)) & v1_relat_1(sK9(X0,X1,X6))))),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f61,plain,(
% 0.21/0.58    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X1) & k1_relat_1(X5) = X0 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X1) | k1_relat_1(X7) != X0 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & (? [X8] : (r1_tarski(k2_relat_1(X8),X1) & k1_relat_1(X8) = X0 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) | ~r2_hidden(X6,X2))) | k1_funct_2(X0,X1) != X2))),
% 0.21/0.58    inference(rectify,[],[f60])).
% 0.21/0.58  fof(f60,plain,(
% 0.21/0.58    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4))) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | ~r2_hidden(X3,X2))) | k1_funct_2(X0,X1) != X2))),
% 0.21/0.58    inference(nnf_transformation,[],[f17])).
% 0.21/0.58  fof(f17,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_funct_2)).
% 0.21/0.58  fof(f187,plain,(
% 0.21/0.58    r1_tarski(k2_relat_1(sK2),sK1)),
% 0.21/0.58    inference(resolution,[],[f170,f89])).
% 0.21/0.58  fof(f89,plain,(
% 0.21/0.58    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f52])).
% 0.21/0.58  fof(f52,plain,(
% 0.21/0.58    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.58    inference(nnf_transformation,[],[f6])).
% 0.21/0.58  fof(f6,axiom,(
% 0.21/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.58  fof(f170,plain,(
% 0.21/0.58    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))),
% 0.21/0.58    inference(backward_demodulation,[],[f164,f165])).
% 0.21/0.58  fof(f165,plain,(
% 0.21/0.58    k2_relat_1(sK2) = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.58    inference(resolution,[],[f68,f109])).
% 0.21/0.58  fof(f109,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f34])).
% 0.21/0.58  fof(f34,plain,(
% 0.21/0.58    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.58    inference(ennf_transformation,[],[f15])).
% 0.21/0.58  fof(f15,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.58  fof(f164,plain,(
% 0.21/0.58    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))),
% 0.21/0.58    inference(resolution,[],[f68,f110])).
% 0.21/0.58  fof(f110,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f35])).
% 0.21/0.58  fof(f35,plain,(
% 0.21/0.58    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.58    inference(ennf_transformation,[],[f13])).
% 0.21/0.58  fof(f13,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.21/0.58  fof(f69,plain,(
% 0.21/0.58    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 0.21/0.58    inference(cnf_transformation,[],[f39])).
% 0.21/0.58  fof(f340,plain,(
% 0.21/0.58    ~r2_hidden(k1_xboole_0,k1_funct_2(sK0,k1_xboole_0))),
% 0.21/0.58    inference(backward_demodulation,[],[f266,f318])).
% 0.21/0.58  fof(f318,plain,(
% 0.21/0.58    k1_xboole_0 = sK2),
% 0.21/0.58    inference(subsumption_resolution,[],[f317,f71])).
% 0.21/0.58  fof(f71,plain,(
% 0.21/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f4])).
% 0.21/0.59  fof(f4,axiom,(
% 0.21/0.59    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.59  fof(f317,plain,(
% 0.21/0.59    ~r1_tarski(k1_xboole_0,sK2) | k1_xboole_0 = sK2),
% 0.21/0.59    inference(forward_demodulation,[],[f316,f131])).
% 0.21/0.59  fof(f131,plain,(
% 0.21/0.59    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.59    inference(equality_resolution,[],[f93])).
% 0.21/0.59  fof(f93,plain,(
% 0.21/0.59    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.21/0.59    inference(cnf_transformation,[],[f54])).
% 0.21/0.59  fof(f54,plain,(
% 0.21/0.59    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.59    inference(flattening,[],[f53])).
% 0.21/0.59  fof(f53,plain,(
% 0.21/0.59    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.59    inference(nnf_transformation,[],[f5])).
% 0.21/0.59  fof(f5,axiom,(
% 0.21/0.59    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.59  fof(f316,plain,(
% 0.21/0.59    ~r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK2) | k1_xboole_0 = sK2),
% 0.21/0.59    inference(forward_demodulation,[],[f315,f263])).
% 0.21/0.59  fof(f315,plain,(
% 0.21/0.59    k1_xboole_0 = sK2 | ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK2)),
% 0.21/0.59    inference(forward_demodulation,[],[f282,f131])).
% 0.21/0.59  fof(f282,plain,(
% 0.21/0.59    sK2 = k2_zfmisc_1(sK0,k1_xboole_0) | ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK2)),
% 0.21/0.59    inference(backward_demodulation,[],[f185,f263])).
% 0.21/0.59  fof(f185,plain,(
% 0.21/0.59    sK2 = k2_zfmisc_1(sK0,sK1) | ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK2)),
% 0.21/0.59    inference(resolution,[],[f169,f85])).
% 0.21/0.59  fof(f85,plain,(
% 0.21/0.59    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f47])).
% 0.21/0.59  fof(f47,plain,(
% 0.21/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.59    inference(flattening,[],[f46])).
% 0.21/0.59  fof(f46,plain,(
% 0.21/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.59    inference(nnf_transformation,[],[f3])).
% 0.21/0.59  fof(f3,axiom,(
% 0.21/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.59  fof(f169,plain,(
% 0.21/0.59    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.21/0.59    inference(resolution,[],[f68,f89])).
% 0.21/0.59  fof(f266,plain,(
% 0.21/0.59    ~r2_hidden(sK2,k1_funct_2(sK0,k1_xboole_0))),
% 0.21/0.59    inference(backward_demodulation,[],[f70,f263])).
% 0.21/0.59  fof(f559,plain,(
% 0.21/0.59    ( ! [X0] : (r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,X0))) )),
% 0.21/0.59    inference(backward_demodulation,[],[f406,f551])).
% 0.21/0.59  fof(f551,plain,(
% 0.21/0.59    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.59    inference(subsumption_resolution,[],[f550,f348])).
% 0.21/0.59  fof(f348,plain,(
% 0.21/0.59    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.59    inference(backward_demodulation,[],[f307,f318])).
% 0.21/0.59  fof(f307,plain,(
% 0.21/0.59    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.59    inference(forward_demodulation,[],[f265,f131])).
% 0.21/0.59  fof(f265,plain,(
% 0.21/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.21/0.59    inference(backward_demodulation,[],[f68,f263])).
% 0.21/0.59  fof(f550,plain,(
% 0.21/0.59    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.59    inference(forward_demodulation,[],[f549,f131])).
% 0.21/0.59  fof(f549,plain,(
% 0.21/0.59    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.21/0.59    inference(forward_demodulation,[],[f535,f508])).
% 0.21/0.59  fof(f508,plain,(
% 0.21/0.59    k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.21/0.59    inference(backward_demodulation,[],[f343,f504])).
% 0.21/0.59  fof(f343,plain,(
% 0.21/0.59    k1_relat_1(k1_xboole_0) = k1_relset_1(sK0,k1_xboole_0,k1_xboole_0)),
% 0.21/0.59    inference(backward_demodulation,[],[f275,f318])).
% 0.21/0.59  fof(f275,plain,(
% 0.21/0.59    k1_relat_1(sK2) = k1_relset_1(sK0,k1_xboole_0,sK2)),
% 0.21/0.59    inference(backward_demodulation,[],[f166,f263])).
% 0.21/0.59  fof(f535,plain,(
% 0.21/0.59    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.21/0.59    inference(resolution,[],[f505,f141])).
% 0.21/0.59  fof(f141,plain,(
% 0.21/0.59    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.21/0.59    inference(equality_resolution,[],[f112])).
% 0.21/0.59  fof(f112,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.59    inference(cnf_transformation,[],[f59])).
% 0.21/0.59  fof(f505,plain,(
% 0.21/0.59    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.21/0.59    inference(backward_demodulation,[],[f339,f504])).
% 0.21/0.59  fof(f339,plain,(
% 0.21/0.59    v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)),
% 0.21/0.59    inference(backward_demodulation,[],[f264,f318])).
% 0.21/0.59  fof(f264,plain,(
% 0.21/0.59    v1_funct_2(sK2,sK0,k1_xboole_0)),
% 0.21/0.59    inference(backward_demodulation,[],[f67,f263])).
% 0.21/0.59  fof(f406,plain,(
% 0.21/0.59    ( ! [X0] : (r2_hidden(k1_xboole_0,k1_funct_2(k1_relat_1(k1_xboole_0),X0))) )),
% 0.21/0.59    inference(subsumption_resolution,[],[f405,f324])).
% 0.21/0.59  fof(f324,plain,(
% 0.21/0.59    v1_relat_1(k1_xboole_0)),
% 0.21/0.59    inference(backward_demodulation,[],[f167,f318])).
% 0.21/0.59  fof(f405,plain,(
% 0.21/0.59    ( ! [X0] : (r2_hidden(k1_xboole_0,k1_funct_2(k1_relat_1(k1_xboole_0),X0)) | ~v1_relat_1(k1_xboole_0)) )),
% 0.21/0.59    inference(subsumption_resolution,[],[f392,f71])).
% 0.21/0.59  fof(f392,plain,(
% 0.21/0.59    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | r2_hidden(k1_xboole_0,k1_funct_2(k1_relat_1(k1_xboole_0),X0)) | ~v1_relat_1(k1_xboole_0)) )),
% 0.21/0.59    inference(backward_demodulation,[],[f357,f387])).
% 0.21/0.59  fof(f387,plain,(
% 0.21/0.59    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.59    inference(subsumption_resolution,[],[f386,f71])).
% 0.21/0.59  fof(f386,plain,(
% 0.21/0.59    ~r1_tarski(k1_xboole_0,k2_relat_1(k1_xboole_0)) | k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.59    inference(forward_demodulation,[],[f385,f263])).
% 0.21/0.59  fof(f385,plain,(
% 0.21/0.59    ~r1_tarski(sK1,k2_relat_1(k1_xboole_0)) | k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.59    inference(forward_demodulation,[],[f384,f318])).
% 0.21/0.59  fof(f384,plain,(
% 0.21/0.59    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~r1_tarski(sK1,k2_relat_1(sK2))),
% 0.21/0.59    inference(forward_demodulation,[],[f285,f318])).
% 0.21/0.59  fof(f285,plain,(
% 0.21/0.59    k1_xboole_0 = k2_relat_1(sK2) | ~r1_tarski(sK1,k2_relat_1(sK2))),
% 0.21/0.59    inference(backward_demodulation,[],[f192,f263])).
% 0.21/0.59  fof(f192,plain,(
% 0.21/0.59    sK1 = k2_relat_1(sK2) | ~r1_tarski(sK1,k2_relat_1(sK2))),
% 0.21/0.59    inference(resolution,[],[f187,f85])).
% 0.21/0.59  fof(f357,plain,(
% 0.21/0.59    ( ! [X0] : (~r1_tarski(k2_relat_1(k1_xboole_0),X0) | r2_hidden(k1_xboole_0,k1_funct_2(k1_relat_1(k1_xboole_0),X0)) | ~v1_relat_1(k1_xboole_0)) )),
% 0.21/0.59    inference(forward_demodulation,[],[f356,f318])).
% 0.21/0.59  fof(f356,plain,(
% 0.21/0.59    ( ! [X0] : (r2_hidden(k1_xboole_0,k1_funct_2(k1_relat_1(k1_xboole_0),X0)) | ~v1_relat_1(k1_xboole_0) | ~r1_tarski(k2_relat_1(sK2),X0)) )),
% 0.21/0.59    inference(forward_demodulation,[],[f320,f318])).
% 0.21/0.59  fof(f320,plain,(
% 0.21/0.59    ( ! [X0] : (~v1_relat_1(k1_xboole_0) | r2_hidden(sK2,k1_funct_2(k1_relat_1(sK2),X0)) | ~r1_tarski(k2_relat_1(sK2),X0)) )),
% 0.21/0.59    inference(backward_demodulation,[],[f151,f318])).
% 0.21/0.59  fof(f151,plain,(
% 0.21/0.59    ( ! [X0] : (r2_hidden(sK2,k1_funct_2(k1_relat_1(sK2),X0)) | ~r1_tarski(k2_relat_1(sK2),X0) | ~v1_relat_1(sK2)) )),
% 0.21/0.59    inference(resolution,[],[f66,f145])).
% 0.21/0.59  % SZS output end Proof for theBenchmark
% 0.21/0.59  % (13638)------------------------------
% 0.21/0.59  % (13638)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (13638)Termination reason: Refutation
% 0.21/0.59  
% 0.21/0.59  % (13638)Memory used [KB]: 2046
% 0.21/0.59  % (13638)Time elapsed: 0.171 s
% 0.21/0.59  % (13638)------------------------------
% 0.21/0.59  % (13638)------------------------------
% 0.21/0.59  % (13609)Success in time 0.227 s
%------------------------------------------------------------------------------
