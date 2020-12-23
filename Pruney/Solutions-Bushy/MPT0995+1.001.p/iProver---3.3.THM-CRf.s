%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0995+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:36 EST 2020

% Result     : Theorem 1.75s
% Output     : CNFRefutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 201 expanded)
%              Number of clauses        :   48 (  55 expanded)
%              Number of leaves         :   13 (  61 expanded)
%              Depth                    :   19
%              Number of atoms          :  372 (1291 expanded)
%              Number of equality atoms :  163 ( 397 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => ! [X4] :
            ( ? [X5] :
                ( k1_funct_1(X3,X5) = X4
                & r2_hidden(X5,X2)
                & r2_hidden(X5,X0) )
           => r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => ! [X4] :
              ( ? [X5] :
                  ( k1_funct_1(X3,X5) = X4
                  & r2_hidden(X5,X2)
                  & r2_hidden(X5,X0) )
             => r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
          & ? [X5] :
              ( k1_funct_1(X3,X5) = X4
              & r2_hidden(X5,X2)
              & r2_hidden(X5,X0) ) )
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
          & ? [X5] :
              ( k1_funct_1(X3,X5) = X4
              & r2_hidden(X5,X2)
              & r2_hidden(X5,X0) ) )
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f15])).

fof(f26,plain,(
    ! [X4,X2,X0,X3] :
      ( ? [X5] :
          ( k1_funct_1(X3,X5) = X4
          & r2_hidden(X5,X2)
          & r2_hidden(X5,X0) )
     => ( k1_funct_1(X3,sK8) = X4
        & r2_hidden(sK8,X2)
        & r2_hidden(sK8,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
          & ? [X5] :
              ( k1_funct_1(X3,X5) = X4
              & r2_hidden(X5,X2)
              & r2_hidden(X5,X0) ) )
     => ( ~ r2_hidden(sK7,k7_relset_1(X0,X1,X3,X2))
        & ? [X5] :
            ( k1_funct_1(X3,X5) = sK7
            & r2_hidden(X5,X2)
            & r2_hidden(X5,X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
            & ? [X5] :
                ( k1_funct_1(X3,X5) = X4
                & r2_hidden(X5,X2)
                & r2_hidden(X5,X0) ) )
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ~ r2_hidden(X4,k7_relset_1(sK3,sK4,sK6,sK5))
          & ? [X5] :
              ( k1_funct_1(sK6,X5) = X4
              & r2_hidden(X5,sK5)
              & r2_hidden(X5,sK3) ) )
      & k1_xboole_0 != sK4
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK6,sK3,sK4)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ~ r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))
    & k1_funct_1(sK6,sK8) = sK7
    & r2_hidden(sK8,sK5)
    & r2_hidden(sK8,sK3)
    & k1_xboole_0 != sK4
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK6,sK3,sK4)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8])],[f16,f26,f25,f24])).

fof(f46,plain,(
    v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f47,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f27])).

fof(f48,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f51,plain,(
    k1_funct_1(sK6,sK8) = sK7 ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) ) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( k1_funct_1(X0,X5) = X3
                      & r2_hidden(X5,X1)
                      & r2_hidden(X5,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ? [X8] :
                      ( k1_funct_1(X0,X8) = X6
                      & r2_hidden(X8,X1)
                      & r2_hidden(X8,k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f17])).

fof(f21,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1,X6)) = X6
        & r2_hidden(sK2(X0,X1,X6),X1)
        & r2_hidden(sK2(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK1(X0,X1,X2)) = X3
        & r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( k1_funct_1(X0,X4) != X3
                | ~ r2_hidden(X4,X1)
                | ~ r2_hidden(X4,k1_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( k1_funct_1(X0,X5) = X3
                & r2_hidden(X5,X1)
                & r2_hidden(X5,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( k1_funct_1(X0,X4) != sK0(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK0(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( k1_funct_1(X0,X4) != sK0(X0,X1,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                | ~ r2_hidden(sK0(X0,X1,X2),X2) )
              & ( ( k1_funct_1(X0,sK1(X0,X1,X2)) = sK0(X0,X1,X2)
                  & r2_hidden(sK1(X0,X1,X2),X1)
                  & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK2(X0,X1,X6)) = X6
                    & r2_hidden(sK2(X0,X1,X6),X1)
                    & r2_hidden(sK2(X0,X1,X6),k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f21,f20,f19])).

fof(f32,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | k1_funct_1(X0,X7) != X6
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f53,plain,(
    ! [X2,X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f54,plain,(
    ! [X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f45,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f52,plain,(
    ~ r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) ),
    inference(cnf_transformation,[],[f27])).

fof(f50,plain,(
    r2_hidden(sK8,sK5) ),
    inference(cnf_transformation,[],[f27])).

fof(f49,plain,(
    r2_hidden(sK8,sK3) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_276,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | sK6 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_22])).

cnf(c_277,plain,
    ( ~ v1_funct_2(sK6,X0,X1)
    | k1_relset_1(X0,X1,sK6) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_276])).

cnf(c_776,plain,
    ( k1_relset_1(X0,X1,sK6) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | sK6 != sK6
    | sK4 != X1
    | sK3 != X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_277])).

cnf(c_777,plain,
    ( k1_relset_1(sK3,sK4,sK6) = sK3
    | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_776])).

cnf(c_21,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_778,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | k1_relset_1(sK3,sK4,sK6) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_777,c_21])).

cnf(c_779,plain,
    ( k1_relset_1(sK3,sK4,sK6) = sK3
    | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(renaming,[status(thm)],[c_778])).

cnf(c_840,plain,
    ( k1_relset_1(sK3,sK4,sK6) = sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_779])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_267,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_22])).

cnf(c_268,plain,
    ( k1_relset_1(X0,X1,sK6) = k1_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(unflattening,[status(thm)],[c_267])).

cnf(c_1463,plain,
    ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
    inference(equality_resolution,[status(thm)],[c_268])).

cnf(c_1693,plain,
    ( k1_relat_1(sK6) = sK3 ),
    inference(demodulation,[status(thm)],[c_840,c_1463])).

cnf(c_18,negated_conjecture,
    ( k1_funct_1(sK6,sK8) = sK7 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(X2))
    | r2_hidden(k1_funct_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_469,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(X2))
    | r2_hidden(k1_funct_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_relat_1(X2)
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_24])).

cnf(c_470,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(sK6))
    | r2_hidden(k1_funct_1(sK6,X0),k9_relat_1(sK6,X1))
    | ~ v1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_469])).

cnf(c_1294,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),k9_relat_1(sK6,X1)) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_470])).

cnf(c_471,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),k9_relat_1(sK6,X1)) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_470])).

cnf(c_1066,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1430,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) = k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1066])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_312,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_22])).

cnf(c_313,plain,
    ( v1_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(unflattening,[status(thm)],[c_312])).

cnf(c_1433,plain,
    ( v1_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_313])).

cnf(c_1434,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1433])).

cnf(c_1896,plain,
    ( r2_hidden(k1_funct_1(sK6,X0),k9_relat_1(sK6,X1)) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1294,c_471,c_1430,c_1434])).

cnf(c_1897,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),k9_relat_1(sK6,X1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_1896])).

cnf(c_1905,plain,
    ( r2_hidden(sK8,X0) != iProver_top
    | r2_hidden(sK8,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(sK7,k9_relat_1(sK6,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_1897])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_258,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_22])).

cnf(c_259,plain,
    ( k7_relset_1(X0,X1,sK6,X2) = k9_relat_1(sK6,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(unflattening,[status(thm)],[c_258])).

cnf(c_1487,plain,
    ( k7_relset_1(sK3,sK4,sK6,X0) = k9_relat_1(sK6,X0) ),
    inference(equality_resolution,[status(thm)],[c_259])).

cnf(c_17,negated_conjecture,
    ( ~ r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1301,plain,
    ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1628,plain,
    ( r2_hidden(sK7,k9_relat_1(sK6,sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1487,c_1301])).

cnf(c_1980,plain,
    ( r2_hidden(sK8,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(sK8,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1905,c_1628])).

cnf(c_19,negated_conjecture,
    ( r2_hidden(sK8,sK5) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_29,plain,
    ( r2_hidden(sK8,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1996,plain,
    ( r2_hidden(sK8,k1_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1980,c_29])).

cnf(c_2264,plain,
    ( r2_hidden(sK8,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1693,c_1996])).

cnf(c_20,negated_conjecture,
    ( r2_hidden(sK8,sK3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_28,plain,
    ( r2_hidden(sK8,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2264,c_28])).


%------------------------------------------------------------------------------
