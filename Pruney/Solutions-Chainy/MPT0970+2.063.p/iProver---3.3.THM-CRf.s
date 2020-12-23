%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:58 EST 2020

% Result     : Theorem 3.98s
% Output     : CNFRefutation 3.98s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 505 expanded)
%              Number of clauses        :   68 ( 140 expanded)
%              Number of leaves         :   25 ( 138 expanded)
%              Depth                    :   16
%              Number of atoms          :  540 (2511 expanded)
%              Number of equality atoms :  225 ( 826 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( ! [X4] :
                  ~ ( k1_funct_1(X2,X4) = X3
                    & r2_hidden(X4,X0) )
              & r2_hidden(X3,X1) )
       => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( ! [X4] :
                    ~ ( k1_funct_1(X2,X4) = X3
                      & r2_hidden(X4,X0) )
                & r2_hidden(X3,X1) )
         => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f49,plain,(
    ! [X2,X0,X3] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) = X3
          & r2_hidden(X4,X0) )
     => ( k1_funct_1(X2,sK12(X3)) = X3
        & r2_hidden(sK12(X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X0,X1,X2] :
        ( k2_relset_1(X0,X1,X2) != X1
        & ! [X3] :
            ( ? [X4] :
                ( k1_funct_1(X2,X4) = X3
                & r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X1) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( k2_relset_1(sK9,sK10,sK11) != sK10
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(sK11,X4) = X3
              & r2_hidden(X4,sK9) )
          | ~ r2_hidden(X3,sK10) )
      & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))
      & v1_funct_2(sK11,sK9,sK10)
      & v1_funct_1(sK11) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( k2_relset_1(sK9,sK10,sK11) != sK10
    & ! [X3] :
        ( ( k1_funct_1(sK11,sK12(X3)) = X3
          & r2_hidden(sK12(X3),sK9) )
        | ~ r2_hidden(X3,sK10) )
    & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))
    & v1_funct_2(sK11,sK9,sK10)
    & v1_funct_1(sK11) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11,sK12])],[f26,f49,f48])).

fof(f82,plain,(
    m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) ),
    inference(cnf_transformation,[],[f50])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f29])).

fof(f33,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK2(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK1(X0,X1)),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK3(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f30,f33,f32,f31])).

fof(f54,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f87,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK3(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
              & r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
              | ~ r2_hidden(X3,X1) )
          | k2_relset_1(X0,X1,X2) != X1 )
        & ( k2_relset_1(X0,X1,X2) = X1
          | ? [X3] :
              ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
              & r2_hidden(X3,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
              | ~ r2_hidden(X3,X1) )
          | k2_relset_1(X0,X1,X2) != X1 )
        & ( k2_relset_1(X0,X1,X2) = X1
          | ? [X5] :
              ( ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X2)
              & r2_hidden(X5,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(rectify,[],[f42])).

fof(f45,plain,(
    ! [X2,X1] :
      ( ? [X5] :
          ( ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X2)
          & r2_hidden(X5,X1) )
     => ( ! [X6] : ~ r2_hidden(k4_tarski(X6,sK8(X1,X2)),X2)
        & r2_hidden(sK8(X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X3,X2] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
     => r2_hidden(k4_tarski(sK7(X2,X3),X3),X2) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( r2_hidden(k4_tarski(sK7(X2,X3),X3),X2)
              | ~ r2_hidden(X3,X1) )
          | k2_relset_1(X0,X1,X2) != X1 )
        & ( k2_relset_1(X0,X1,X2) = X1
          | ( ! [X6] : ~ r2_hidden(k4_tarski(X6,sK8(X1,X2)),X2)
            & r2_hidden(sK8(X1,X2),X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f43,f45,f44])).

fof(f72,plain,(
    ! [X6,X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_hidden(k4_tarski(X6,sK8(X1,X2)),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( ( k1_funct_1(X0,X1) = X2
                | k1_xboole_0 != X2 )
              & ( k1_xboole_0 = X2
                | k1_funct_1(X0,X1) != X2 ) )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( ( k1_funct_1(X0,X1) = X2
                | ~ r2_hidden(k4_tarski(X1,X2),X0) )
              & ( r2_hidden(k4_tarski(X1,X2),X0)
                | k1_funct_1(X0,X1) != X2 ) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | k1_funct_1(X0,X1) != X2
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,X1) = k1_xboole_0
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | r2_hidden(sK8(X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f85,plain,(
    k2_relset_1(sK9,sK10,sK11) != sK10 ),
    inference(cnf_transformation,[],[f50])).

fof(f84,plain,(
    ! [X3] :
      ( k1_funct_1(sK11,sK12(X3)) = X3
      | ~ r2_hidden(X3,sK10) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f36])).

fof(f40,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK6(X0,X5)) = X5
        & r2_hidden(sK6(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK5(X0,X1)) = X2
        & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK4(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK4(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK4(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK4(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK5(X0,X1)) = sK4(X0,X1)
                  & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK4(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK6(X0,X5)) = X5
                    & r2_hidden(sK6(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f37,f40,f39,f38])).

fof(f65,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f91,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f92,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f91])).

fof(f80,plain,(
    v1_funct_1(sK11) ),
    inference(cnf_transformation,[],[f50])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f27])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f83,plain,(
    ! [X3] :
      ( r2_hidden(sK12(X3),sK9)
      | ~ r2_hidden(X3,sK10) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f10,axiom,(
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

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f81,plain,(
    v1_funct_2(sK11,sK9,sK10) ),
    inference(cnf_transformation,[],[f50])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1004,plain,
    ( m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK3(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1028,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(sK3(X1,X0),X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(k4_tarski(X3,sK8(X2,X0)),X0)
    | k2_relset_1(X1,X2,X0) = X2 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1014,plain,
    ( k2_relset_1(X0,X1,X2) = X1
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(k4_tarski(X3,sK8(X1,X2)),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4761,plain,
    ( k2_relset_1(X0,X1,X2) = X1
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(sK8(X1,X2),k2_relat_1(X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1028,c_1014])).

cnf(c_13311,plain,
    ( k2_relset_1(sK9,sK10,sK11) = sK10
    | r2_hidden(sK8(sK10,sK11),k2_relat_1(sK11)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1004,c_4761])).

cnf(c_9,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1026,plain,
    ( k1_funct_1(X0,X1) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(sK8(X2,X0),X2)
    | k2_relset_1(X1,X2,X0) = X2 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1013,plain,
    ( k2_relset_1(X0,X1,X2) = X1
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(sK8(X1,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3527,plain,
    ( k2_relset_1(sK9,sK10,sK11) = sK10
    | r2_hidden(sK8(sK10,sK11),sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_1004,c_1013])).

cnf(c_37,plain,
    ( m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_29,negated_conjecture,
    ( k2_relset_1(sK9,sK10,sK11) != sK10 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1403,plain,
    ( ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))
    | r2_hidden(sK8(sK10,sK11),sK10)
    | k2_relset_1(sK9,sK10,sK11) = sK10 ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1404,plain,
    ( k2_relset_1(sK9,sK10,sK11) = sK10
    | m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) != iProver_top
    | r2_hidden(sK8(sK10,sK11),sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1403])).

cnf(c_3845,plain,
    ( r2_hidden(sK8(sK10,sK11),sK10) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3527,c_37,c_29,c_1404])).

cnf(c_30,negated_conjecture,
    ( ~ r2_hidden(X0,sK10)
    | k1_funct_1(sK11,sK12(X0)) = X0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1006,plain,
    ( k1_funct_1(sK11,sK12(X0)) = X0
    | r2_hidden(X0,sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3851,plain,
    ( k1_funct_1(sK11,sK12(sK8(sK10,sK11))) = sK8(sK10,sK11) ),
    inference(superposition,[status(thm)],[c_3845,c_1006])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1020,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5195,plain,
    ( r2_hidden(sK8(sK10,sK11),k2_relat_1(sK11)) = iProver_top
    | r2_hidden(sK12(sK8(sK10,sK11)),k1_relat_1(sK11)) != iProver_top
    | v1_funct_1(sK11) != iProver_top
    | v1_relat_1(sK11) != iProver_top ),
    inference(superposition,[status(thm)],[c_3851,c_1020])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK11) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_35,plain,
    ( v1_funct_1(sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1439,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK9,sK10))
    | v1_relat_1(sK11) ),
    inference(resolution,[status(thm)],[c_2,c_32])).

cnf(c_1440,plain,
    ( v1_relat_1(k2_zfmisc_1(sK9,sK10)) != iProver_top
    | v1_relat_1(sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1439])).

cnf(c_7,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1719,plain,
    ( v1_relat_1(k2_zfmisc_1(sK9,sK10)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1720,plain,
    ( v1_relat_1(k2_zfmisc_1(sK9,sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1719])).

cnf(c_5489,plain,
    ( r2_hidden(sK8(sK10,sK11),k2_relat_1(sK11)) = iProver_top
    | r2_hidden(sK12(sK8(sK10,sK11)),k1_relat_1(sK11)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5195,c_35,c_1440,c_1720])).

cnf(c_5495,plain,
    ( k1_funct_1(sK11,sK12(sK8(sK10,sK11))) = k1_xboole_0
    | r2_hidden(sK8(sK10,sK11),k2_relat_1(sK11)) = iProver_top
    | v1_funct_1(sK11) != iProver_top
    | v1_relat_1(sK11) != iProver_top ),
    inference(superposition,[status(thm)],[c_1026,c_5489])).

cnf(c_5507,plain,
    ( sK8(sK10,sK11) = k1_xboole_0
    | r2_hidden(sK8(sK10,sK11),k2_relat_1(sK11)) = iProver_top
    | v1_funct_1(sK11) != iProver_top
    | v1_relat_1(sK11) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5495,c_3851])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_75,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_471,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_496,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_471])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1427,plain,
    ( r1_tarski(X0,X0) ),
    inference(resolution,[status(thm)],[c_0,c_1])).

cnf(c_1429,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1427])).

cnf(c_473,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1446,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK8(sK10,sK11),sK10)
    | X0 != sK8(sK10,sK11)
    | X1 != sK10 ),
    inference(instantiation,[status(thm)],[c_473])).

cnf(c_1451,plain,
    ( ~ r2_hidden(sK8(sK10,sK11),sK10)
    | r2_hidden(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != sK8(sK10,sK11)
    | k1_xboole_0 != sK10 ),
    inference(instantiation,[status(thm)],[c_1446])).

cnf(c_31,negated_conjecture,
    ( ~ r2_hidden(X0,sK10)
    | r2_hidden(sK12(X0),sK9) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1460,plain,
    ( ~ r2_hidden(sK8(sK10,sK11),sK10)
    | r2_hidden(sK12(sK8(sK10,sK11)),sK9) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_1461,plain,
    ( r2_hidden(sK8(sK10,sK11),sK10) != iProver_top
    | r2_hidden(sK12(sK8(sK10,sK11)),sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1460])).

cnf(c_472,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1859,plain,
    ( X0 != X1
    | X0 = sK10
    | sK10 != X1 ),
    inference(instantiation,[status(thm)],[c_472])).

cnf(c_1860,plain,
    ( sK10 != k1_xboole_0
    | k1_xboole_0 = sK10
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1859])).

cnf(c_2223,plain,
    ( X0 != X1
    | X0 = sK8(sK10,sK11)
    | sK8(sK10,sK11) != X1 ),
    inference(instantiation,[status(thm)],[c_472])).

cnf(c_2224,plain,
    ( sK8(sK10,sK11) != k1_xboole_0
    | k1_xboole_0 = sK8(sK10,sK11)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2223])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1007,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1470,plain,
    ( k1_relset_1(sK9,sK10,sK11) = sK9
    | sK10 = k1_xboole_0
    | v1_funct_2(sK11,sK9,sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_1004,c_1007])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK11,sK9,sK10) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_36,plain,
    ( v1_funct_2(sK11,sK9,sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_2047,plain,
    ( sK10 = k1_xboole_0
    | k1_relset_1(sK9,sK10,sK11) = sK9 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1470,c_36])).

cnf(c_2048,plain,
    ( k1_relset_1(sK9,sK10,sK11) = sK9
    | sK10 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2047])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1016,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1867,plain,
    ( k1_relset_1(sK9,sK10,sK11) = k1_relat_1(sK11) ),
    inference(superposition,[status(thm)],[c_1004,c_1016])).

cnf(c_2049,plain,
    ( k1_relat_1(sK11) = sK9
    | sK10 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2048,c_1867])).

cnf(c_5496,plain,
    ( sK10 = k1_xboole_0
    | r2_hidden(sK8(sK10,sK11),k2_relat_1(sK11)) = iProver_top
    | r2_hidden(sK12(sK8(sK10,sK11)),sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_2049,c_5489])).

cnf(c_5742,plain,
    ( r2_hidden(sK8(sK10,sK11),k2_relat_1(sK11)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5507,c_35,c_32,c_37,c_29,c_75,c_496,c_1403,c_1404,c_1429,c_1440,c_1451,c_1461,c_1720,c_1860,c_2224,c_5496])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13311,c_5742,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:11:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.98/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.98/1.00  
% 3.98/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.98/1.00  
% 3.98/1.00  ------  iProver source info
% 3.98/1.00  
% 3.98/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.98/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.98/1.00  git: non_committed_changes: false
% 3.98/1.00  git: last_make_outside_of_git: false
% 3.98/1.00  
% 3.98/1.00  ------ 
% 3.98/1.00  ------ Parsing...
% 3.98/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.98/1.00  
% 3.98/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.98/1.00  
% 3.98/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.98/1.00  
% 3.98/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.98/1.00  ------ Proving...
% 3.98/1.00  ------ Problem Properties 
% 3.98/1.00  
% 3.98/1.00  
% 3.98/1.00  clauses                                 34
% 3.98/1.00  conjectures                             6
% 3.98/1.00  EPR                                     3
% 3.98/1.00  Horn                                    24
% 3.98/1.00  unary                                   5
% 3.98/1.00  binary                                  8
% 3.98/1.00  lits                                    102
% 3.98/1.00  lits eq                                 25
% 3.98/1.00  fd_pure                                 0
% 3.98/1.00  fd_pseudo                               0
% 3.98/1.00  fd_cond                                 3
% 3.98/1.00  fd_pseudo_cond                          6
% 3.98/1.00  AC symbols                              0
% 3.98/1.00  
% 3.98/1.00  ------ Input Options Time Limit: Unbounded
% 3.98/1.00  
% 3.98/1.00  
% 3.98/1.00  ------ 
% 3.98/1.00  Current options:
% 3.98/1.00  ------ 
% 3.98/1.00  
% 3.98/1.00  
% 3.98/1.00  
% 3.98/1.00  
% 3.98/1.00  ------ Proving...
% 3.98/1.00  
% 3.98/1.00  
% 3.98/1.00  % SZS status Theorem for theBenchmark.p
% 3.98/1.00  
% 3.98/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.98/1.00  
% 3.98/1.00  fof(f11,conjecture,(
% 3.98/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 3.98/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.98/1.00  
% 3.98/1.00  fof(f12,negated_conjecture,(
% 3.98/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 3.98/1.00    inference(negated_conjecture,[],[f11])).
% 3.98/1.00  
% 3.98/1.00  fof(f25,plain,(
% 3.98/1.00    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.98/1.00    inference(ennf_transformation,[],[f12])).
% 3.98/1.00  
% 3.98/1.00  fof(f26,plain,(
% 3.98/1.00    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.98/1.00    inference(flattening,[],[f25])).
% 3.98/1.00  
% 3.98/1.00  fof(f49,plain,(
% 3.98/1.00    ( ! [X2,X0] : (! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) => (k1_funct_1(X2,sK12(X3)) = X3 & r2_hidden(sK12(X3),X0)))) )),
% 3.98/1.00    introduced(choice_axiom,[])).
% 3.98/1.00  
% 3.98/1.00  fof(f48,plain,(
% 3.98/1.00    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (k2_relset_1(sK9,sK10,sK11) != sK10 & ! [X3] : (? [X4] : (k1_funct_1(sK11,X4) = X3 & r2_hidden(X4,sK9)) | ~r2_hidden(X3,sK10)) & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) & v1_funct_2(sK11,sK9,sK10) & v1_funct_1(sK11))),
% 3.98/1.00    introduced(choice_axiom,[])).
% 3.98/1.00  
% 3.98/1.00  fof(f50,plain,(
% 3.98/1.00    k2_relset_1(sK9,sK10,sK11) != sK10 & ! [X3] : ((k1_funct_1(sK11,sK12(X3)) = X3 & r2_hidden(sK12(X3),sK9)) | ~r2_hidden(X3,sK10)) & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) & v1_funct_2(sK11,sK9,sK10) & v1_funct_1(sK11)),
% 3.98/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11,sK12])],[f26,f49,f48])).
% 3.98/1.00  
% 3.98/1.00  fof(f82,plain,(
% 3.98/1.00    m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))),
% 3.98/1.00    inference(cnf_transformation,[],[f50])).
% 3.98/1.00  
% 3.98/1.00  fof(f3,axiom,(
% 3.98/1.00    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 3.98/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.98/1.00  
% 3.98/1.00  fof(f29,plain,(
% 3.98/1.00    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 3.98/1.00    inference(nnf_transformation,[],[f3])).
% 3.98/1.00  
% 3.98/1.00  fof(f30,plain,(
% 3.98/1.00    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 3.98/1.00    inference(rectify,[],[f29])).
% 3.98/1.00  
% 3.98/1.00  fof(f33,plain,(
% 3.98/1.00    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK3(X0,X5),X5),X0))),
% 3.98/1.00    introduced(choice_axiom,[])).
% 3.98/1.00  
% 3.98/1.00  fof(f32,plain,(
% 3.98/1.00    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK2(X0,X1),X2),X0))) )),
% 3.98/1.00    introduced(choice_axiom,[])).
% 3.98/1.00  
% 3.98/1.00  fof(f31,plain,(
% 3.98/1.00    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK1(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 3.98/1.00    introduced(choice_axiom,[])).
% 3.98/1.00  
% 3.98/1.00  fof(f34,plain,(
% 3.98/1.00    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 3.98/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f30,f33,f32,f31])).
% 3.98/1.00  
% 3.98/1.00  fof(f54,plain,(
% 3.98/1.00    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 3.98/1.00    inference(cnf_transformation,[],[f34])).
% 3.98/1.00  
% 3.98/1.00  fof(f87,plain,(
% 3.98/1.00    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 3.98/1.00    inference(equality_resolution,[],[f54])).
% 3.98/1.00  
% 3.98/1.00  fof(f9,axiom,(
% 3.98/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 3.98/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.98/1.00  
% 3.98/1.00  fof(f22,plain,(
% 3.98/1.00    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.98/1.00    inference(ennf_transformation,[],[f9])).
% 3.98/1.00  
% 3.98/1.00  fof(f42,plain,(
% 3.98/1.00    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)) | k2_relset_1(X0,X1,X2) != X1) & (k2_relset_1(X0,X1,X2) = X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.98/1.00    inference(nnf_transformation,[],[f22])).
% 3.98/1.00  
% 3.98/1.00  fof(f43,plain,(
% 3.98/1.00    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)) | k2_relset_1(X0,X1,X2) != X1) & (k2_relset_1(X0,X1,X2) = X1 | ? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X6,X5),X2) & r2_hidden(X5,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.98/1.00    inference(rectify,[],[f42])).
% 3.98/1.00  
% 3.98/1.00  fof(f45,plain,(
% 3.98/1.00    ! [X2,X1] : (? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X6,X5),X2) & r2_hidden(X5,X1)) => (! [X6] : ~r2_hidden(k4_tarski(X6,sK8(X1,X2)),X2) & r2_hidden(sK8(X1,X2),X1)))),
% 3.98/1.00    introduced(choice_axiom,[])).
% 3.98/1.00  
% 3.98/1.00  fof(f44,plain,(
% 3.98/1.00    ! [X3,X2] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) => r2_hidden(k4_tarski(sK7(X2,X3),X3),X2))),
% 3.98/1.00    introduced(choice_axiom,[])).
% 3.98/1.00  
% 3.98/1.00  fof(f46,plain,(
% 3.98/1.00    ! [X0,X1,X2] : (((! [X3] : (r2_hidden(k4_tarski(sK7(X2,X3),X3),X2) | ~r2_hidden(X3,X1)) | k2_relset_1(X0,X1,X2) != X1) & (k2_relset_1(X0,X1,X2) = X1 | (! [X6] : ~r2_hidden(k4_tarski(X6,sK8(X1,X2)),X2) & r2_hidden(sK8(X1,X2),X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.98/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f43,f45,f44])).
% 3.98/1.00  
% 3.98/1.00  fof(f72,plain,(
% 3.98/1.00    ( ! [X6,X2,X0,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_hidden(k4_tarski(X6,sK8(X1,X2)),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.98/1.00    inference(cnf_transformation,[],[f46])).
% 3.98/1.00  
% 3.98/1.00  fof(f5,axiom,(
% 3.98/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 3.98/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.98/1.00  
% 3.98/1.00  fof(f16,plain,(
% 3.98/1.00    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.98/1.00    inference(ennf_transformation,[],[f5])).
% 3.98/1.00  
% 3.98/1.00  fof(f17,plain,(
% 3.98/1.00    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.98/1.00    inference(flattening,[],[f16])).
% 3.98/1.00  
% 3.98/1.00  fof(f35,plain,(
% 3.98/1.00    ! [X0] : (! [X1,X2] : ((((k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2)) | r2_hidden(X1,k1_relat_1(X0))) & (((k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0)) & (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.98/1.00    inference(nnf_transformation,[],[f17])).
% 3.98/1.00  
% 3.98/1.00  fof(f61,plain,(
% 3.98/1.00    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2 | r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.98/1.00    inference(cnf_transformation,[],[f35])).
% 3.98/1.00  
% 3.98/1.00  fof(f89,plain,(
% 3.98/1.00    ( ! [X0,X1] : (k1_funct_1(X0,X1) = k1_xboole_0 | r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.98/1.00    inference(equality_resolution,[],[f61])).
% 3.98/1.00  
% 3.98/1.00  fof(f71,plain,(
% 3.98/1.00    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = X1 | r2_hidden(sK8(X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.98/1.00    inference(cnf_transformation,[],[f46])).
% 3.98/1.00  
% 3.98/1.00  fof(f85,plain,(
% 3.98/1.00    k2_relset_1(sK9,sK10,sK11) != sK10),
% 3.98/1.00    inference(cnf_transformation,[],[f50])).
% 3.98/1.00  
% 3.98/1.00  fof(f84,plain,(
% 3.98/1.00    ( ! [X3] : (k1_funct_1(sK11,sK12(X3)) = X3 | ~r2_hidden(X3,sK10)) )),
% 3.98/1.00    inference(cnf_transformation,[],[f50])).
% 3.98/1.00  
% 3.98/1.00  fof(f6,axiom,(
% 3.98/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 3.98/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.98/1.00  
% 3.98/1.00  fof(f18,plain,(
% 3.98/1.00    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.98/1.00    inference(ennf_transformation,[],[f6])).
% 3.98/1.00  
% 3.98/1.00  fof(f19,plain,(
% 3.98/1.00    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.98/1.00    inference(flattening,[],[f18])).
% 3.98/1.00  
% 3.98/1.00  fof(f36,plain,(
% 3.98/1.00    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.98/1.00    inference(nnf_transformation,[],[f19])).
% 3.98/1.00  
% 3.98/1.00  fof(f37,plain,(
% 3.98/1.00    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.98/1.00    inference(rectify,[],[f36])).
% 3.98/1.00  
% 3.98/1.00  fof(f40,plain,(
% 3.98/1.00    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK6(X0,X5)) = X5 & r2_hidden(sK6(X0,X5),k1_relat_1(X0))))),
% 3.98/1.00    introduced(choice_axiom,[])).
% 3.98/1.00  
% 3.98/1.00  fof(f39,plain,(
% 3.98/1.00    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK5(X0,X1)) = X2 & r2_hidden(sK5(X0,X1),k1_relat_1(X0))))) )),
% 3.98/1.00    introduced(choice_axiom,[])).
% 3.98/1.00  
% 3.98/1.00  fof(f38,plain,(
% 3.98/1.00    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK4(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK4(X0,X1),X1))))),
% 3.98/1.00    introduced(choice_axiom,[])).
% 3.98/1.00  
% 3.98/1.00  fof(f41,plain,(
% 3.98/1.00    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1),X1)) & ((k1_funct_1(X0,sK5(X0,X1)) = sK4(X0,X1) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK6(X0,X5)) = X5 & r2_hidden(sK6(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.98/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f37,f40,f39,f38])).
% 3.98/1.00  
% 3.98/1.00  fof(f65,plain,(
% 3.98/1.00    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.98/1.00    inference(cnf_transformation,[],[f41])).
% 3.98/1.00  
% 3.98/1.00  fof(f91,plain,(
% 3.98/1.00    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.98/1.00    inference(equality_resolution,[],[f65])).
% 3.98/1.00  
% 3.98/1.00  fof(f92,plain,(
% 3.98/1.00    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.98/1.00    inference(equality_resolution,[],[f91])).
% 3.98/1.00  
% 3.98/1.00  fof(f80,plain,(
% 3.98/1.00    v1_funct_1(sK11)),
% 3.98/1.00    inference(cnf_transformation,[],[f50])).
% 3.98/1.00  
% 3.98/1.00  fof(f2,axiom,(
% 3.98/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.98/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.98/1.00  
% 3.98/1.00  fof(f15,plain,(
% 3.98/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.98/1.00    inference(ennf_transformation,[],[f2])).
% 3.98/1.00  
% 3.98/1.00  fof(f53,plain,(
% 3.98/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.98/1.00    inference(cnf_transformation,[],[f15])).
% 3.98/1.00  
% 3.98/1.00  fof(f4,axiom,(
% 3.98/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.98/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.98/1.00  
% 3.98/1.00  fof(f58,plain,(
% 3.98/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.98/1.00    inference(cnf_transformation,[],[f4])).
% 3.98/1.00  
% 3.98/1.00  fof(f7,axiom,(
% 3.98/1.00    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.98/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.98/1.00  
% 3.98/1.00  fof(f20,plain,(
% 3.98/1.00    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.98/1.00    inference(ennf_transformation,[],[f7])).
% 3.98/1.00  
% 3.98/1.00  fof(f69,plain,(
% 3.98/1.00    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.98/1.00    inference(cnf_transformation,[],[f20])).
% 3.98/1.00  
% 3.98/1.00  fof(f1,axiom,(
% 3.98/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.98/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.98/1.00  
% 3.98/1.00  fof(f13,plain,(
% 3.98/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 3.98/1.00    inference(unused_predicate_definition_removal,[],[f1])).
% 3.98/1.00  
% 3.98/1.00  fof(f14,plain,(
% 3.98/1.00    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 3.98/1.00    inference(ennf_transformation,[],[f13])).
% 3.98/1.00  
% 3.98/1.00  fof(f27,plain,(
% 3.98/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.98/1.00    introduced(choice_axiom,[])).
% 3.98/1.00  
% 3.98/1.00  fof(f28,plain,(
% 3.98/1.00    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.98/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f27])).
% 3.98/1.00  
% 3.98/1.00  fof(f52,plain,(
% 3.98/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.98/1.00    inference(cnf_transformation,[],[f28])).
% 3.98/1.00  
% 3.98/1.00  fof(f51,plain,(
% 3.98/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.98/1.00    inference(cnf_transformation,[],[f28])).
% 3.98/1.00  
% 3.98/1.00  fof(f83,plain,(
% 3.98/1.00    ( ! [X3] : (r2_hidden(sK12(X3),sK9) | ~r2_hidden(X3,sK10)) )),
% 3.98/1.00    inference(cnf_transformation,[],[f50])).
% 3.98/1.00  
% 3.98/1.00  fof(f10,axiom,(
% 3.98/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.98/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.98/1.00  
% 3.98/1.00  fof(f23,plain,(
% 3.98/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.98/1.00    inference(ennf_transformation,[],[f10])).
% 3.98/1.00  
% 3.98/1.00  fof(f24,plain,(
% 3.98/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.98/1.00    inference(flattening,[],[f23])).
% 3.98/1.00  
% 3.98/1.00  fof(f47,plain,(
% 3.98/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.98/1.00    inference(nnf_transformation,[],[f24])).
% 3.98/1.00  
% 3.98/1.00  fof(f74,plain,(
% 3.98/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.98/1.00    inference(cnf_transformation,[],[f47])).
% 3.98/1.00  
% 3.98/1.00  fof(f81,plain,(
% 3.98/1.00    v1_funct_2(sK11,sK9,sK10)),
% 3.98/1.00    inference(cnf_transformation,[],[f50])).
% 3.98/1.00  
% 3.98/1.00  fof(f8,axiom,(
% 3.98/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.98/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.98/1.00  
% 3.98/1.00  fof(f21,plain,(
% 3.98/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.98/1.00    inference(ennf_transformation,[],[f8])).
% 3.98/1.00  
% 3.98/1.00  fof(f70,plain,(
% 3.98/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.98/1.00    inference(cnf_transformation,[],[f21])).
% 3.98/1.00  
% 3.98/1.00  cnf(c_32,negated_conjecture,
% 3.98/1.00      ( m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) ),
% 3.98/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_1004,plain,
% 3.98/1.00      ( m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) = iProver_top ),
% 3.98/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_6,plain,
% 3.98/1.00      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.98/1.00      | r2_hidden(k4_tarski(sK3(X1,X0),X0),X1) ),
% 3.98/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_1028,plain,
% 3.98/1.00      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 3.98/1.00      | r2_hidden(k4_tarski(sK3(X1,X0),X0),X1) = iProver_top ),
% 3.98/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_21,plain,
% 3.98/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.98/1.00      | ~ r2_hidden(k4_tarski(X3,sK8(X2,X0)),X0)
% 3.98/1.00      | k2_relset_1(X1,X2,X0) = X2 ),
% 3.98/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_1014,plain,
% 3.98/1.00      ( k2_relset_1(X0,X1,X2) = X1
% 3.98/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.98/1.00      | r2_hidden(k4_tarski(X3,sK8(X1,X2)),X2) != iProver_top ),
% 3.98/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_4761,plain,
% 3.98/1.00      ( k2_relset_1(X0,X1,X2) = X1
% 3.98/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.98/1.00      | r2_hidden(sK8(X1,X2),k2_relat_1(X2)) != iProver_top ),
% 3.98/1.00      inference(superposition,[status(thm)],[c_1028,c_1014]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_13311,plain,
% 3.98/1.00      ( k2_relset_1(sK9,sK10,sK11) = sK10
% 3.98/1.00      | r2_hidden(sK8(sK10,sK11),k2_relat_1(sK11)) != iProver_top ),
% 3.98/1.00      inference(superposition,[status(thm)],[c_1004,c_4761]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_9,plain,
% 3.98/1.00      ( r2_hidden(X0,k1_relat_1(X1))
% 3.98/1.00      | ~ v1_funct_1(X1)
% 3.98/1.00      | ~ v1_relat_1(X1)
% 3.98/1.00      | k1_funct_1(X1,X0) = k1_xboole_0 ),
% 3.98/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_1026,plain,
% 3.98/1.00      ( k1_funct_1(X0,X1) = k1_xboole_0
% 3.98/1.00      | r2_hidden(X1,k1_relat_1(X0)) = iProver_top
% 3.98/1.00      | v1_funct_1(X0) != iProver_top
% 3.98/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.98/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_22,plain,
% 3.98/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.98/1.00      | r2_hidden(sK8(X2,X0),X2)
% 3.98/1.00      | k2_relset_1(X1,X2,X0) = X2 ),
% 3.98/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_1013,plain,
% 3.98/1.00      ( k2_relset_1(X0,X1,X2) = X1
% 3.98/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.98/1.00      | r2_hidden(sK8(X1,X2),X1) = iProver_top ),
% 3.98/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_3527,plain,
% 3.98/1.00      ( k2_relset_1(sK9,sK10,sK11) = sK10
% 3.98/1.00      | r2_hidden(sK8(sK10,sK11),sK10) = iProver_top ),
% 3.98/1.00      inference(superposition,[status(thm)],[c_1004,c_1013]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_37,plain,
% 3.98/1.00      ( m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) = iProver_top ),
% 3.98/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_29,negated_conjecture,
% 3.98/1.00      ( k2_relset_1(sK9,sK10,sK11) != sK10 ),
% 3.98/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_1403,plain,
% 3.98/1.00      ( ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))
% 3.98/1.00      | r2_hidden(sK8(sK10,sK11),sK10)
% 3.98/1.00      | k2_relset_1(sK9,sK10,sK11) = sK10 ),
% 3.98/1.00      inference(instantiation,[status(thm)],[c_22]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_1404,plain,
% 3.98/1.00      ( k2_relset_1(sK9,sK10,sK11) = sK10
% 3.98/1.00      | m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) != iProver_top
% 3.98/1.00      | r2_hidden(sK8(sK10,sK11),sK10) = iProver_top ),
% 3.98/1.00      inference(predicate_to_equality,[status(thm)],[c_1403]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_3845,plain,
% 3.98/1.00      ( r2_hidden(sK8(sK10,sK11),sK10) = iProver_top ),
% 3.98/1.00      inference(global_propositional_subsumption,
% 3.98/1.00                [status(thm)],
% 3.98/1.00                [c_3527,c_37,c_29,c_1404]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_30,negated_conjecture,
% 3.98/1.00      ( ~ r2_hidden(X0,sK10) | k1_funct_1(sK11,sK12(X0)) = X0 ),
% 3.98/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_1006,plain,
% 3.98/1.00      ( k1_funct_1(sK11,sK12(X0)) = X0
% 3.98/1.00      | r2_hidden(X0,sK10) != iProver_top ),
% 3.98/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_3851,plain,
% 3.98/1.00      ( k1_funct_1(sK11,sK12(sK8(sK10,sK11))) = sK8(sK10,sK11) ),
% 3.98/1.00      inference(superposition,[status(thm)],[c_3845,c_1006]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_15,plain,
% 3.98/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.98/1.00      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 3.98/1.00      | ~ v1_funct_1(X1)
% 3.98/1.00      | ~ v1_relat_1(X1) ),
% 3.98/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_1020,plain,
% 3.98/1.00      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 3.98/1.00      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
% 3.98/1.00      | v1_funct_1(X1) != iProver_top
% 3.98/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.98/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_5195,plain,
% 3.98/1.00      ( r2_hidden(sK8(sK10,sK11),k2_relat_1(sK11)) = iProver_top
% 3.98/1.00      | r2_hidden(sK12(sK8(sK10,sK11)),k1_relat_1(sK11)) != iProver_top
% 3.98/1.00      | v1_funct_1(sK11) != iProver_top
% 3.98/1.00      | v1_relat_1(sK11) != iProver_top ),
% 3.98/1.00      inference(superposition,[status(thm)],[c_3851,c_1020]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_34,negated_conjecture,
% 3.98/1.00      ( v1_funct_1(sK11) ),
% 3.98/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_35,plain,
% 3.98/1.00      ( v1_funct_1(sK11) = iProver_top ),
% 3.98/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_2,plain,
% 3.98/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.98/1.00      | ~ v1_relat_1(X1)
% 3.98/1.00      | v1_relat_1(X0) ),
% 3.98/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_1439,plain,
% 3.98/1.00      ( ~ v1_relat_1(k2_zfmisc_1(sK9,sK10)) | v1_relat_1(sK11) ),
% 3.98/1.00      inference(resolution,[status(thm)],[c_2,c_32]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_1440,plain,
% 3.98/1.00      ( v1_relat_1(k2_zfmisc_1(sK9,sK10)) != iProver_top
% 3.98/1.00      | v1_relat_1(sK11) = iProver_top ),
% 3.98/1.00      inference(predicate_to_equality,[status(thm)],[c_1439]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_7,plain,
% 3.98/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.98/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_1719,plain,
% 3.98/1.00      ( v1_relat_1(k2_zfmisc_1(sK9,sK10)) ),
% 3.98/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_1720,plain,
% 3.98/1.00      ( v1_relat_1(k2_zfmisc_1(sK9,sK10)) = iProver_top ),
% 3.98/1.00      inference(predicate_to_equality,[status(thm)],[c_1719]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_5489,plain,
% 3.98/1.00      ( r2_hidden(sK8(sK10,sK11),k2_relat_1(sK11)) = iProver_top
% 3.98/1.00      | r2_hidden(sK12(sK8(sK10,sK11)),k1_relat_1(sK11)) != iProver_top ),
% 3.98/1.00      inference(global_propositional_subsumption,
% 3.98/1.00                [status(thm)],
% 3.98/1.00                [c_5195,c_35,c_1440,c_1720]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_5495,plain,
% 3.98/1.00      ( k1_funct_1(sK11,sK12(sK8(sK10,sK11))) = k1_xboole_0
% 3.98/1.00      | r2_hidden(sK8(sK10,sK11),k2_relat_1(sK11)) = iProver_top
% 3.98/1.00      | v1_funct_1(sK11) != iProver_top
% 3.98/1.00      | v1_relat_1(sK11) != iProver_top ),
% 3.98/1.00      inference(superposition,[status(thm)],[c_1026,c_5489]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_5507,plain,
% 3.98/1.00      ( sK8(sK10,sK11) = k1_xboole_0
% 3.98/1.00      | r2_hidden(sK8(sK10,sK11),k2_relat_1(sK11)) = iProver_top
% 3.98/1.00      | v1_funct_1(sK11) != iProver_top
% 3.98/1.00      | v1_relat_1(sK11) != iProver_top ),
% 3.98/1.00      inference(demodulation,[status(thm)],[c_5495,c_3851]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_18,plain,
% 3.98/1.00      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 3.98/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_75,plain,
% 3.98/1.00      ( ~ r2_hidden(k1_xboole_0,k1_xboole_0)
% 3.98/1.00      | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.98/1.00      inference(instantiation,[status(thm)],[c_18]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_471,plain,( X0 = X0 ),theory(equality) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_496,plain,
% 3.98/1.00      ( k1_xboole_0 = k1_xboole_0 ),
% 3.98/1.00      inference(instantiation,[status(thm)],[c_471]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_0,plain,
% 3.98/1.00      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.98/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_1,plain,
% 3.98/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.98/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_1427,plain,
% 3.98/1.00      ( r1_tarski(X0,X0) ),
% 3.98/1.00      inference(resolution,[status(thm)],[c_0,c_1]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_1429,plain,
% 3.98/1.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.98/1.00      inference(instantiation,[status(thm)],[c_1427]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_473,plain,
% 3.98/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.98/1.00      theory(equality) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_1446,plain,
% 3.98/1.00      ( r2_hidden(X0,X1)
% 3.98/1.00      | ~ r2_hidden(sK8(sK10,sK11),sK10)
% 3.98/1.00      | X0 != sK8(sK10,sK11)
% 3.98/1.00      | X1 != sK10 ),
% 3.98/1.00      inference(instantiation,[status(thm)],[c_473]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_1451,plain,
% 3.98/1.00      ( ~ r2_hidden(sK8(sK10,sK11),sK10)
% 3.98/1.00      | r2_hidden(k1_xboole_0,k1_xboole_0)
% 3.98/1.00      | k1_xboole_0 != sK8(sK10,sK11)
% 3.98/1.00      | k1_xboole_0 != sK10 ),
% 3.98/1.00      inference(instantiation,[status(thm)],[c_1446]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_31,negated_conjecture,
% 3.98/1.00      ( ~ r2_hidden(X0,sK10) | r2_hidden(sK12(X0),sK9) ),
% 3.98/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_1460,plain,
% 3.98/1.00      ( ~ r2_hidden(sK8(sK10,sK11),sK10)
% 3.98/1.00      | r2_hidden(sK12(sK8(sK10,sK11)),sK9) ),
% 3.98/1.00      inference(instantiation,[status(thm)],[c_31]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_1461,plain,
% 3.98/1.00      ( r2_hidden(sK8(sK10,sK11),sK10) != iProver_top
% 3.98/1.00      | r2_hidden(sK12(sK8(sK10,sK11)),sK9) = iProver_top ),
% 3.98/1.00      inference(predicate_to_equality,[status(thm)],[c_1460]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_472,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_1859,plain,
% 3.98/1.00      ( X0 != X1 | X0 = sK10 | sK10 != X1 ),
% 3.98/1.00      inference(instantiation,[status(thm)],[c_472]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_1860,plain,
% 3.98/1.00      ( sK10 != k1_xboole_0
% 3.98/1.00      | k1_xboole_0 = sK10
% 3.98/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.98/1.00      inference(instantiation,[status(thm)],[c_1859]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_2223,plain,
% 3.98/1.00      ( X0 != X1 | X0 = sK8(sK10,sK11) | sK8(sK10,sK11) != X1 ),
% 3.98/1.00      inference(instantiation,[status(thm)],[c_472]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_2224,plain,
% 3.98/1.00      ( sK8(sK10,sK11) != k1_xboole_0
% 3.98/1.00      | k1_xboole_0 = sK8(sK10,sK11)
% 3.98/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.98/1.00      inference(instantiation,[status(thm)],[c_2223]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_28,plain,
% 3.98/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.98/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.98/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.98/1.00      | k1_xboole_0 = X2 ),
% 3.98/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_1007,plain,
% 3.98/1.00      ( k1_relset_1(X0,X1,X2) = X0
% 3.98/1.00      | k1_xboole_0 = X1
% 3.98/1.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.98/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.98/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_1470,plain,
% 3.98/1.00      ( k1_relset_1(sK9,sK10,sK11) = sK9
% 3.98/1.00      | sK10 = k1_xboole_0
% 3.98/1.00      | v1_funct_2(sK11,sK9,sK10) != iProver_top ),
% 3.98/1.00      inference(superposition,[status(thm)],[c_1004,c_1007]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_33,negated_conjecture,
% 3.98/1.00      ( v1_funct_2(sK11,sK9,sK10) ),
% 3.98/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_36,plain,
% 3.98/1.00      ( v1_funct_2(sK11,sK9,sK10) = iProver_top ),
% 3.98/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_2047,plain,
% 3.98/1.00      ( sK10 = k1_xboole_0 | k1_relset_1(sK9,sK10,sK11) = sK9 ),
% 3.98/1.00      inference(global_propositional_subsumption,
% 3.98/1.00                [status(thm)],
% 3.98/1.00                [c_1470,c_36]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_2048,plain,
% 3.98/1.00      ( k1_relset_1(sK9,sK10,sK11) = sK9 | sK10 = k1_xboole_0 ),
% 3.98/1.00      inference(renaming,[status(thm)],[c_2047]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_19,plain,
% 3.98/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.98/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.98/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_1016,plain,
% 3.98/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.98/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.98/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_1867,plain,
% 3.98/1.00      ( k1_relset_1(sK9,sK10,sK11) = k1_relat_1(sK11) ),
% 3.98/1.00      inference(superposition,[status(thm)],[c_1004,c_1016]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_2049,plain,
% 3.98/1.00      ( k1_relat_1(sK11) = sK9 | sK10 = k1_xboole_0 ),
% 3.98/1.00      inference(demodulation,[status(thm)],[c_2048,c_1867]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_5496,plain,
% 3.98/1.00      ( sK10 = k1_xboole_0
% 3.98/1.00      | r2_hidden(sK8(sK10,sK11),k2_relat_1(sK11)) = iProver_top
% 3.98/1.00      | r2_hidden(sK12(sK8(sK10,sK11)),sK9) != iProver_top ),
% 3.98/1.00      inference(superposition,[status(thm)],[c_2049,c_5489]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(c_5742,plain,
% 3.98/1.00      ( r2_hidden(sK8(sK10,sK11),k2_relat_1(sK11)) = iProver_top ),
% 3.98/1.00      inference(global_propositional_subsumption,
% 3.98/1.00                [status(thm)],
% 3.98/1.00                [c_5507,c_35,c_32,c_37,c_29,c_75,c_496,c_1403,c_1404,
% 3.98/1.00                 c_1429,c_1440,c_1451,c_1461,c_1720,c_1860,c_2224,c_5496]) ).
% 3.98/1.00  
% 3.98/1.00  cnf(contradiction,plain,
% 3.98/1.00      ( $false ),
% 3.98/1.00      inference(minisat,[status(thm)],[c_13311,c_5742,c_29]) ).
% 3.98/1.00  
% 3.98/1.00  
% 3.98/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.98/1.00  
% 3.98/1.00  ------                               Statistics
% 3.98/1.00  
% 3.98/1.00  ------ Selected
% 3.98/1.00  
% 3.98/1.00  total_time:                             0.497
% 3.98/1.00  
%------------------------------------------------------------------------------
