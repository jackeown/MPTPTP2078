%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:18 EST 2020

% Result     : Theorem 31.47s
% Output     : CNFRefutation 31.47s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 347 expanded)
%              Number of clauses        :   63 ( 103 expanded)
%              Number of leaves         :   18 (  81 expanded)
%              Depth                    :   21
%              Number of atoms          :  441 (1970 expanded)
%              Number of equality atoms :  109 ( 309 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f38,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK5(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f35,f38,f37,f36])).

fof(f55,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f80,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f55])).

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

fof(f12,plain,(
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

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(X1,X2),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f28])).

fof(f32,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f29,f32,f31,f30])).

fof(f52,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f77,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f9,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( ! [X3] :
                ( r2_hidden(X3,X0)
               => r2_hidden(k1_funct_1(X2,X3),X1) )
            & k1_relat_1(X2) = X0 )
         => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X2,X0,X1)
            & v1_funct_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & ! [X3] :
          ( r2_hidden(k1_funct_1(X2,X3),X1)
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & ! [X3] :
          ( r2_hidden(k1_funct_1(X2,X3),X1)
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f43,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2) )
        & ! [X3] :
            ( r2_hidden(k1_funct_1(X2,X3),X1)
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(X2) = X0
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
        | ~ v1_funct_2(sK9,sK7,sK8)
        | ~ v1_funct_1(sK9) )
      & ! [X3] :
          ( r2_hidden(k1_funct_1(sK9,X3),sK8)
          | ~ r2_hidden(X3,sK7) )
      & k1_relat_1(sK9) = sK7
      & v1_funct_1(sK9)
      & v1_relat_1(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
      | ~ v1_funct_2(sK9,sK7,sK8)
      | ~ v1_funct_1(sK9) )
    & ! [X3] :
        ( r2_hidden(k1_funct_1(sK9,X3),sK8)
        | ~ r2_hidden(X3,sK7) )
    & k1_relat_1(sK9) = sK7
    & v1_funct_1(sK9)
    & v1_relat_1(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f21,f43])).

fof(f71,plain,(
    v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f44])).

fof(f70,plain,(
    v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f44])).

fof(f72,plain,(
    k1_relat_1(sK9) = sK7 ),
    inference(cnf_transformation,[],[f44])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f74,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ v1_funct_2(sK9,sK7,sK8)
    | ~ v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f44])).

fof(f73,plain,(
    ! [X3] :
      ( r2_hidden(k1_funct_1(sK9,X3),sK8)
      | ~ r2_hidden(X3,sK7) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f76,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_949,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK6(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_938,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(sK6(X1,X0),X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_funct_1(X1,X0) = X2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_8,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_175,plain,
    ( ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_funct_1(X1,X0) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_16,c_8])).

cnf(c_176,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(renaming,[status(thm)],[c_175])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_416,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK9 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_176,c_28])).

cnf(c_417,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK9)
    | ~ v1_relat_1(sK9)
    | k1_funct_1(sK9,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_416])).

cnf(c_29,negated_conjecture,
    ( v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_421,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK9)
    | k1_funct_1(sK9,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_417,c_29])).

cnf(c_932,plain,
    ( k1_funct_1(sK9,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_421])).

cnf(c_1383,plain,
    ( k1_funct_1(sK9,sK6(sK9,X0)) = X0
    | r2_hidden(X0,k2_relat_1(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_938,c_932])).

cnf(c_2821,plain,
    ( k1_funct_1(sK9,sK6(sK9,sK0(k2_relat_1(sK9),X0))) = sK0(k2_relat_1(sK9),X0)
    | r1_tarski(k2_relat_1(sK9),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_949,c_1383])).

cnf(c_27,negated_conjecture,
    ( k1_relat_1(sK9) = sK7 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_22,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_23,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_25,negated_conjecture,
    ( ~ v1_funct_2(sK9,sK7,sK8)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_159,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ v1_funct_2(sK9,sK7,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_25,c_28])).

cnf(c_160,negated_conjecture,
    ( ~ v1_funct_2(sK9,sK7,sK8)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) ),
    inference(renaming,[status(thm)],[c_159])).

cnf(c_309,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) != sK7
    | sK8 != X1
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_160])).

cnf(c_310,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ r1_tarski(k2_relat_1(sK9),sK8)
    | ~ v1_relat_1(sK9)
    | ~ v1_funct_1(sK9)
    | k1_relat_1(sK9) != sK7 ),
    inference(unflattening,[status(thm)],[c_309])).

cnf(c_312,plain,
    ( ~ r1_tarski(k2_relat_1(sK9),sK8)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_310,c_29,c_28,c_27])).

cnf(c_313,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ r1_tarski(k2_relat_1(sK9),sK8) ),
    inference(renaming,[status(thm)],[c_312])).

cnf(c_350,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(sK9),sK8)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)) != k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_313])).

cnf(c_351,plain,
    ( ~ r1_tarski(k2_relat_1(sK9),X0)
    | ~ r1_tarski(k2_relat_1(sK9),sK8)
    | ~ v1_relat_1(sK9)
    | ~ v1_funct_1(sK9)
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK9),X0)) != k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)) ),
    inference(unflattening,[status(thm)],[c_350])).

cnf(c_355,plain,
    ( ~ r1_tarski(k2_relat_1(sK9),X0)
    | ~ r1_tarski(k2_relat_1(sK9),sK8)
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK9),X0)) != k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_351,c_29,c_28])).

cnf(c_935,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK9),X0)) != k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))
    | r1_tarski(k2_relat_1(sK9),X0) != iProver_top
    | r1_tarski(k2_relat_1(sK9),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_355])).

cnf(c_1567,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK7,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))
    | r1_tarski(k2_relat_1(sK9),X0) != iProver_top
    | r1_tarski(k2_relat_1(sK9),sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_27,c_935])).

cnf(c_2034,plain,
    ( r1_tarski(k2_relat_1(sK9),sK8) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1567])).

cnf(c_5725,plain,
    ( k1_funct_1(sK9,sK6(sK9,sK0(k2_relat_1(sK9),sK8))) = sK0(k2_relat_1(sK9),sK8) ),
    inference(superposition,[status(thm)],[c_2821,c_2034])).

cnf(c_26,negated_conjecture,
    ( ~ r2_hidden(X0,sK7)
    | r2_hidden(k1_funct_1(sK9,X0),sK8) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_937,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(k1_funct_1(sK9,X0),sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_109847,plain,
    ( r2_hidden(sK6(sK9,sK0(k2_relat_1(sK9),sK8)),sK7) != iProver_top
    | r2_hidden(sK0(k2_relat_1(sK9),sK8),sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_5725,c_937])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_4899,plain,
    ( r2_hidden(sK6(sK9,sK0(k2_relat_1(sK9),sK8)),X0)
    | ~ r2_hidden(sK6(sK9,sK0(k2_relat_1(sK9),sK8)),k1_relat_1(sK9))
    | ~ r1_tarski(k1_relat_1(sK9),X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_34336,plain,
    ( ~ r2_hidden(sK6(sK9,sK0(k2_relat_1(sK9),sK8)),k1_relat_1(sK9))
    | r2_hidden(sK6(sK9,sK0(k2_relat_1(sK9),sK8)),sK7)
    | ~ r1_tarski(k1_relat_1(sK9),sK7) ),
    inference(instantiation,[status(thm)],[c_4899])).

cnf(c_34337,plain,
    ( r2_hidden(sK6(sK9,sK0(k2_relat_1(sK9),sK8)),k1_relat_1(sK9)) != iProver_top
    | r2_hidden(sK6(sK9,sK0(k2_relat_1(sK9),sK8)),sK7) = iProver_top
    | r1_tarski(k1_relat_1(sK9),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34336])).

cnf(c_580,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_579,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2181,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_580,c_579])).

cnf(c_4479,plain,
    ( sK7 = k1_relat_1(sK9) ),
    inference(resolution,[status(thm)],[c_2181,c_27])).

cnf(c_581,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_4755,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK9))
    | r1_tarski(X1,sK7)
    | X1 != X0 ),
    inference(resolution,[status(thm)],[c_4479,c_581])).

cnf(c_6890,plain,
    ( r1_tarski(k1_relat_1(sK9),sK7)
    | ~ r1_tarski(sK7,k1_relat_1(sK9)) ),
    inference(resolution,[status(thm)],[c_4755,c_27])).

cnf(c_6891,plain,
    ( r1_tarski(k1_relat_1(sK9),sK7) = iProver_top
    | r1_tarski(sK7,k1_relat_1(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6890])).

cnf(c_2212,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_581,c_579])).

cnf(c_4747,plain,
    ( ~ r1_tarski(k1_relat_1(sK9),X0)
    | r1_tarski(sK7,X0) ),
    inference(resolution,[status(thm)],[c_4479,c_2212])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_4894,plain,
    ( r1_tarski(sK7,k1_relat_1(sK9)) ),
    inference(resolution,[status(thm)],[c_4747,c_5])).

cnf(c_4895,plain,
    ( r1_tarski(sK7,k1_relat_1(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4894])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_3862,plain,
    ( ~ r2_hidden(sK0(k2_relat_1(sK9),sK8),sK8)
    | r1_tarski(k2_relat_1(sK9),sK8) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3865,plain,
    ( r2_hidden(sK0(k2_relat_1(sK9),sK8),sK8) != iProver_top
    | r1_tarski(k2_relat_1(sK9),sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3862])).

cnf(c_1691,plain,
    ( r2_hidden(sK6(sK9,sK0(k2_relat_1(sK9),sK8)),k1_relat_1(sK9))
    | ~ r2_hidden(k4_tarski(sK6(sK9,sK0(k2_relat_1(sK9),sK8)),sK0(k2_relat_1(sK9),sK8)),sK9) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1692,plain,
    ( r2_hidden(sK6(sK9,sK0(k2_relat_1(sK9),sK8)),k1_relat_1(sK9)) = iProver_top
    | r2_hidden(k4_tarski(sK6(sK9,sK0(k2_relat_1(sK9),sK8)),sK0(k2_relat_1(sK9),sK8)),sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1691])).

cnf(c_1101,plain,
    ( r2_hidden(k4_tarski(sK6(sK9,sK0(k2_relat_1(sK9),sK8)),sK0(k2_relat_1(sK9),sK8)),sK9)
    | ~ r2_hidden(sK0(k2_relat_1(sK9),sK8),k2_relat_1(sK9)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1102,plain,
    ( r2_hidden(k4_tarski(sK6(sK9,sK0(k2_relat_1(sK9),sK8)),sK0(k2_relat_1(sK9),sK8)),sK9) = iProver_top
    | r2_hidden(sK0(k2_relat_1(sK9),sK8),k2_relat_1(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1101])).

cnf(c_1026,plain,
    ( r2_hidden(sK0(k2_relat_1(sK9),sK8),k2_relat_1(sK9))
    | r1_tarski(k2_relat_1(sK9),sK8) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1027,plain,
    ( r2_hidden(sK0(k2_relat_1(sK9),sK8),k2_relat_1(sK9)) = iProver_top
    | r1_tarski(k2_relat_1(sK9),sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1026])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_109847,c_34337,c_6891,c_4895,c_3865,c_2034,c_1692,c_1102,c_1027])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:53:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 31.47/4.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.47/4.50  
% 31.47/4.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.47/4.50  
% 31.47/4.50  ------  iProver source info
% 31.47/4.50  
% 31.47/4.50  git: date: 2020-06-30 10:37:57 +0100
% 31.47/4.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.47/4.50  git: non_committed_changes: false
% 31.47/4.50  git: last_make_outside_of_git: false
% 31.47/4.50  
% 31.47/4.50  ------ 
% 31.47/4.50  ------ Parsing...
% 31.47/4.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.47/4.50  
% 31.47/4.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 31.47/4.50  
% 31.47/4.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.47/4.50  
% 31.47/4.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.47/4.50  ------ Proving...
% 31.47/4.50  ------ Problem Properties 
% 31.47/4.50  
% 31.47/4.50  
% 31.47/4.50  clauses                                 20
% 31.47/4.50  conjectures                             2
% 31.47/4.50  EPR                                     3
% 31.47/4.50  Horn                                    16
% 31.47/4.50  unary                                   2
% 31.47/4.50  binary                                  10
% 31.47/4.50  lits                                    47
% 31.47/4.50  lits eq                                 10
% 31.47/4.50  fd_pure                                 0
% 31.47/4.50  fd_pseudo                               0
% 31.47/4.50  fd_cond                                 0
% 31.47/4.50  fd_pseudo_cond                          6
% 31.47/4.50  AC symbols                              0
% 31.47/4.50  
% 31.47/4.50  ------ Input Options Time Limit: Unbounded
% 31.47/4.50  
% 31.47/4.50  
% 31.47/4.50  ------ 
% 31.47/4.50  Current options:
% 31.47/4.50  ------ 
% 31.47/4.50  
% 31.47/4.50  
% 31.47/4.50  
% 31.47/4.50  
% 31.47/4.50  ------ Proving...
% 31.47/4.50  
% 31.47/4.50  
% 31.47/4.50  % SZS status Theorem for theBenchmark.p
% 31.47/4.50  
% 31.47/4.50  % SZS output start CNFRefutation for theBenchmark.p
% 31.47/4.50  
% 31.47/4.50  fof(f1,axiom,(
% 31.47/4.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 31.47/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.47/4.50  
% 31.47/4.50  fof(f11,plain,(
% 31.47/4.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 31.47/4.50    inference(ennf_transformation,[],[f1])).
% 31.47/4.50  
% 31.47/4.50  fof(f22,plain,(
% 31.47/4.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 31.47/4.50    inference(nnf_transformation,[],[f11])).
% 31.47/4.50  
% 31.47/4.50  fof(f23,plain,(
% 31.47/4.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 31.47/4.50    inference(rectify,[],[f22])).
% 31.47/4.50  
% 31.47/4.50  fof(f24,plain,(
% 31.47/4.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 31.47/4.50    introduced(choice_axiom,[])).
% 31.47/4.50  
% 31.47/4.50  fof(f25,plain,(
% 31.47/4.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 31.47/4.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 31.47/4.50  
% 31.47/4.50  fof(f46,plain,(
% 31.47/4.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 31.47/4.50    inference(cnf_transformation,[],[f25])).
% 31.47/4.50  
% 31.47/4.50  fof(f4,axiom,(
% 31.47/4.50    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 31.47/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.47/4.50  
% 31.47/4.50  fof(f34,plain,(
% 31.47/4.50    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 31.47/4.50    inference(nnf_transformation,[],[f4])).
% 31.47/4.50  
% 31.47/4.50  fof(f35,plain,(
% 31.47/4.50    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 31.47/4.50    inference(rectify,[],[f34])).
% 31.47/4.50  
% 31.47/4.50  fof(f38,plain,(
% 31.47/4.50    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK6(X0,X5),X5),X0))),
% 31.47/4.50    introduced(choice_axiom,[])).
% 31.47/4.50  
% 31.47/4.50  fof(f37,plain,(
% 31.47/4.50    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK5(X0,X1),X2),X0))) )),
% 31.47/4.50    introduced(choice_axiom,[])).
% 31.47/4.50  
% 31.47/4.50  fof(f36,plain,(
% 31.47/4.50    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 31.47/4.50    introduced(choice_axiom,[])).
% 31.47/4.50  
% 31.47/4.50  fof(f39,plain,(
% 31.47/4.50    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 31.47/4.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f35,f38,f37,f36])).
% 31.47/4.50  
% 31.47/4.50  fof(f55,plain,(
% 31.47/4.50    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 31.47/4.50    inference(cnf_transformation,[],[f39])).
% 31.47/4.50  
% 31.47/4.50  fof(f80,plain,(
% 31.47/4.50    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 31.47/4.50    inference(equality_resolution,[],[f55])).
% 31.47/4.50  
% 31.47/4.50  fof(f5,axiom,(
% 31.47/4.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 31.47/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.47/4.50  
% 31.47/4.50  fof(f12,plain,(
% 31.47/4.50    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 31.47/4.50    inference(ennf_transformation,[],[f5])).
% 31.47/4.50  
% 31.47/4.50  fof(f13,plain,(
% 31.47/4.50    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 31.47/4.50    inference(flattening,[],[f12])).
% 31.47/4.50  
% 31.47/4.50  fof(f40,plain,(
% 31.47/4.50    ! [X0] : (! [X1,X2] : ((((k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2)) | r2_hidden(X1,k1_relat_1(X0))) & (((k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0)) & (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 31.47/4.50    inference(nnf_transformation,[],[f13])).
% 31.47/4.50  
% 31.47/4.50  fof(f60,plain,(
% 31.47/4.50    ( ! [X2,X0,X1] : (k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 31.47/4.50    inference(cnf_transformation,[],[f40])).
% 31.47/4.50  
% 31.47/4.50  fof(f3,axiom,(
% 31.47/4.50    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 31.47/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.47/4.50  
% 31.47/4.50  fof(f28,plain,(
% 31.47/4.50    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 31.47/4.50    inference(nnf_transformation,[],[f3])).
% 31.47/4.50  
% 31.47/4.50  fof(f29,plain,(
% 31.47/4.50    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 31.47/4.50    inference(rectify,[],[f28])).
% 31.47/4.50  
% 31.47/4.50  fof(f32,plain,(
% 31.47/4.50    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0))),
% 31.47/4.50    introduced(choice_axiom,[])).
% 31.47/4.50  
% 31.47/4.50  fof(f31,plain,(
% 31.47/4.50    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0))) )),
% 31.47/4.50    introduced(choice_axiom,[])).
% 31.47/4.50  
% 31.47/4.50  fof(f30,plain,(
% 31.47/4.50    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 31.47/4.50    introduced(choice_axiom,[])).
% 31.47/4.50  
% 31.47/4.50  fof(f33,plain,(
% 31.47/4.50    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 31.47/4.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f29,f32,f31,f30])).
% 31.47/4.50  
% 31.47/4.50  fof(f52,plain,(
% 31.47/4.50    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 31.47/4.50    inference(cnf_transformation,[],[f33])).
% 31.47/4.50  
% 31.47/4.50  fof(f77,plain,(
% 31.47/4.50    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 31.47/4.50    inference(equality_resolution,[],[f52])).
% 31.47/4.50  
% 31.47/4.50  fof(f9,conjecture,(
% 31.47/4.50    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 31.47/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.47/4.50  
% 31.47/4.50  fof(f10,negated_conjecture,(
% 31.47/4.50    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 31.47/4.50    inference(negated_conjecture,[],[f9])).
% 31.47/4.50  
% 31.47/4.50  fof(f20,plain,(
% 31.47/4.50    ? [X0,X1,X2] : (((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & (! [X3] : (r2_hidden(k1_funct_1(X2,X3),X1) | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 31.47/4.50    inference(ennf_transformation,[],[f10])).
% 31.47/4.50  
% 31.47/4.50  fof(f21,plain,(
% 31.47/4.50    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & ! [X3] : (r2_hidden(k1_funct_1(X2,X3),X1) | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 31.47/4.50    inference(flattening,[],[f20])).
% 31.47/4.50  
% 31.47/4.50  fof(f43,plain,(
% 31.47/4.50    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & ! [X3] : (r2_hidden(k1_funct_1(X2,X3),X1) | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => ((~m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) | ~v1_funct_2(sK9,sK7,sK8) | ~v1_funct_1(sK9)) & ! [X3] : (r2_hidden(k1_funct_1(sK9,X3),sK8) | ~r2_hidden(X3,sK7)) & k1_relat_1(sK9) = sK7 & v1_funct_1(sK9) & v1_relat_1(sK9))),
% 31.47/4.50    introduced(choice_axiom,[])).
% 31.47/4.50  
% 31.47/4.50  fof(f44,plain,(
% 31.47/4.50    (~m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) | ~v1_funct_2(sK9,sK7,sK8) | ~v1_funct_1(sK9)) & ! [X3] : (r2_hidden(k1_funct_1(sK9,X3),sK8) | ~r2_hidden(X3,sK7)) & k1_relat_1(sK9) = sK7 & v1_funct_1(sK9) & v1_relat_1(sK9)),
% 31.47/4.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f21,f43])).
% 31.47/4.50  
% 31.47/4.50  fof(f71,plain,(
% 31.47/4.50    v1_funct_1(sK9)),
% 31.47/4.50    inference(cnf_transformation,[],[f44])).
% 31.47/4.50  
% 31.47/4.50  fof(f70,plain,(
% 31.47/4.50    v1_relat_1(sK9)),
% 31.47/4.50    inference(cnf_transformation,[],[f44])).
% 31.47/4.50  
% 31.47/4.50  fof(f72,plain,(
% 31.47/4.50    k1_relat_1(sK9) = sK7),
% 31.47/4.50    inference(cnf_transformation,[],[f44])).
% 31.47/4.50  
% 31.47/4.50  fof(f8,axiom,(
% 31.47/4.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 31.47/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.47/4.50  
% 31.47/4.50  fof(f18,plain,(
% 31.47/4.50    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 31.47/4.50    inference(ennf_transformation,[],[f8])).
% 31.47/4.50  
% 31.47/4.50  fof(f19,plain,(
% 31.47/4.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 31.47/4.50    inference(flattening,[],[f18])).
% 31.47/4.50  
% 31.47/4.50  fof(f69,plain,(
% 31.47/4.50    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 31.47/4.50    inference(cnf_transformation,[],[f19])).
% 31.47/4.50  
% 31.47/4.50  fof(f68,plain,(
% 31.47/4.50    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 31.47/4.50    inference(cnf_transformation,[],[f19])).
% 31.47/4.50  
% 31.47/4.50  fof(f74,plain,(
% 31.47/4.50    ~m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) | ~v1_funct_2(sK9,sK7,sK8) | ~v1_funct_1(sK9)),
% 31.47/4.50    inference(cnf_transformation,[],[f44])).
% 31.47/4.50  
% 31.47/4.50  fof(f73,plain,(
% 31.47/4.50    ( ! [X3] : (r2_hidden(k1_funct_1(sK9,X3),sK8) | ~r2_hidden(X3,sK7)) )),
% 31.47/4.50    inference(cnf_transformation,[],[f44])).
% 31.47/4.50  
% 31.47/4.50  fof(f45,plain,(
% 31.47/4.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 31.47/4.50    inference(cnf_transformation,[],[f25])).
% 31.47/4.50  
% 31.47/4.50  fof(f2,axiom,(
% 31.47/4.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 31.47/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.47/4.50  
% 31.47/4.50  fof(f26,plain,(
% 31.47/4.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 31.47/4.50    inference(nnf_transformation,[],[f2])).
% 31.47/4.50  
% 31.47/4.50  fof(f27,plain,(
% 31.47/4.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 31.47/4.50    inference(flattening,[],[f26])).
% 31.47/4.50  
% 31.47/4.50  fof(f48,plain,(
% 31.47/4.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 31.47/4.50    inference(cnf_transformation,[],[f27])).
% 31.47/4.50  
% 31.47/4.50  fof(f76,plain,(
% 31.47/4.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 31.47/4.50    inference(equality_resolution,[],[f48])).
% 31.47/4.50  
% 31.47/4.50  fof(f47,plain,(
% 31.47/4.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 31.47/4.50    inference(cnf_transformation,[],[f25])).
% 31.47/4.50  
% 31.47/4.50  cnf(c_1,plain,
% 31.47/4.50      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 31.47/4.50      inference(cnf_transformation,[],[f46]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_949,plain,
% 31.47/4.50      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 31.47/4.50      | r1_tarski(X0,X1) = iProver_top ),
% 31.47/4.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_13,plain,
% 31.47/4.50      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 31.47/4.50      | r2_hidden(k4_tarski(sK6(X1,X0),X0),X1) ),
% 31.47/4.50      inference(cnf_transformation,[],[f80]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_938,plain,
% 31.47/4.50      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 31.47/4.50      | r2_hidden(k4_tarski(sK6(X1,X0),X0),X1) = iProver_top ),
% 31.47/4.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_16,plain,
% 31.47/4.50      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 31.47/4.50      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 31.47/4.50      | ~ v1_relat_1(X1)
% 31.47/4.50      | ~ v1_funct_1(X1)
% 31.47/4.50      | k1_funct_1(X1,X0) = X2 ),
% 31.47/4.50      inference(cnf_transformation,[],[f60]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_8,plain,
% 31.47/4.50      ( r2_hidden(X0,k1_relat_1(X1)) | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
% 31.47/4.50      inference(cnf_transformation,[],[f77]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_175,plain,
% 31.47/4.50      ( ~ r2_hidden(k4_tarski(X0,X2),X1)
% 31.47/4.50      | ~ v1_relat_1(X1)
% 31.47/4.50      | ~ v1_funct_1(X1)
% 31.47/4.50      | k1_funct_1(X1,X0) = X2 ),
% 31.47/4.50      inference(global_propositional_subsumption,
% 31.47/4.50                [status(thm)],
% 31.47/4.50                [c_16,c_8]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_176,plain,
% 31.47/4.50      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 31.47/4.50      | ~ v1_relat_1(X2)
% 31.47/4.50      | ~ v1_funct_1(X2)
% 31.47/4.50      | k1_funct_1(X2,X0) = X1 ),
% 31.47/4.50      inference(renaming,[status(thm)],[c_175]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_28,negated_conjecture,
% 31.47/4.50      ( v1_funct_1(sK9) ),
% 31.47/4.50      inference(cnf_transformation,[],[f71]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_416,plain,
% 31.47/4.50      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 31.47/4.50      | ~ v1_relat_1(X2)
% 31.47/4.50      | k1_funct_1(X2,X0) = X1
% 31.47/4.50      | sK9 != X2 ),
% 31.47/4.50      inference(resolution_lifted,[status(thm)],[c_176,c_28]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_417,plain,
% 31.47/4.50      ( ~ r2_hidden(k4_tarski(X0,X1),sK9)
% 31.47/4.50      | ~ v1_relat_1(sK9)
% 31.47/4.50      | k1_funct_1(sK9,X0) = X1 ),
% 31.47/4.50      inference(unflattening,[status(thm)],[c_416]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_29,negated_conjecture,
% 31.47/4.50      ( v1_relat_1(sK9) ),
% 31.47/4.50      inference(cnf_transformation,[],[f70]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_421,plain,
% 31.47/4.50      ( ~ r2_hidden(k4_tarski(X0,X1),sK9) | k1_funct_1(sK9,X0) = X1 ),
% 31.47/4.50      inference(global_propositional_subsumption,
% 31.47/4.50                [status(thm)],
% 31.47/4.50                [c_417,c_29]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_932,plain,
% 31.47/4.50      ( k1_funct_1(sK9,X0) = X1
% 31.47/4.50      | r2_hidden(k4_tarski(X0,X1),sK9) != iProver_top ),
% 31.47/4.50      inference(predicate_to_equality,[status(thm)],[c_421]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_1383,plain,
% 31.47/4.50      ( k1_funct_1(sK9,sK6(sK9,X0)) = X0
% 31.47/4.50      | r2_hidden(X0,k2_relat_1(sK9)) != iProver_top ),
% 31.47/4.50      inference(superposition,[status(thm)],[c_938,c_932]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_2821,plain,
% 31.47/4.50      ( k1_funct_1(sK9,sK6(sK9,sK0(k2_relat_1(sK9),X0))) = sK0(k2_relat_1(sK9),X0)
% 31.47/4.50      | r1_tarski(k2_relat_1(sK9),X0) = iProver_top ),
% 31.47/4.50      inference(superposition,[status(thm)],[c_949,c_1383]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_27,negated_conjecture,
% 31.47/4.50      ( k1_relat_1(sK9) = sK7 ),
% 31.47/4.50      inference(cnf_transformation,[],[f72]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_22,plain,
% 31.47/4.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 31.47/4.50      | ~ r1_tarski(k2_relat_1(X0),X1)
% 31.47/4.50      | ~ v1_relat_1(X0)
% 31.47/4.50      | ~ v1_funct_1(X0) ),
% 31.47/4.50      inference(cnf_transformation,[],[f69]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_23,plain,
% 31.47/4.50      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 31.47/4.50      | ~ r1_tarski(k2_relat_1(X0),X1)
% 31.47/4.50      | ~ v1_relat_1(X0)
% 31.47/4.50      | ~ v1_funct_1(X0) ),
% 31.47/4.50      inference(cnf_transformation,[],[f68]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_25,negated_conjecture,
% 31.47/4.50      ( ~ v1_funct_2(sK9,sK7,sK8)
% 31.47/4.50      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 31.47/4.50      | ~ v1_funct_1(sK9) ),
% 31.47/4.50      inference(cnf_transformation,[],[f74]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_159,plain,
% 31.47/4.50      ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 31.47/4.50      | ~ v1_funct_2(sK9,sK7,sK8) ),
% 31.47/4.50      inference(global_propositional_subsumption,
% 31.47/4.50                [status(thm)],
% 31.47/4.50                [c_25,c_28]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_160,negated_conjecture,
% 31.47/4.50      ( ~ v1_funct_2(sK9,sK7,sK8)
% 31.47/4.50      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) ),
% 31.47/4.50      inference(renaming,[status(thm)],[c_159]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_309,plain,
% 31.47/4.50      ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 31.47/4.50      | ~ r1_tarski(k2_relat_1(X0),X1)
% 31.47/4.50      | ~ v1_relat_1(X0)
% 31.47/4.50      | ~ v1_funct_1(X0)
% 31.47/4.50      | k1_relat_1(X0) != sK7
% 31.47/4.50      | sK8 != X1
% 31.47/4.50      | sK9 != X0 ),
% 31.47/4.50      inference(resolution_lifted,[status(thm)],[c_23,c_160]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_310,plain,
% 31.47/4.50      ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 31.47/4.50      | ~ r1_tarski(k2_relat_1(sK9),sK8)
% 31.47/4.50      | ~ v1_relat_1(sK9)
% 31.47/4.50      | ~ v1_funct_1(sK9)
% 31.47/4.50      | k1_relat_1(sK9) != sK7 ),
% 31.47/4.50      inference(unflattening,[status(thm)],[c_309]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_312,plain,
% 31.47/4.50      ( ~ r1_tarski(k2_relat_1(sK9),sK8)
% 31.47/4.50      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) ),
% 31.47/4.50      inference(global_propositional_subsumption,
% 31.47/4.50                [status(thm)],
% 31.47/4.50                [c_310,c_29,c_28,c_27]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_313,plain,
% 31.47/4.50      ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 31.47/4.50      | ~ r1_tarski(k2_relat_1(sK9),sK8) ),
% 31.47/4.50      inference(renaming,[status(thm)],[c_312]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_350,plain,
% 31.47/4.50      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 31.47/4.50      | ~ r1_tarski(k2_relat_1(sK9),sK8)
% 31.47/4.50      | ~ v1_relat_1(X0)
% 31.47/4.50      | ~ v1_funct_1(X0)
% 31.47/4.50      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)) != k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))
% 31.47/4.50      | sK9 != X0 ),
% 31.47/4.50      inference(resolution_lifted,[status(thm)],[c_22,c_313]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_351,plain,
% 31.47/4.50      ( ~ r1_tarski(k2_relat_1(sK9),X0)
% 31.47/4.50      | ~ r1_tarski(k2_relat_1(sK9),sK8)
% 31.47/4.50      | ~ v1_relat_1(sK9)
% 31.47/4.50      | ~ v1_funct_1(sK9)
% 31.47/4.50      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK9),X0)) != k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)) ),
% 31.47/4.50      inference(unflattening,[status(thm)],[c_350]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_355,plain,
% 31.47/4.50      ( ~ r1_tarski(k2_relat_1(sK9),X0)
% 31.47/4.50      | ~ r1_tarski(k2_relat_1(sK9),sK8)
% 31.47/4.50      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK9),X0)) != k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)) ),
% 31.47/4.50      inference(global_propositional_subsumption,
% 31.47/4.50                [status(thm)],
% 31.47/4.50                [c_351,c_29,c_28]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_935,plain,
% 31.47/4.50      ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK9),X0)) != k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))
% 31.47/4.50      | r1_tarski(k2_relat_1(sK9),X0) != iProver_top
% 31.47/4.50      | r1_tarski(k2_relat_1(sK9),sK8) != iProver_top ),
% 31.47/4.50      inference(predicate_to_equality,[status(thm)],[c_355]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_1567,plain,
% 31.47/4.50      ( k1_zfmisc_1(k2_zfmisc_1(sK7,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))
% 31.47/4.50      | r1_tarski(k2_relat_1(sK9),X0) != iProver_top
% 31.47/4.50      | r1_tarski(k2_relat_1(sK9),sK8) != iProver_top ),
% 31.47/4.50      inference(superposition,[status(thm)],[c_27,c_935]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_2034,plain,
% 31.47/4.50      ( r1_tarski(k2_relat_1(sK9),sK8) != iProver_top ),
% 31.47/4.50      inference(equality_resolution,[status(thm)],[c_1567]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_5725,plain,
% 31.47/4.50      ( k1_funct_1(sK9,sK6(sK9,sK0(k2_relat_1(sK9),sK8))) = sK0(k2_relat_1(sK9),sK8) ),
% 31.47/4.50      inference(superposition,[status(thm)],[c_2821,c_2034]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_26,negated_conjecture,
% 31.47/4.50      ( ~ r2_hidden(X0,sK7) | r2_hidden(k1_funct_1(sK9,X0),sK8) ),
% 31.47/4.50      inference(cnf_transformation,[],[f73]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_937,plain,
% 31.47/4.50      ( r2_hidden(X0,sK7) != iProver_top
% 31.47/4.50      | r2_hidden(k1_funct_1(sK9,X0),sK8) = iProver_top ),
% 31.47/4.50      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_109847,plain,
% 31.47/4.50      ( r2_hidden(sK6(sK9,sK0(k2_relat_1(sK9),sK8)),sK7) != iProver_top
% 31.47/4.50      | r2_hidden(sK0(k2_relat_1(sK9),sK8),sK8) = iProver_top ),
% 31.47/4.50      inference(superposition,[status(thm)],[c_5725,c_937]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_2,plain,
% 31.47/4.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 31.47/4.50      inference(cnf_transformation,[],[f45]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_4899,plain,
% 31.47/4.50      ( r2_hidden(sK6(sK9,sK0(k2_relat_1(sK9),sK8)),X0)
% 31.47/4.50      | ~ r2_hidden(sK6(sK9,sK0(k2_relat_1(sK9),sK8)),k1_relat_1(sK9))
% 31.47/4.50      | ~ r1_tarski(k1_relat_1(sK9),X0) ),
% 31.47/4.50      inference(instantiation,[status(thm)],[c_2]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_34336,plain,
% 31.47/4.50      ( ~ r2_hidden(sK6(sK9,sK0(k2_relat_1(sK9),sK8)),k1_relat_1(sK9))
% 31.47/4.50      | r2_hidden(sK6(sK9,sK0(k2_relat_1(sK9),sK8)),sK7)
% 31.47/4.50      | ~ r1_tarski(k1_relat_1(sK9),sK7) ),
% 31.47/4.50      inference(instantiation,[status(thm)],[c_4899]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_34337,plain,
% 31.47/4.50      ( r2_hidden(sK6(sK9,sK0(k2_relat_1(sK9),sK8)),k1_relat_1(sK9)) != iProver_top
% 31.47/4.50      | r2_hidden(sK6(sK9,sK0(k2_relat_1(sK9),sK8)),sK7) = iProver_top
% 31.47/4.50      | r1_tarski(k1_relat_1(sK9),sK7) != iProver_top ),
% 31.47/4.50      inference(predicate_to_equality,[status(thm)],[c_34336]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_580,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_579,plain,( X0 = X0 ),theory(equality) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_2181,plain,
% 31.47/4.50      ( X0 != X1 | X1 = X0 ),
% 31.47/4.50      inference(resolution,[status(thm)],[c_580,c_579]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_4479,plain,
% 31.47/4.50      ( sK7 = k1_relat_1(sK9) ),
% 31.47/4.50      inference(resolution,[status(thm)],[c_2181,c_27]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_581,plain,
% 31.47/4.50      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 31.47/4.50      theory(equality) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_4755,plain,
% 31.47/4.50      ( ~ r1_tarski(X0,k1_relat_1(sK9)) | r1_tarski(X1,sK7) | X1 != X0 ),
% 31.47/4.50      inference(resolution,[status(thm)],[c_4479,c_581]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_6890,plain,
% 31.47/4.50      ( r1_tarski(k1_relat_1(sK9),sK7)
% 31.47/4.50      | ~ r1_tarski(sK7,k1_relat_1(sK9)) ),
% 31.47/4.50      inference(resolution,[status(thm)],[c_4755,c_27]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_6891,plain,
% 31.47/4.50      ( r1_tarski(k1_relat_1(sK9),sK7) = iProver_top
% 31.47/4.50      | r1_tarski(sK7,k1_relat_1(sK9)) != iProver_top ),
% 31.47/4.50      inference(predicate_to_equality,[status(thm)],[c_6890]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_2212,plain,
% 31.47/4.50      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 31.47/4.50      inference(resolution,[status(thm)],[c_581,c_579]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_4747,plain,
% 31.47/4.50      ( ~ r1_tarski(k1_relat_1(sK9),X0) | r1_tarski(sK7,X0) ),
% 31.47/4.50      inference(resolution,[status(thm)],[c_4479,c_2212]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_5,plain,
% 31.47/4.50      ( r1_tarski(X0,X0) ),
% 31.47/4.50      inference(cnf_transformation,[],[f76]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_4894,plain,
% 31.47/4.50      ( r1_tarski(sK7,k1_relat_1(sK9)) ),
% 31.47/4.50      inference(resolution,[status(thm)],[c_4747,c_5]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_4895,plain,
% 31.47/4.50      ( r1_tarski(sK7,k1_relat_1(sK9)) = iProver_top ),
% 31.47/4.50      inference(predicate_to_equality,[status(thm)],[c_4894]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_0,plain,
% 31.47/4.50      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 31.47/4.50      inference(cnf_transformation,[],[f47]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_3862,plain,
% 31.47/4.50      ( ~ r2_hidden(sK0(k2_relat_1(sK9),sK8),sK8)
% 31.47/4.50      | r1_tarski(k2_relat_1(sK9),sK8) ),
% 31.47/4.50      inference(instantiation,[status(thm)],[c_0]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_3865,plain,
% 31.47/4.50      ( r2_hidden(sK0(k2_relat_1(sK9),sK8),sK8) != iProver_top
% 31.47/4.50      | r1_tarski(k2_relat_1(sK9),sK8) = iProver_top ),
% 31.47/4.50      inference(predicate_to_equality,[status(thm)],[c_3862]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_1691,plain,
% 31.47/4.50      ( r2_hidden(sK6(sK9,sK0(k2_relat_1(sK9),sK8)),k1_relat_1(sK9))
% 31.47/4.50      | ~ r2_hidden(k4_tarski(sK6(sK9,sK0(k2_relat_1(sK9),sK8)),sK0(k2_relat_1(sK9),sK8)),sK9) ),
% 31.47/4.50      inference(instantiation,[status(thm)],[c_8]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_1692,plain,
% 31.47/4.50      ( r2_hidden(sK6(sK9,sK0(k2_relat_1(sK9),sK8)),k1_relat_1(sK9)) = iProver_top
% 31.47/4.50      | r2_hidden(k4_tarski(sK6(sK9,sK0(k2_relat_1(sK9),sK8)),sK0(k2_relat_1(sK9),sK8)),sK9) != iProver_top ),
% 31.47/4.50      inference(predicate_to_equality,[status(thm)],[c_1691]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_1101,plain,
% 31.47/4.50      ( r2_hidden(k4_tarski(sK6(sK9,sK0(k2_relat_1(sK9),sK8)),sK0(k2_relat_1(sK9),sK8)),sK9)
% 31.47/4.50      | ~ r2_hidden(sK0(k2_relat_1(sK9),sK8),k2_relat_1(sK9)) ),
% 31.47/4.50      inference(instantiation,[status(thm)],[c_13]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_1102,plain,
% 31.47/4.50      ( r2_hidden(k4_tarski(sK6(sK9,sK0(k2_relat_1(sK9),sK8)),sK0(k2_relat_1(sK9),sK8)),sK9) = iProver_top
% 31.47/4.50      | r2_hidden(sK0(k2_relat_1(sK9),sK8),k2_relat_1(sK9)) != iProver_top ),
% 31.47/4.50      inference(predicate_to_equality,[status(thm)],[c_1101]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_1026,plain,
% 31.47/4.50      ( r2_hidden(sK0(k2_relat_1(sK9),sK8),k2_relat_1(sK9))
% 31.47/4.50      | r1_tarski(k2_relat_1(sK9),sK8) ),
% 31.47/4.50      inference(instantiation,[status(thm)],[c_1]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(c_1027,plain,
% 31.47/4.50      ( r2_hidden(sK0(k2_relat_1(sK9),sK8),k2_relat_1(sK9)) = iProver_top
% 31.47/4.50      | r1_tarski(k2_relat_1(sK9),sK8) = iProver_top ),
% 31.47/4.50      inference(predicate_to_equality,[status(thm)],[c_1026]) ).
% 31.47/4.50  
% 31.47/4.50  cnf(contradiction,plain,
% 31.47/4.50      ( $false ),
% 31.47/4.50      inference(minisat,
% 31.47/4.50                [status(thm)],
% 31.47/4.50                [c_109847,c_34337,c_6891,c_4895,c_3865,c_2034,c_1692,
% 31.47/4.50                 c_1102,c_1027]) ).
% 31.47/4.50  
% 31.47/4.50  
% 31.47/4.50  % SZS output end CNFRefutation for theBenchmark.p
% 31.47/4.50  
% 31.47/4.50  ------                               Statistics
% 31.47/4.50  
% 31.47/4.50  ------ Selected
% 31.47/4.50  
% 31.47/4.50  total_time:                             3.755
% 31.47/4.50  
%------------------------------------------------------------------------------
