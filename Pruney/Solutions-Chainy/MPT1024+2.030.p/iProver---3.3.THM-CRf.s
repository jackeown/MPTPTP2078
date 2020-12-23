%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:53 EST 2020

% Result     : Theorem 2.87s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :  174 (6199 expanded)
%              Number of clauses        :  114 (1972 expanded)
%              Number of leaves         :   15 (1448 expanded)
%              Depth                    :   27
%              Number of atoms          :  564 (30942 expanded)
%              Number of equality atoms :  236 (6877 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ~ ( k1_funct_1(X3,X5) = X4
                  & r2_hidden(X5,X2)
                  & r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2)
                    & r2_hidden(X5,X0) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f21])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
     => ( ! [X5] :
            ( k1_funct_1(X3,X5) != sK6
            | ~ r2_hidden(X5,X2)
            | ~ r2_hidden(X5,X0) )
        & r2_hidden(sK6,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ! [X5] :
                ( k1_funct_1(X3,X5) != X4
                | ~ r2_hidden(X5,X2)
                | ~ r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(sK5,X5) != X4
              | ~ r2_hidden(X5,sK4)
              | ~ r2_hidden(X5,sK2) )
          & r2_hidden(X4,k7_relset_1(sK2,sK3,sK5,sK4)) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK5,sK2,sK3)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ! [X5] :
        ( k1_funct_1(sK5,X5) != sK6
        | ~ r2_hidden(X5,sK4)
        | ~ r2_hidden(X5,sK2) )
    & r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4))
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK5,sK2,sK3)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f22,f36,f35])).

fof(f63,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f64,plain,(
    r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4)) ),
    inference(cnf_transformation,[],[f37])).

fof(f9,axiom,(
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

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f62,plain,(
    v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
        & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
            & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

fof(f38,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f61,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f37])).

fof(f65,plain,(
    ! [X5] :
      ( k1_funct_1(sK5,X5) != sK6
      | ~ r2_hidden(X5,sK4)
      | ~ r2_hidden(X5,sK2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f69,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f59])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f39,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f71,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f56])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1795,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1798,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2546,plain,
    ( k7_relset_1(sK2,sK3,sK5,X0) = k9_relat_1(sK5,X0) ),
    inference(superposition,[status(thm)],[c_1795,c_1798])).

cnf(c_24,negated_conjecture,
    ( r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1796,plain,
    ( r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2747,plain,
    ( r2_hidden(sK6,k9_relat_1(sK5,sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2546,c_1796])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_556,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X2
    | sK2 != X1
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_26])).

cnf(c_557,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_relset_1(sK2,sK3,sK5) = sK2
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_556])).

cnf(c_559,plain,
    ( k1_relset_1(sK2,sK3,sK5) = sK2
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_557,c_25])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1799,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2542,plain,
    ( k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1795,c_1799])).

cnf(c_2742,plain,
    ( k1_relat_1(sK5) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_559,c_2542])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1801,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3136,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
    | r2_hidden(sK1(X0,X1,sK5),sK2) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2742,c_1801])).

cnf(c_30,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1989,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1990,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1989])).

cnf(c_3819,plain,
    ( r2_hidden(sK1(X0,X1,sK5),sK2) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3136,c_30,c_1990])).

cnf(c_3820,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
    | r2_hidden(sK1(X0,X1,sK5),sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_3819])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1809,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3829,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3820,c_1809])).

cnf(c_3986,plain,
    ( sK3 = k1_xboole_0
    | v1_xboole_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2747,c_3829])).

cnf(c_2756,plain,
    ( r2_hidden(sK6,k9_relat_1(sK5,sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2747])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1802,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_12,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_350,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_27])).

cnf(c_351,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK5)
    | ~ v1_relat_1(sK5)
    | k1_funct_1(sK5,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_350])).

cnf(c_1791,plain,
    ( k1_funct_1(sK5,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_351])).

cnf(c_352,plain,
    ( k1_funct_1(sK5,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_351])).

cnf(c_2021,plain,
    ( r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top
    | k1_funct_1(sK5,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1791,c_30,c_352,c_1990])).

cnf(c_2022,plain,
    ( k1_funct_1(sK5,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_2021])).

cnf(c_3186,plain,
    ( k1_funct_1(sK5,sK1(X0,X1,sK5)) = X0
    | r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1802,c_2022])).

cnf(c_3581,plain,
    ( r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
    | k1_funct_1(sK5,sK1(X0,X1,sK5)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3186,c_30,c_1990])).

cnf(c_3582,plain,
    ( k1_funct_1(sK5,sK1(X0,X1,sK5)) = X0
    | r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3581])).

cnf(c_3592,plain,
    ( k1_funct_1(sK5,sK1(sK6,sK4,sK5)) = sK6 ),
    inference(superposition,[status(thm)],[c_2747,c_3582])).

cnf(c_23,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | ~ r2_hidden(X0,sK4)
    | k1_funct_1(sK5,X0) != sK6 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1797,plain,
    ( k1_funct_1(sK5,X0) != sK6
    | r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3623,plain,
    ( r2_hidden(sK1(sK6,sK4,sK5),sK2) != iProver_top
    | r2_hidden(sK1(sK6,sK4,sK5),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3592,c_1797])).

cnf(c_3830,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK1(sK6,sK4,sK5),sK4) != iProver_top
    | r2_hidden(sK6,k9_relat_1(sK5,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3820,c_3623])).

cnf(c_3855,plain,
    ( ~ r2_hidden(sK1(sK6,sK4,sK5),sK4)
    | ~ r2_hidden(sK6,k9_relat_1(sK5,sK4))
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3830])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK1(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2061,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK5,X1))
    | r2_hidden(sK1(X0,X1,sK5),X1)
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_4186,plain,
    ( r2_hidden(sK1(sK6,sK4,sK5),sK4)
    | ~ r2_hidden(sK6,k9_relat_1(sK5,sK4))
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_2061])).

cnf(c_4252,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3986,c_25,c_1989,c_2756,c_3855,c_4186])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_523,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK3 != k1_xboole_0
    | sK2 != X1
    | sK5 != X0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_26])).

cnf(c_524,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | sK3 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_523])).

cnf(c_1790,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK5
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_524])).

cnf(c_4259,plain,
    ( sK2 = k1_xboole_0
    | sK5 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4252,c_1790])).

cnf(c_4271,plain,
    ( sK2 = k1_xboole_0
    | sK5 = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4259])).

cnf(c_4262,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4252,c_1795])).

cnf(c_4275,plain,
    ( sK2 = k1_xboole_0
    | sK5 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4271,c_4262])).

cnf(c_31,plain,
    ( r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_5,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_177,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5,c_1])).

cnf(c_178,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_177])).

cnf(c_683,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) != X1
    | sK3 != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK5 != X0
    | sK5 = k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_178,c_524])).

cnf(c_684,plain,
    ( ~ r2_hidden(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | sK3 != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK5 = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_683])).

cnf(c_685,plain,
    ( sK3 != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK5 = k1_xboole_0
    | r2_hidden(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_684])).

cnf(c_1981,plain,
    ( ~ r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4))
    | ~ v1_xboole_0(k7_relset_1(sK2,sK3,sK5,sK4)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1982,plain,
    ( r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4)) != iProver_top
    | v1_xboole_0(k7_relset_1(sK2,sK3,sK5,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1981])).

cnf(c_1393,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2050,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k7_relset_1(sK2,sK3,sK5,sK4))
    | k7_relset_1(sK2,sK3,sK5,sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_1393])).

cnf(c_2208,plain,
    ( v1_xboole_0(k7_relset_1(sK2,sK3,sK5,sK4))
    | ~ v1_xboole_0(k9_relat_1(sK5,sK4))
    | k7_relset_1(sK2,sK3,sK5,sK4) != k9_relat_1(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_2050])).

cnf(c_2210,plain,
    ( k7_relset_1(sK2,sK3,sK5,sK4) != k9_relat_1(sK5,sK4)
    | v1_xboole_0(k7_relset_1(sK2,sK3,sK5,sK4)) = iProver_top
    | v1_xboole_0(k9_relat_1(sK5,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2208])).

cnf(c_2035,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k7_relset_1(sK2,sK3,sK5,X0) = k9_relat_1(sK5,X0) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2209,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k7_relset_1(sK2,sK3,sK5,sK4) = k9_relat_1(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_2035])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_2396,plain,
    ( r2_hidden(sK0(k9_relat_1(sK5,sK4)),k9_relat_1(sK5,sK4))
    | v1_xboole_0(k9_relat_1(sK5,sK4)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2397,plain,
    ( r2_hidden(sK0(k9_relat_1(sK5,sK4)),k9_relat_1(sK5,sK4)) = iProver_top
    | v1_xboole_0(k9_relat_1(sK5,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2396])).

cnf(c_2059,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK5,X1))
    | r2_hidden(k4_tarski(sK1(X0,X1,sK5),X0),sK5)
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2730,plain,
    ( r2_hidden(k4_tarski(sK1(sK0(k9_relat_1(sK5,sK4)),sK4,sK5),sK0(k9_relat_1(sK5,sK4))),sK5)
    | ~ r2_hidden(sK0(k9_relat_1(sK5,sK4)),k9_relat_1(sK5,sK4))
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_2059])).

cnf(c_2734,plain,
    ( r2_hidden(k4_tarski(sK1(sK0(k9_relat_1(sK5,sK4)),sK4,sK5),sK0(k9_relat_1(sK5,sK4))),sK5) = iProver_top
    | r2_hidden(sK0(k9_relat_1(sK5,sK4)),k9_relat_1(sK5,sK4)) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2730])).

cnf(c_3248,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK5)
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_1393])).

cnf(c_3250,plain,
    ( v1_xboole_0(sK5)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3248])).

cnf(c_3430,plain,
    ( ~ r2_hidden(k4_tarski(sK1(sK0(k9_relat_1(sK5,sK4)),sK4,sK5),sK0(k9_relat_1(sK5,sK4))),sK5)
    | ~ v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3431,plain,
    ( r2_hidden(k4_tarski(sK1(sK0(k9_relat_1(sK5,sK4)),sK4,sK5),sK0(k9_relat_1(sK5,sK4))),sK5) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3430])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1805,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2597,plain,
    ( r2_hidden(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1795,c_1805])).

cnf(c_4255,plain,
    ( r2_hidden(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4252,c_2597])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1806,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2609,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1795,c_1806])).

cnf(c_4256,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4252,c_2609])).

cnf(c_4661,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4275,c_25,c_30,c_24,c_31,c_2,c_685,c_1981,c_1982,c_1989,c_1990,c_2208,c_2210,c_2209,c_2396,c_2397,c_2730,c_2734,c_2756,c_3250,c_3430,c_3431,c_3855,c_4186,c_4255,c_4256])).

cnf(c_4258,plain,
    ( k1_relset_1(sK2,k1_xboole_0,sK5) = k1_relat_1(sK5) ),
    inference(demodulation,[status(thm)],[c_4252,c_2542])).

cnf(c_4666,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_relat_1(sK5) ),
    inference(demodulation,[status(thm)],[c_4661,c_4258])).

cnf(c_4667,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4661,c_4262])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_543,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK3 != X1
    | sK2 != k1_xboole_0
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_26])).

cnf(c_544,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
    | k1_relset_1(k1_xboole_0,sK3,sK5) = k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_543])).

cnf(c_1789,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK5) = k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_544])).

cnf(c_4260,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4252,c_1789])).

cnf(c_4440,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4260,c_25,c_30,c_24,c_31,c_2,c_685,c_1981,c_1982,c_1989,c_1990,c_2208,c_2210,c_2209,c_2396,c_2397,c_2730,c_2734,c_2756,c_3250,c_3430,c_3431,c_3855,c_4186,c_4255,c_4256])).

cnf(c_4750,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4667,c_4440])).

cnf(c_4922,plain,
    ( k1_relat_1(sK5) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4666,c_4750])).

cnf(c_4377,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k1_relat_1(sK5))
    | k1_relat_1(sK5) != X0 ),
    inference(instantiation,[status(thm)],[c_1393])).

cnf(c_4379,plain,
    ( v1_xboole_0(k1_relat_1(sK5))
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_relat_1(sK5) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4377])).

cnf(c_3449,plain,
    ( ~ r2_hidden(sK1(sK0(k9_relat_1(sK5,sK4)),sK4,sK5),k1_relat_1(sK5))
    | ~ v1_xboole_0(k1_relat_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2060,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK5,X1))
    | r2_hidden(sK1(X0,X1,sK5),k1_relat_1(sK5))
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2731,plain,
    ( r2_hidden(sK1(sK0(k9_relat_1(sK5,sK4)),sK4,sK5),k1_relat_1(sK5))
    | ~ r2_hidden(sK0(k9_relat_1(sK5,sK4)),k9_relat_1(sK5,sK4))
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_2060])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4922,c_4379,c_3449,c_2731,c_2396,c_2209,c_2208,c_1989,c_1981,c_2,c_24,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:59:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.87/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.01  
% 2.87/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.87/1.01  
% 2.87/1.01  ------  iProver source info
% 2.87/1.01  
% 2.87/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.87/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.87/1.01  git: non_committed_changes: false
% 2.87/1.01  git: last_make_outside_of_git: false
% 2.87/1.01  
% 2.87/1.01  ------ 
% 2.87/1.01  
% 2.87/1.01  ------ Input Options
% 2.87/1.01  
% 2.87/1.01  --out_options                           all
% 2.87/1.01  --tptp_safe_out                         true
% 2.87/1.01  --problem_path                          ""
% 2.87/1.01  --include_path                          ""
% 2.87/1.01  --clausifier                            res/vclausify_rel
% 2.87/1.01  --clausifier_options                    --mode clausify
% 2.87/1.01  --stdin                                 false
% 2.87/1.01  --stats_out                             all
% 2.87/1.01  
% 2.87/1.01  ------ General Options
% 2.87/1.01  
% 2.87/1.01  --fof                                   false
% 2.87/1.01  --time_out_real                         305.
% 2.87/1.01  --time_out_virtual                      -1.
% 2.87/1.01  --symbol_type_check                     false
% 2.87/1.01  --clausify_out                          false
% 2.87/1.01  --sig_cnt_out                           false
% 2.87/1.01  --trig_cnt_out                          false
% 2.87/1.01  --trig_cnt_out_tolerance                1.
% 2.87/1.01  --trig_cnt_out_sk_spl                   false
% 2.87/1.01  --abstr_cl_out                          false
% 2.87/1.01  
% 2.87/1.01  ------ Global Options
% 2.87/1.01  
% 2.87/1.01  --schedule                              default
% 2.87/1.01  --add_important_lit                     false
% 2.87/1.01  --prop_solver_per_cl                    1000
% 2.87/1.01  --min_unsat_core                        false
% 2.87/1.01  --soft_assumptions                      false
% 2.87/1.01  --soft_lemma_size                       3
% 2.87/1.01  --prop_impl_unit_size                   0
% 2.87/1.01  --prop_impl_unit                        []
% 2.87/1.01  --share_sel_clauses                     true
% 2.87/1.01  --reset_solvers                         false
% 2.87/1.01  --bc_imp_inh                            [conj_cone]
% 2.87/1.01  --conj_cone_tolerance                   3.
% 2.87/1.01  --extra_neg_conj                        none
% 2.87/1.01  --large_theory_mode                     true
% 2.87/1.01  --prolific_symb_bound                   200
% 2.87/1.01  --lt_threshold                          2000
% 2.87/1.01  --clause_weak_htbl                      true
% 2.87/1.01  --gc_record_bc_elim                     false
% 2.87/1.01  
% 2.87/1.01  ------ Preprocessing Options
% 2.87/1.01  
% 2.87/1.01  --preprocessing_flag                    true
% 2.87/1.01  --time_out_prep_mult                    0.1
% 2.87/1.01  --splitting_mode                        input
% 2.87/1.01  --splitting_grd                         true
% 2.87/1.01  --splitting_cvd                         false
% 2.87/1.01  --splitting_cvd_svl                     false
% 2.87/1.01  --splitting_nvd                         32
% 2.87/1.01  --sub_typing                            true
% 2.87/1.01  --prep_gs_sim                           true
% 2.87/1.01  --prep_unflatten                        true
% 2.87/1.01  --prep_res_sim                          true
% 2.87/1.01  --prep_upred                            true
% 2.87/1.01  --prep_sem_filter                       exhaustive
% 2.87/1.01  --prep_sem_filter_out                   false
% 2.87/1.01  --pred_elim                             true
% 2.87/1.01  --res_sim_input                         true
% 2.87/1.01  --eq_ax_congr_red                       true
% 2.87/1.01  --pure_diseq_elim                       true
% 2.87/1.01  --brand_transform                       false
% 2.87/1.01  --non_eq_to_eq                          false
% 2.87/1.01  --prep_def_merge                        true
% 2.87/1.01  --prep_def_merge_prop_impl              false
% 2.87/1.01  --prep_def_merge_mbd                    true
% 2.87/1.01  --prep_def_merge_tr_red                 false
% 2.87/1.01  --prep_def_merge_tr_cl                  false
% 2.87/1.01  --smt_preprocessing                     true
% 2.87/1.01  --smt_ac_axioms                         fast
% 2.87/1.01  --preprocessed_out                      false
% 2.87/1.01  --preprocessed_stats                    false
% 2.87/1.01  
% 2.87/1.01  ------ Abstraction refinement Options
% 2.87/1.01  
% 2.87/1.01  --abstr_ref                             []
% 2.87/1.01  --abstr_ref_prep                        false
% 2.87/1.01  --abstr_ref_until_sat                   false
% 2.87/1.01  --abstr_ref_sig_restrict                funpre
% 2.87/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.87/1.01  --abstr_ref_under                       []
% 2.87/1.01  
% 2.87/1.01  ------ SAT Options
% 2.87/1.01  
% 2.87/1.01  --sat_mode                              false
% 2.87/1.01  --sat_fm_restart_options                ""
% 2.87/1.01  --sat_gr_def                            false
% 2.87/1.01  --sat_epr_types                         true
% 2.87/1.01  --sat_non_cyclic_types                  false
% 2.87/1.01  --sat_finite_models                     false
% 2.87/1.01  --sat_fm_lemmas                         false
% 2.87/1.01  --sat_fm_prep                           false
% 2.87/1.01  --sat_fm_uc_incr                        true
% 2.87/1.01  --sat_out_model                         small
% 2.87/1.01  --sat_out_clauses                       false
% 2.87/1.01  
% 2.87/1.01  ------ QBF Options
% 2.87/1.01  
% 2.87/1.01  --qbf_mode                              false
% 2.87/1.01  --qbf_elim_univ                         false
% 2.87/1.01  --qbf_dom_inst                          none
% 2.87/1.01  --qbf_dom_pre_inst                      false
% 2.87/1.01  --qbf_sk_in                             false
% 2.87/1.01  --qbf_pred_elim                         true
% 2.87/1.01  --qbf_split                             512
% 2.87/1.01  
% 2.87/1.01  ------ BMC1 Options
% 2.87/1.01  
% 2.87/1.01  --bmc1_incremental                      false
% 2.87/1.01  --bmc1_axioms                           reachable_all
% 2.87/1.01  --bmc1_min_bound                        0
% 2.87/1.01  --bmc1_max_bound                        -1
% 2.87/1.01  --bmc1_max_bound_default                -1
% 2.87/1.01  --bmc1_symbol_reachability              true
% 2.87/1.01  --bmc1_property_lemmas                  false
% 2.87/1.01  --bmc1_k_induction                      false
% 2.87/1.01  --bmc1_non_equiv_states                 false
% 2.87/1.01  --bmc1_deadlock                         false
% 2.87/1.01  --bmc1_ucm                              false
% 2.87/1.01  --bmc1_add_unsat_core                   none
% 2.87/1.01  --bmc1_unsat_core_children              false
% 2.87/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.87/1.01  --bmc1_out_stat                         full
% 2.87/1.01  --bmc1_ground_init                      false
% 2.87/1.01  --bmc1_pre_inst_next_state              false
% 2.87/1.01  --bmc1_pre_inst_state                   false
% 2.87/1.01  --bmc1_pre_inst_reach_state             false
% 2.87/1.01  --bmc1_out_unsat_core                   false
% 2.87/1.01  --bmc1_aig_witness_out                  false
% 2.87/1.01  --bmc1_verbose                          false
% 2.87/1.01  --bmc1_dump_clauses_tptp                false
% 2.87/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.87/1.01  --bmc1_dump_file                        -
% 2.87/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.87/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.87/1.01  --bmc1_ucm_extend_mode                  1
% 2.87/1.01  --bmc1_ucm_init_mode                    2
% 2.87/1.01  --bmc1_ucm_cone_mode                    none
% 2.87/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.87/1.01  --bmc1_ucm_relax_model                  4
% 2.87/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.87/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.87/1.01  --bmc1_ucm_layered_model                none
% 2.87/1.01  --bmc1_ucm_max_lemma_size               10
% 2.87/1.01  
% 2.87/1.01  ------ AIG Options
% 2.87/1.01  
% 2.87/1.01  --aig_mode                              false
% 2.87/1.01  
% 2.87/1.01  ------ Instantiation Options
% 2.87/1.01  
% 2.87/1.01  --instantiation_flag                    true
% 2.87/1.01  --inst_sos_flag                         false
% 2.87/1.01  --inst_sos_phase                        true
% 2.87/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.87/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.87/1.01  --inst_lit_sel_side                     num_symb
% 2.87/1.01  --inst_solver_per_active                1400
% 2.87/1.01  --inst_solver_calls_frac                1.
% 2.87/1.01  --inst_passive_queue_type               priority_queues
% 2.87/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.87/1.01  --inst_passive_queues_freq              [25;2]
% 2.87/1.01  --inst_dismatching                      true
% 2.87/1.01  --inst_eager_unprocessed_to_passive     true
% 2.87/1.01  --inst_prop_sim_given                   true
% 2.87/1.01  --inst_prop_sim_new                     false
% 2.87/1.01  --inst_subs_new                         false
% 2.87/1.01  --inst_eq_res_simp                      false
% 2.87/1.01  --inst_subs_given                       false
% 2.87/1.01  --inst_orphan_elimination               true
% 2.87/1.01  --inst_learning_loop_flag               true
% 2.87/1.01  --inst_learning_start                   3000
% 2.87/1.01  --inst_learning_factor                  2
% 2.87/1.01  --inst_start_prop_sim_after_learn       3
% 2.87/1.01  --inst_sel_renew                        solver
% 2.87/1.01  --inst_lit_activity_flag                true
% 2.87/1.01  --inst_restr_to_given                   false
% 2.87/1.01  --inst_activity_threshold               500
% 2.87/1.01  --inst_out_proof                        true
% 2.87/1.01  
% 2.87/1.01  ------ Resolution Options
% 2.87/1.01  
% 2.87/1.01  --resolution_flag                       true
% 2.87/1.01  --res_lit_sel                           adaptive
% 2.87/1.01  --res_lit_sel_side                      none
% 2.87/1.01  --res_ordering                          kbo
% 2.87/1.01  --res_to_prop_solver                    active
% 2.87/1.01  --res_prop_simpl_new                    false
% 2.87/1.01  --res_prop_simpl_given                  true
% 2.87/1.01  --res_passive_queue_type                priority_queues
% 2.87/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.87/1.01  --res_passive_queues_freq               [15;5]
% 2.87/1.01  --res_forward_subs                      full
% 2.87/1.01  --res_backward_subs                     full
% 2.87/1.01  --res_forward_subs_resolution           true
% 2.87/1.01  --res_backward_subs_resolution          true
% 2.87/1.01  --res_orphan_elimination                true
% 2.87/1.01  --res_time_limit                        2.
% 2.87/1.01  --res_out_proof                         true
% 2.87/1.01  
% 2.87/1.01  ------ Superposition Options
% 2.87/1.01  
% 2.87/1.01  --superposition_flag                    true
% 2.87/1.01  --sup_passive_queue_type                priority_queues
% 2.87/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.87/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.87/1.01  --demod_completeness_check              fast
% 2.87/1.01  --demod_use_ground                      true
% 2.87/1.01  --sup_to_prop_solver                    passive
% 2.87/1.01  --sup_prop_simpl_new                    true
% 2.87/1.01  --sup_prop_simpl_given                  true
% 2.87/1.01  --sup_fun_splitting                     false
% 2.87/1.01  --sup_smt_interval                      50000
% 2.87/1.01  
% 2.87/1.01  ------ Superposition Simplification Setup
% 2.87/1.01  
% 2.87/1.01  --sup_indices_passive                   []
% 2.87/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.87/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/1.01  --sup_full_bw                           [BwDemod]
% 2.87/1.01  --sup_immed_triv                        [TrivRules]
% 2.87/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.87/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/1.01  --sup_immed_bw_main                     []
% 2.87/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.87/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.87/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.87/1.01  
% 2.87/1.01  ------ Combination Options
% 2.87/1.01  
% 2.87/1.01  --comb_res_mult                         3
% 2.87/1.01  --comb_sup_mult                         2
% 2.87/1.01  --comb_inst_mult                        10
% 2.87/1.01  
% 2.87/1.01  ------ Debug Options
% 2.87/1.01  
% 2.87/1.01  --dbg_backtrace                         false
% 2.87/1.01  --dbg_dump_prop_clauses                 false
% 2.87/1.01  --dbg_dump_prop_clauses_file            -
% 2.87/1.01  --dbg_out_stat                          false
% 2.87/1.01  ------ Parsing...
% 2.87/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.87/1.01  
% 2.87/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.87/1.01  
% 2.87/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.87/1.01  
% 2.87/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.87/1.01  ------ Proving...
% 2.87/1.01  ------ Problem Properties 
% 2.87/1.01  
% 2.87/1.01  
% 2.87/1.01  clauses                                 23
% 2.87/1.01  conjectures                             3
% 2.87/1.01  EPR                                     6
% 2.87/1.01  Horn                                    19
% 2.87/1.01  unary                                   3
% 2.87/1.01  binary                                  7
% 2.87/1.01  lits                                    59
% 2.87/1.01  lits eq                                 11
% 2.87/1.01  fd_pure                                 0
% 2.87/1.01  fd_pseudo                               0
% 2.87/1.01  fd_cond                                 0
% 2.87/1.01  fd_pseudo_cond                          1
% 2.87/1.01  AC symbols                              0
% 2.87/1.01  
% 2.87/1.01  ------ Schedule dynamic 5 is on 
% 2.87/1.01  
% 2.87/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.87/1.01  
% 2.87/1.01  
% 2.87/1.01  ------ 
% 2.87/1.01  Current options:
% 2.87/1.01  ------ 
% 2.87/1.01  
% 2.87/1.01  ------ Input Options
% 2.87/1.01  
% 2.87/1.01  --out_options                           all
% 2.87/1.01  --tptp_safe_out                         true
% 2.87/1.01  --problem_path                          ""
% 2.87/1.01  --include_path                          ""
% 2.87/1.01  --clausifier                            res/vclausify_rel
% 2.87/1.01  --clausifier_options                    --mode clausify
% 2.87/1.01  --stdin                                 false
% 2.87/1.01  --stats_out                             all
% 2.87/1.01  
% 2.87/1.01  ------ General Options
% 2.87/1.01  
% 2.87/1.01  --fof                                   false
% 2.87/1.01  --time_out_real                         305.
% 2.87/1.01  --time_out_virtual                      -1.
% 2.87/1.01  --symbol_type_check                     false
% 2.87/1.01  --clausify_out                          false
% 2.87/1.01  --sig_cnt_out                           false
% 2.87/1.01  --trig_cnt_out                          false
% 2.87/1.01  --trig_cnt_out_tolerance                1.
% 2.87/1.01  --trig_cnt_out_sk_spl                   false
% 2.87/1.01  --abstr_cl_out                          false
% 2.87/1.01  
% 2.87/1.01  ------ Global Options
% 2.87/1.01  
% 2.87/1.01  --schedule                              default
% 2.87/1.01  --add_important_lit                     false
% 2.87/1.01  --prop_solver_per_cl                    1000
% 2.87/1.01  --min_unsat_core                        false
% 2.87/1.01  --soft_assumptions                      false
% 2.87/1.01  --soft_lemma_size                       3
% 2.87/1.01  --prop_impl_unit_size                   0
% 2.87/1.01  --prop_impl_unit                        []
% 2.87/1.01  --share_sel_clauses                     true
% 2.87/1.01  --reset_solvers                         false
% 2.87/1.01  --bc_imp_inh                            [conj_cone]
% 2.87/1.01  --conj_cone_tolerance                   3.
% 2.87/1.01  --extra_neg_conj                        none
% 2.87/1.01  --large_theory_mode                     true
% 2.87/1.01  --prolific_symb_bound                   200
% 2.87/1.01  --lt_threshold                          2000
% 2.87/1.01  --clause_weak_htbl                      true
% 2.87/1.01  --gc_record_bc_elim                     false
% 2.87/1.01  
% 2.87/1.01  ------ Preprocessing Options
% 2.87/1.01  
% 2.87/1.01  --preprocessing_flag                    true
% 2.87/1.01  --time_out_prep_mult                    0.1
% 2.87/1.01  --splitting_mode                        input
% 2.87/1.01  --splitting_grd                         true
% 2.87/1.01  --splitting_cvd                         false
% 2.87/1.01  --splitting_cvd_svl                     false
% 2.87/1.01  --splitting_nvd                         32
% 2.87/1.01  --sub_typing                            true
% 2.87/1.01  --prep_gs_sim                           true
% 2.87/1.01  --prep_unflatten                        true
% 2.87/1.01  --prep_res_sim                          true
% 2.87/1.01  --prep_upred                            true
% 2.87/1.01  --prep_sem_filter                       exhaustive
% 2.87/1.01  --prep_sem_filter_out                   false
% 2.87/1.01  --pred_elim                             true
% 2.87/1.01  --res_sim_input                         true
% 2.87/1.01  --eq_ax_congr_red                       true
% 2.87/1.01  --pure_diseq_elim                       true
% 2.87/1.01  --brand_transform                       false
% 2.87/1.01  --non_eq_to_eq                          false
% 2.87/1.01  --prep_def_merge                        true
% 2.87/1.01  --prep_def_merge_prop_impl              false
% 2.87/1.01  --prep_def_merge_mbd                    true
% 2.87/1.01  --prep_def_merge_tr_red                 false
% 2.87/1.01  --prep_def_merge_tr_cl                  false
% 2.87/1.01  --smt_preprocessing                     true
% 2.87/1.01  --smt_ac_axioms                         fast
% 2.87/1.01  --preprocessed_out                      false
% 2.87/1.01  --preprocessed_stats                    false
% 2.87/1.01  
% 2.87/1.01  ------ Abstraction refinement Options
% 2.87/1.01  
% 2.87/1.01  --abstr_ref                             []
% 2.87/1.01  --abstr_ref_prep                        false
% 2.87/1.01  --abstr_ref_until_sat                   false
% 2.87/1.01  --abstr_ref_sig_restrict                funpre
% 2.87/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.87/1.01  --abstr_ref_under                       []
% 2.87/1.01  
% 2.87/1.01  ------ SAT Options
% 2.87/1.01  
% 2.87/1.01  --sat_mode                              false
% 2.87/1.01  --sat_fm_restart_options                ""
% 2.87/1.01  --sat_gr_def                            false
% 2.87/1.01  --sat_epr_types                         true
% 2.87/1.01  --sat_non_cyclic_types                  false
% 2.87/1.01  --sat_finite_models                     false
% 2.87/1.01  --sat_fm_lemmas                         false
% 2.87/1.01  --sat_fm_prep                           false
% 2.87/1.01  --sat_fm_uc_incr                        true
% 2.87/1.01  --sat_out_model                         small
% 2.87/1.01  --sat_out_clauses                       false
% 2.87/1.01  
% 2.87/1.01  ------ QBF Options
% 2.87/1.01  
% 2.87/1.01  --qbf_mode                              false
% 2.87/1.01  --qbf_elim_univ                         false
% 2.87/1.01  --qbf_dom_inst                          none
% 2.87/1.01  --qbf_dom_pre_inst                      false
% 2.87/1.01  --qbf_sk_in                             false
% 2.87/1.01  --qbf_pred_elim                         true
% 2.87/1.01  --qbf_split                             512
% 2.87/1.01  
% 2.87/1.01  ------ BMC1 Options
% 2.87/1.01  
% 2.87/1.01  --bmc1_incremental                      false
% 2.87/1.01  --bmc1_axioms                           reachable_all
% 2.87/1.01  --bmc1_min_bound                        0
% 2.87/1.01  --bmc1_max_bound                        -1
% 2.87/1.01  --bmc1_max_bound_default                -1
% 2.87/1.01  --bmc1_symbol_reachability              true
% 2.87/1.01  --bmc1_property_lemmas                  false
% 2.87/1.01  --bmc1_k_induction                      false
% 2.87/1.01  --bmc1_non_equiv_states                 false
% 2.87/1.01  --bmc1_deadlock                         false
% 2.87/1.01  --bmc1_ucm                              false
% 2.87/1.01  --bmc1_add_unsat_core                   none
% 2.87/1.01  --bmc1_unsat_core_children              false
% 2.87/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.87/1.01  --bmc1_out_stat                         full
% 2.87/1.01  --bmc1_ground_init                      false
% 2.87/1.01  --bmc1_pre_inst_next_state              false
% 2.87/1.01  --bmc1_pre_inst_state                   false
% 2.87/1.01  --bmc1_pre_inst_reach_state             false
% 2.87/1.01  --bmc1_out_unsat_core                   false
% 2.87/1.01  --bmc1_aig_witness_out                  false
% 2.87/1.01  --bmc1_verbose                          false
% 2.87/1.01  --bmc1_dump_clauses_tptp                false
% 2.87/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.87/1.01  --bmc1_dump_file                        -
% 2.87/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.87/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.87/1.01  --bmc1_ucm_extend_mode                  1
% 2.87/1.01  --bmc1_ucm_init_mode                    2
% 2.87/1.01  --bmc1_ucm_cone_mode                    none
% 2.87/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.87/1.01  --bmc1_ucm_relax_model                  4
% 2.87/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.87/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.87/1.01  --bmc1_ucm_layered_model                none
% 2.87/1.01  --bmc1_ucm_max_lemma_size               10
% 2.87/1.01  
% 2.87/1.01  ------ AIG Options
% 2.87/1.01  
% 2.87/1.01  --aig_mode                              false
% 2.87/1.01  
% 2.87/1.01  ------ Instantiation Options
% 2.87/1.01  
% 2.87/1.01  --instantiation_flag                    true
% 2.87/1.01  --inst_sos_flag                         false
% 2.87/1.01  --inst_sos_phase                        true
% 2.87/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.87/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.87/1.01  --inst_lit_sel_side                     none
% 2.87/1.01  --inst_solver_per_active                1400
% 2.87/1.01  --inst_solver_calls_frac                1.
% 2.87/1.01  --inst_passive_queue_type               priority_queues
% 2.87/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.87/1.01  --inst_passive_queues_freq              [25;2]
% 2.87/1.01  --inst_dismatching                      true
% 2.87/1.01  --inst_eager_unprocessed_to_passive     true
% 2.87/1.01  --inst_prop_sim_given                   true
% 2.87/1.01  --inst_prop_sim_new                     false
% 2.87/1.01  --inst_subs_new                         false
% 2.87/1.01  --inst_eq_res_simp                      false
% 2.87/1.01  --inst_subs_given                       false
% 2.87/1.01  --inst_orphan_elimination               true
% 2.87/1.01  --inst_learning_loop_flag               true
% 2.87/1.01  --inst_learning_start                   3000
% 2.87/1.01  --inst_learning_factor                  2
% 2.87/1.01  --inst_start_prop_sim_after_learn       3
% 2.87/1.01  --inst_sel_renew                        solver
% 2.87/1.01  --inst_lit_activity_flag                true
% 2.87/1.01  --inst_restr_to_given                   false
% 2.87/1.01  --inst_activity_threshold               500
% 2.87/1.01  --inst_out_proof                        true
% 2.87/1.01  
% 2.87/1.01  ------ Resolution Options
% 2.87/1.01  
% 2.87/1.01  --resolution_flag                       false
% 2.87/1.01  --res_lit_sel                           adaptive
% 2.87/1.01  --res_lit_sel_side                      none
% 2.87/1.01  --res_ordering                          kbo
% 2.87/1.02  --res_to_prop_solver                    active
% 2.87/1.02  --res_prop_simpl_new                    false
% 2.87/1.02  --res_prop_simpl_given                  true
% 2.87/1.02  --res_passive_queue_type                priority_queues
% 2.87/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.87/1.02  --res_passive_queues_freq               [15;5]
% 2.87/1.02  --res_forward_subs                      full
% 2.87/1.02  --res_backward_subs                     full
% 2.87/1.02  --res_forward_subs_resolution           true
% 2.87/1.02  --res_backward_subs_resolution          true
% 2.87/1.02  --res_orphan_elimination                true
% 2.87/1.02  --res_time_limit                        2.
% 2.87/1.02  --res_out_proof                         true
% 2.87/1.02  
% 2.87/1.02  ------ Superposition Options
% 2.87/1.02  
% 2.87/1.02  --superposition_flag                    true
% 2.87/1.02  --sup_passive_queue_type                priority_queues
% 2.87/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.87/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.87/1.02  --demod_completeness_check              fast
% 2.87/1.02  --demod_use_ground                      true
% 2.87/1.02  --sup_to_prop_solver                    passive
% 2.87/1.02  --sup_prop_simpl_new                    true
% 2.87/1.02  --sup_prop_simpl_given                  true
% 2.87/1.02  --sup_fun_splitting                     false
% 2.87/1.02  --sup_smt_interval                      50000
% 2.87/1.02  
% 2.87/1.02  ------ Superposition Simplification Setup
% 2.87/1.02  
% 2.87/1.02  --sup_indices_passive                   []
% 2.87/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.87/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/1.02  --sup_full_bw                           [BwDemod]
% 2.87/1.02  --sup_immed_triv                        [TrivRules]
% 2.87/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.87/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/1.02  --sup_immed_bw_main                     []
% 2.87/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.87/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.87/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.87/1.02  
% 2.87/1.02  ------ Combination Options
% 2.87/1.02  
% 2.87/1.02  --comb_res_mult                         3
% 2.87/1.02  --comb_sup_mult                         2
% 2.87/1.02  --comb_inst_mult                        10
% 2.87/1.02  
% 2.87/1.02  ------ Debug Options
% 2.87/1.02  
% 2.87/1.02  --dbg_backtrace                         false
% 2.87/1.02  --dbg_dump_prop_clauses                 false
% 2.87/1.02  --dbg_dump_prop_clauses_file            -
% 2.87/1.02  --dbg_out_stat                          false
% 2.87/1.02  
% 2.87/1.02  
% 2.87/1.02  
% 2.87/1.02  
% 2.87/1.02  ------ Proving...
% 2.87/1.02  
% 2.87/1.02  
% 2.87/1.02  % SZS status Theorem for theBenchmark.p
% 2.87/1.02  
% 2.87/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.87/1.02  
% 2.87/1.02  fof(f10,conjecture,(
% 2.87/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 2.87/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.02  
% 2.87/1.02  fof(f11,negated_conjecture,(
% 2.87/1.02    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 2.87/1.02    inference(negated_conjecture,[],[f10])).
% 2.87/1.02  
% 2.87/1.02  fof(f21,plain,(
% 2.87/1.02    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 2.87/1.02    inference(ennf_transformation,[],[f11])).
% 2.87/1.02  
% 2.87/1.02  fof(f22,plain,(
% 2.87/1.02    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 2.87/1.02    inference(flattening,[],[f21])).
% 2.87/1.02  
% 2.87/1.02  fof(f36,plain,(
% 2.87/1.02    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK6 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(sK6,k7_relset_1(X0,X1,X3,X2)))) )),
% 2.87/1.02    introduced(choice_axiom,[])).
% 2.87/1.02  
% 2.87/1.02  fof(f35,plain,(
% 2.87/1.02    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK5,X5) != X4 | ~r2_hidden(X5,sK4) | ~r2_hidden(X5,sK2)) & r2_hidden(X4,k7_relset_1(sK2,sK3,sK5,sK4))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK5,sK2,sK3) & v1_funct_1(sK5))),
% 2.87/1.02    introduced(choice_axiom,[])).
% 2.87/1.02  
% 2.87/1.02  fof(f37,plain,(
% 2.87/1.02    (! [X5] : (k1_funct_1(sK5,X5) != sK6 | ~r2_hidden(X5,sK4) | ~r2_hidden(X5,sK2)) & r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK5,sK2,sK3) & v1_funct_1(sK5)),
% 2.87/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f22,f36,f35])).
% 2.87/1.02  
% 2.87/1.02  fof(f63,plain,(
% 2.87/1.02    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 2.87/1.02    inference(cnf_transformation,[],[f37])).
% 2.87/1.02  
% 2.87/1.02  fof(f8,axiom,(
% 2.87/1.02    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.87/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.02  
% 2.87/1.02  fof(f18,plain,(
% 2.87/1.02    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.87/1.02    inference(ennf_transformation,[],[f8])).
% 2.87/1.02  
% 2.87/1.02  fof(f54,plain,(
% 2.87/1.02    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.87/1.02    inference(cnf_transformation,[],[f18])).
% 2.87/1.02  
% 2.87/1.02  fof(f64,plain,(
% 2.87/1.02    r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4))),
% 2.87/1.02    inference(cnf_transformation,[],[f37])).
% 2.87/1.02  
% 2.87/1.02  fof(f9,axiom,(
% 2.87/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.87/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.02  
% 2.87/1.02  fof(f19,plain,(
% 2.87/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.87/1.02    inference(ennf_transformation,[],[f9])).
% 2.87/1.02  
% 2.87/1.02  fof(f20,plain,(
% 2.87/1.02    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.87/1.02    inference(flattening,[],[f19])).
% 2.87/1.02  
% 2.87/1.02  fof(f34,plain,(
% 2.87/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.87/1.02    inference(nnf_transformation,[],[f20])).
% 2.87/1.02  
% 2.87/1.02  fof(f55,plain,(
% 2.87/1.02    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.87/1.02    inference(cnf_transformation,[],[f34])).
% 2.87/1.02  
% 2.87/1.02  fof(f62,plain,(
% 2.87/1.02    v1_funct_2(sK5,sK2,sK3)),
% 2.87/1.02    inference(cnf_transformation,[],[f37])).
% 2.87/1.02  
% 2.87/1.02  fof(f7,axiom,(
% 2.87/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.87/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.02  
% 2.87/1.02  fof(f17,plain,(
% 2.87/1.02    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.87/1.02    inference(ennf_transformation,[],[f7])).
% 2.87/1.02  
% 2.87/1.02  fof(f53,plain,(
% 2.87/1.02    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.87/1.02    inference(cnf_transformation,[],[f17])).
% 2.87/1.02  
% 2.87/1.02  fof(f4,axiom,(
% 2.87/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 2.87/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.02  
% 2.87/1.02  fof(f13,plain,(
% 2.87/1.02    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 2.87/1.02    inference(ennf_transformation,[],[f4])).
% 2.87/1.02  
% 2.87/1.02  fof(f28,plain,(
% 2.87/1.02    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.87/1.02    inference(nnf_transformation,[],[f13])).
% 2.87/1.02  
% 2.87/1.02  fof(f29,plain,(
% 2.87/1.02    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.87/1.02    inference(rectify,[],[f28])).
% 2.87/1.02  
% 2.87/1.02  fof(f30,plain,(
% 2.87/1.02    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))))),
% 2.87/1.02    introduced(choice_axiom,[])).
% 2.87/1.02  
% 2.87/1.02  fof(f31,plain,(
% 2.87/1.02    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.87/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).
% 2.87/1.02  
% 2.87/1.02  fof(f45,plain,(
% 2.87/1.02    ( ! [X2,X0,X1] : (r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.87/1.02    inference(cnf_transformation,[],[f31])).
% 2.87/1.02  
% 2.87/1.02  fof(f6,axiom,(
% 2.87/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.87/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.02  
% 2.87/1.02  fof(f16,plain,(
% 2.87/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.87/1.02    inference(ennf_transformation,[],[f6])).
% 2.87/1.02  
% 2.87/1.02  fof(f52,plain,(
% 2.87/1.02    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.87/1.02    inference(cnf_transformation,[],[f16])).
% 2.87/1.02  
% 2.87/1.02  fof(f1,axiom,(
% 2.87/1.02    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.87/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.02  
% 2.87/1.02  fof(f23,plain,(
% 2.87/1.02    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.87/1.02    inference(nnf_transformation,[],[f1])).
% 2.87/1.02  
% 2.87/1.02  fof(f24,plain,(
% 2.87/1.02    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.87/1.02    inference(rectify,[],[f23])).
% 2.87/1.02  
% 2.87/1.02  fof(f25,plain,(
% 2.87/1.02    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.87/1.02    introduced(choice_axiom,[])).
% 2.87/1.02  
% 2.87/1.02  fof(f26,plain,(
% 2.87/1.02    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.87/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 2.87/1.02  
% 2.87/1.02  fof(f38,plain,(
% 2.87/1.02    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.87/1.02    inference(cnf_transformation,[],[f26])).
% 2.87/1.02  
% 2.87/1.02  fof(f46,plain,(
% 2.87/1.02    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.87/1.02    inference(cnf_transformation,[],[f31])).
% 2.87/1.02  
% 2.87/1.02  fof(f5,axiom,(
% 2.87/1.02    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 2.87/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.02  
% 2.87/1.02  fof(f14,plain,(
% 2.87/1.02    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.87/1.02    inference(ennf_transformation,[],[f5])).
% 2.87/1.02  
% 2.87/1.02  fof(f15,plain,(
% 2.87/1.02    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.87/1.02    inference(flattening,[],[f14])).
% 2.87/1.02  
% 2.87/1.02  fof(f32,plain,(
% 2.87/1.02    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.87/1.02    inference(nnf_transformation,[],[f15])).
% 2.87/1.02  
% 2.87/1.02  fof(f33,plain,(
% 2.87/1.02    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.87/1.02    inference(flattening,[],[f32])).
% 2.87/1.02  
% 2.87/1.02  fof(f50,plain,(
% 2.87/1.02    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.87/1.02    inference(cnf_transformation,[],[f33])).
% 2.87/1.02  
% 2.87/1.02  fof(f61,plain,(
% 2.87/1.02    v1_funct_1(sK5)),
% 2.87/1.02    inference(cnf_transformation,[],[f37])).
% 2.87/1.02  
% 2.87/1.02  fof(f65,plain,(
% 2.87/1.02    ( ! [X5] : (k1_funct_1(sK5,X5) != sK6 | ~r2_hidden(X5,sK4) | ~r2_hidden(X5,sK2)) )),
% 2.87/1.02    inference(cnf_transformation,[],[f37])).
% 2.87/1.02  
% 2.87/1.02  fof(f47,plain,(
% 2.87/1.02    ( ! [X2,X0,X1] : (r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.87/1.02    inference(cnf_transformation,[],[f31])).
% 2.87/1.02  
% 2.87/1.02  fof(f59,plain,(
% 2.87/1.02    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.87/1.02    inference(cnf_transformation,[],[f34])).
% 2.87/1.02  
% 2.87/1.02  fof(f69,plain,(
% 2.87/1.02    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.87/1.02    inference(equality_resolution,[],[f59])).
% 2.87/1.02  
% 2.87/1.02  fof(f2,axiom,(
% 2.87/1.02    v1_xboole_0(k1_xboole_0)),
% 2.87/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.02  
% 2.87/1.02  fof(f40,plain,(
% 2.87/1.02    v1_xboole_0(k1_xboole_0)),
% 2.87/1.02    inference(cnf_transformation,[],[f2])).
% 2.87/1.02  
% 2.87/1.02  fof(f3,axiom,(
% 2.87/1.02    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.87/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.02  
% 2.87/1.02  fof(f12,plain,(
% 2.87/1.02    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.87/1.02    inference(ennf_transformation,[],[f3])).
% 2.87/1.02  
% 2.87/1.02  fof(f27,plain,(
% 2.87/1.02    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 2.87/1.02    inference(nnf_transformation,[],[f12])).
% 2.87/1.02  
% 2.87/1.02  fof(f42,plain,(
% 2.87/1.02    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.87/1.02    inference(cnf_transformation,[],[f27])).
% 2.87/1.02  
% 2.87/1.02  fof(f39,plain,(
% 2.87/1.02    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 2.87/1.02    inference(cnf_transformation,[],[f26])).
% 2.87/1.02  
% 2.87/1.02  fof(f41,plain,(
% 2.87/1.02    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.87/1.02    inference(cnf_transformation,[],[f27])).
% 2.87/1.02  
% 2.87/1.02  fof(f43,plain,(
% 2.87/1.02    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,X0) | ~v1_xboole_0(X0)) )),
% 2.87/1.02    inference(cnf_transformation,[],[f27])).
% 2.87/1.02  
% 2.87/1.02  fof(f56,plain,(
% 2.87/1.02    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.87/1.02    inference(cnf_transformation,[],[f34])).
% 2.87/1.02  
% 2.87/1.02  fof(f71,plain,(
% 2.87/1.02    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.87/1.02    inference(equality_resolution,[],[f56])).
% 2.87/1.02  
% 2.87/1.02  cnf(c_25,negated_conjecture,
% 2.87/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 2.87/1.02      inference(cnf_transformation,[],[f63]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_1795,plain,
% 2.87/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_16,plain,
% 2.87/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.87/1.02      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.87/1.02      inference(cnf_transformation,[],[f54]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_1798,plain,
% 2.87/1.02      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 2.87/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_2546,plain,
% 2.87/1.02      ( k7_relset_1(sK2,sK3,sK5,X0) = k9_relat_1(sK5,X0) ),
% 2.87/1.02      inference(superposition,[status(thm)],[c_1795,c_1798]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_24,negated_conjecture,
% 2.87/1.02      ( r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4)) ),
% 2.87/1.02      inference(cnf_transformation,[],[f64]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_1796,plain,
% 2.87/1.02      ( r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4)) = iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_2747,plain,
% 2.87/1.02      ( r2_hidden(sK6,k9_relat_1(sK5,sK4)) = iProver_top ),
% 2.87/1.02      inference(demodulation,[status(thm)],[c_2546,c_1796]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_22,plain,
% 2.87/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.87/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.87/1.02      | k1_relset_1(X1,X2,X0) = X1
% 2.87/1.02      | k1_xboole_0 = X2 ),
% 2.87/1.02      inference(cnf_transformation,[],[f55]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_26,negated_conjecture,
% 2.87/1.02      ( v1_funct_2(sK5,sK2,sK3) ),
% 2.87/1.02      inference(cnf_transformation,[],[f62]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_556,plain,
% 2.87/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.87/1.02      | k1_relset_1(X1,X2,X0) = X1
% 2.87/1.02      | sK3 != X2
% 2.87/1.02      | sK2 != X1
% 2.87/1.02      | sK5 != X0
% 2.87/1.02      | k1_xboole_0 = X2 ),
% 2.87/1.02      inference(resolution_lifted,[status(thm)],[c_22,c_26]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_557,plain,
% 2.87/1.02      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.87/1.02      | k1_relset_1(sK2,sK3,sK5) = sK2
% 2.87/1.02      | k1_xboole_0 = sK3 ),
% 2.87/1.02      inference(unflattening,[status(thm)],[c_556]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_559,plain,
% 2.87/1.02      ( k1_relset_1(sK2,sK3,sK5) = sK2 | k1_xboole_0 = sK3 ),
% 2.87/1.02      inference(global_propositional_subsumption,
% 2.87/1.02                [status(thm)],
% 2.87/1.02                [c_557,c_25]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_15,plain,
% 2.87/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.87/1.02      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.87/1.02      inference(cnf_transformation,[],[f53]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_1799,plain,
% 2.87/1.02      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.87/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_2542,plain,
% 2.87/1.02      ( k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
% 2.87/1.02      inference(superposition,[status(thm)],[c_1795,c_1799]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_2742,plain,
% 2.87/1.02      ( k1_relat_1(sK5) = sK2 | sK3 = k1_xboole_0 ),
% 2.87/1.02      inference(superposition,[status(thm)],[c_559,c_2542]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_10,plain,
% 2.87/1.02      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.87/1.02      | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1))
% 2.87/1.02      | ~ v1_relat_1(X1) ),
% 2.87/1.02      inference(cnf_transformation,[],[f45]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_1801,plain,
% 2.87/1.02      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 2.87/1.02      | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1)) = iProver_top
% 2.87/1.02      | v1_relat_1(X1) != iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_3136,plain,
% 2.87/1.02      ( sK3 = k1_xboole_0
% 2.87/1.02      | r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
% 2.87/1.02      | r2_hidden(sK1(X0,X1,sK5),sK2) = iProver_top
% 2.87/1.02      | v1_relat_1(sK5) != iProver_top ),
% 2.87/1.02      inference(superposition,[status(thm)],[c_2742,c_1801]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_30,plain,
% 2.87/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_14,plain,
% 2.87/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.87/1.02      | v1_relat_1(X0) ),
% 2.87/1.02      inference(cnf_transformation,[],[f52]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_1989,plain,
% 2.87/1.02      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.87/1.02      | v1_relat_1(sK5) ),
% 2.87/1.02      inference(instantiation,[status(thm)],[c_14]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_1990,plain,
% 2.87/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 2.87/1.02      | v1_relat_1(sK5) = iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_1989]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_3819,plain,
% 2.87/1.02      ( r2_hidden(sK1(X0,X1,sK5),sK2) = iProver_top
% 2.87/1.02      | r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
% 2.87/1.02      | sK3 = k1_xboole_0 ),
% 2.87/1.02      inference(global_propositional_subsumption,
% 2.87/1.02                [status(thm)],
% 2.87/1.02                [c_3136,c_30,c_1990]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_3820,plain,
% 2.87/1.02      ( sK3 = k1_xboole_0
% 2.87/1.02      | r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
% 2.87/1.02      | r2_hidden(sK1(X0,X1,sK5),sK2) = iProver_top ),
% 2.87/1.02      inference(renaming,[status(thm)],[c_3819]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_1,plain,
% 2.87/1.02      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.87/1.02      inference(cnf_transformation,[],[f38]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_1809,plain,
% 2.87/1.02      ( r2_hidden(X0,X1) != iProver_top
% 2.87/1.02      | v1_xboole_0(X1) != iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_3829,plain,
% 2.87/1.02      ( sK3 = k1_xboole_0
% 2.87/1.02      | r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
% 2.87/1.02      | v1_xboole_0(sK2) != iProver_top ),
% 2.87/1.02      inference(superposition,[status(thm)],[c_3820,c_1809]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_3986,plain,
% 2.87/1.02      ( sK3 = k1_xboole_0 | v1_xboole_0(sK2) != iProver_top ),
% 2.87/1.02      inference(superposition,[status(thm)],[c_2747,c_3829]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_2756,plain,
% 2.87/1.02      ( r2_hidden(sK6,k9_relat_1(sK5,sK4)) ),
% 2.87/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_2747]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_9,plain,
% 2.87/1.02      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.87/1.02      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
% 2.87/1.02      | ~ v1_relat_1(X1) ),
% 2.87/1.02      inference(cnf_transformation,[],[f46]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_1802,plain,
% 2.87/1.02      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 2.87/1.02      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1) = iProver_top
% 2.87/1.02      | v1_relat_1(X1) != iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_12,plain,
% 2.87/1.02      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 2.87/1.02      | ~ v1_funct_1(X2)
% 2.87/1.02      | ~ v1_relat_1(X2)
% 2.87/1.02      | k1_funct_1(X2,X0) = X1 ),
% 2.87/1.02      inference(cnf_transformation,[],[f50]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_27,negated_conjecture,
% 2.87/1.02      ( v1_funct_1(sK5) ),
% 2.87/1.02      inference(cnf_transformation,[],[f61]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_350,plain,
% 2.87/1.02      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 2.87/1.02      | ~ v1_relat_1(X2)
% 2.87/1.02      | k1_funct_1(X2,X0) = X1
% 2.87/1.02      | sK5 != X2 ),
% 2.87/1.02      inference(resolution_lifted,[status(thm)],[c_12,c_27]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_351,plain,
% 2.87/1.02      ( ~ r2_hidden(k4_tarski(X0,X1),sK5)
% 2.87/1.02      | ~ v1_relat_1(sK5)
% 2.87/1.02      | k1_funct_1(sK5,X0) = X1 ),
% 2.87/1.02      inference(unflattening,[status(thm)],[c_350]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_1791,plain,
% 2.87/1.02      ( k1_funct_1(sK5,X0) = X1
% 2.87/1.02      | r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top
% 2.87/1.02      | v1_relat_1(sK5) != iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_351]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_352,plain,
% 2.87/1.02      ( k1_funct_1(sK5,X0) = X1
% 2.87/1.02      | r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top
% 2.87/1.02      | v1_relat_1(sK5) != iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_351]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_2021,plain,
% 2.87/1.02      ( r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top
% 2.87/1.02      | k1_funct_1(sK5,X0) = X1 ),
% 2.87/1.02      inference(global_propositional_subsumption,
% 2.87/1.02                [status(thm)],
% 2.87/1.02                [c_1791,c_30,c_352,c_1990]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_2022,plain,
% 2.87/1.02      ( k1_funct_1(sK5,X0) = X1
% 2.87/1.02      | r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top ),
% 2.87/1.02      inference(renaming,[status(thm)],[c_2021]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_3186,plain,
% 2.87/1.02      ( k1_funct_1(sK5,sK1(X0,X1,sK5)) = X0
% 2.87/1.02      | r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
% 2.87/1.02      | v1_relat_1(sK5) != iProver_top ),
% 2.87/1.02      inference(superposition,[status(thm)],[c_1802,c_2022]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_3581,plain,
% 2.87/1.02      ( r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
% 2.87/1.02      | k1_funct_1(sK5,sK1(X0,X1,sK5)) = X0 ),
% 2.87/1.02      inference(global_propositional_subsumption,
% 2.87/1.02                [status(thm)],
% 2.87/1.02                [c_3186,c_30,c_1990]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_3582,plain,
% 2.87/1.02      ( k1_funct_1(sK5,sK1(X0,X1,sK5)) = X0
% 2.87/1.02      | r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top ),
% 2.87/1.02      inference(renaming,[status(thm)],[c_3581]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_3592,plain,
% 2.87/1.02      ( k1_funct_1(sK5,sK1(sK6,sK4,sK5)) = sK6 ),
% 2.87/1.02      inference(superposition,[status(thm)],[c_2747,c_3582]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_23,negated_conjecture,
% 2.87/1.02      ( ~ r2_hidden(X0,sK2)
% 2.87/1.02      | ~ r2_hidden(X0,sK4)
% 2.87/1.02      | k1_funct_1(sK5,X0) != sK6 ),
% 2.87/1.02      inference(cnf_transformation,[],[f65]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_1797,plain,
% 2.87/1.02      ( k1_funct_1(sK5,X0) != sK6
% 2.87/1.02      | r2_hidden(X0,sK2) != iProver_top
% 2.87/1.02      | r2_hidden(X0,sK4) != iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_3623,plain,
% 2.87/1.02      ( r2_hidden(sK1(sK6,sK4,sK5),sK2) != iProver_top
% 2.87/1.02      | r2_hidden(sK1(sK6,sK4,sK5),sK4) != iProver_top ),
% 2.87/1.02      inference(superposition,[status(thm)],[c_3592,c_1797]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_3830,plain,
% 2.87/1.02      ( sK3 = k1_xboole_0
% 2.87/1.02      | r2_hidden(sK1(sK6,sK4,sK5),sK4) != iProver_top
% 2.87/1.02      | r2_hidden(sK6,k9_relat_1(sK5,sK4)) != iProver_top ),
% 2.87/1.02      inference(superposition,[status(thm)],[c_3820,c_3623]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_3855,plain,
% 2.87/1.02      ( ~ r2_hidden(sK1(sK6,sK4,sK5),sK4)
% 2.87/1.02      | ~ r2_hidden(sK6,k9_relat_1(sK5,sK4))
% 2.87/1.02      | sK3 = k1_xboole_0 ),
% 2.87/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_3830]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_8,plain,
% 2.87/1.02      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.87/1.02      | r2_hidden(sK1(X0,X2,X1),X2)
% 2.87/1.02      | ~ v1_relat_1(X1) ),
% 2.87/1.02      inference(cnf_transformation,[],[f47]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_2061,plain,
% 2.87/1.02      ( ~ r2_hidden(X0,k9_relat_1(sK5,X1))
% 2.87/1.02      | r2_hidden(sK1(X0,X1,sK5),X1)
% 2.87/1.02      | ~ v1_relat_1(sK5) ),
% 2.87/1.02      inference(instantiation,[status(thm)],[c_8]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_4186,plain,
% 2.87/1.02      ( r2_hidden(sK1(sK6,sK4,sK5),sK4)
% 2.87/1.02      | ~ r2_hidden(sK6,k9_relat_1(sK5,sK4))
% 2.87/1.02      | ~ v1_relat_1(sK5) ),
% 2.87/1.02      inference(instantiation,[status(thm)],[c_2061]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_4252,plain,
% 2.87/1.02      ( sK3 = k1_xboole_0 ),
% 2.87/1.02      inference(global_propositional_subsumption,
% 2.87/1.02                [status(thm)],
% 2.87/1.02                [c_3986,c_25,c_1989,c_2756,c_3855,c_4186]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_18,plain,
% 2.87/1.02      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 2.87/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.87/1.02      | k1_xboole_0 = X1
% 2.87/1.02      | k1_xboole_0 = X0 ),
% 2.87/1.02      inference(cnf_transformation,[],[f69]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_523,plain,
% 2.87/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.87/1.02      | sK3 != k1_xboole_0
% 2.87/1.02      | sK2 != X1
% 2.87/1.02      | sK5 != X0
% 2.87/1.02      | k1_xboole_0 = X0
% 2.87/1.02      | k1_xboole_0 = X1 ),
% 2.87/1.02      inference(resolution_lifted,[status(thm)],[c_18,c_26]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_524,plain,
% 2.87/1.02      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 2.87/1.02      | sK3 != k1_xboole_0
% 2.87/1.02      | k1_xboole_0 = sK2
% 2.87/1.02      | k1_xboole_0 = sK5 ),
% 2.87/1.02      inference(unflattening,[status(thm)],[c_523]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_1790,plain,
% 2.87/1.02      ( sK3 != k1_xboole_0
% 2.87/1.02      | k1_xboole_0 = sK2
% 2.87/1.02      | k1_xboole_0 = sK5
% 2.87/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_524]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_4259,plain,
% 2.87/1.02      ( sK2 = k1_xboole_0
% 2.87/1.02      | sK5 = k1_xboole_0
% 2.87/1.02      | k1_xboole_0 != k1_xboole_0
% 2.87/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 2.87/1.02      inference(demodulation,[status(thm)],[c_4252,c_1790]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_4271,plain,
% 2.87/1.02      ( sK2 = k1_xboole_0
% 2.87/1.02      | sK5 = k1_xboole_0
% 2.87/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 2.87/1.02      inference(equality_resolution_simp,[status(thm)],[c_4259]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_4262,plain,
% 2.87/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
% 2.87/1.02      inference(demodulation,[status(thm)],[c_4252,c_1795]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_4275,plain,
% 2.87/1.02      ( sK2 = k1_xboole_0 | sK5 = k1_xboole_0 ),
% 2.87/1.02      inference(forward_subsumption_resolution,
% 2.87/1.02                [status(thm)],
% 2.87/1.02                [c_4271,c_4262]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_31,plain,
% 2.87/1.02      ( r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4)) = iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_2,plain,
% 2.87/1.02      ( v1_xboole_0(k1_xboole_0) ),
% 2.87/1.02      inference(cnf_transformation,[],[f40]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_5,plain,
% 2.87/1.02      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.87/1.02      inference(cnf_transformation,[],[f42]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_177,plain,
% 2.87/1.02      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 2.87/1.02      inference(global_propositional_subsumption,[status(thm)],[c_5,c_1]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_178,plain,
% 2.87/1.02      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 2.87/1.02      inference(renaming,[status(thm)],[c_177]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_683,plain,
% 2.87/1.02      ( ~ r2_hidden(X0,X1)
% 2.87/1.02      | k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) != X1
% 2.87/1.02      | sK3 != k1_xboole_0
% 2.87/1.02      | sK2 = k1_xboole_0
% 2.87/1.02      | sK5 != X0
% 2.87/1.02      | sK5 = k1_xboole_0 ),
% 2.87/1.02      inference(resolution_lifted,[status(thm)],[c_178,c_524]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_684,plain,
% 2.87/1.02      ( ~ r2_hidden(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 2.87/1.02      | sK3 != k1_xboole_0
% 2.87/1.02      | sK2 = k1_xboole_0
% 2.87/1.02      | sK5 = k1_xboole_0 ),
% 2.87/1.02      inference(unflattening,[status(thm)],[c_683]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_685,plain,
% 2.87/1.02      ( sK3 != k1_xboole_0
% 2.87/1.02      | sK2 = k1_xboole_0
% 2.87/1.02      | sK5 = k1_xboole_0
% 2.87/1.02      | r2_hidden(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_684]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_1981,plain,
% 2.87/1.02      ( ~ r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4))
% 2.87/1.02      | ~ v1_xboole_0(k7_relset_1(sK2,sK3,sK5,sK4)) ),
% 2.87/1.02      inference(instantiation,[status(thm)],[c_1]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_1982,plain,
% 2.87/1.02      ( r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4)) != iProver_top
% 2.87/1.02      | v1_xboole_0(k7_relset_1(sK2,sK3,sK5,sK4)) != iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_1981]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_1393,plain,
% 2.87/1.02      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.87/1.02      theory(equality) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_2050,plain,
% 2.87/1.02      ( ~ v1_xboole_0(X0)
% 2.87/1.02      | v1_xboole_0(k7_relset_1(sK2,sK3,sK5,sK4))
% 2.87/1.02      | k7_relset_1(sK2,sK3,sK5,sK4) != X0 ),
% 2.87/1.02      inference(instantiation,[status(thm)],[c_1393]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_2208,plain,
% 2.87/1.02      ( v1_xboole_0(k7_relset_1(sK2,sK3,sK5,sK4))
% 2.87/1.02      | ~ v1_xboole_0(k9_relat_1(sK5,sK4))
% 2.87/1.02      | k7_relset_1(sK2,sK3,sK5,sK4) != k9_relat_1(sK5,sK4) ),
% 2.87/1.02      inference(instantiation,[status(thm)],[c_2050]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_2210,plain,
% 2.87/1.02      ( k7_relset_1(sK2,sK3,sK5,sK4) != k9_relat_1(sK5,sK4)
% 2.87/1.02      | v1_xboole_0(k7_relset_1(sK2,sK3,sK5,sK4)) = iProver_top
% 2.87/1.02      | v1_xboole_0(k9_relat_1(sK5,sK4)) != iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_2208]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_2035,plain,
% 2.87/1.02      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.87/1.02      | k7_relset_1(sK2,sK3,sK5,X0) = k9_relat_1(sK5,X0) ),
% 2.87/1.02      inference(instantiation,[status(thm)],[c_16]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_2209,plain,
% 2.87/1.02      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.87/1.02      | k7_relset_1(sK2,sK3,sK5,sK4) = k9_relat_1(sK5,sK4) ),
% 2.87/1.02      inference(instantiation,[status(thm)],[c_2035]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_0,plain,
% 2.87/1.02      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 2.87/1.02      inference(cnf_transformation,[],[f39]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_2396,plain,
% 2.87/1.02      ( r2_hidden(sK0(k9_relat_1(sK5,sK4)),k9_relat_1(sK5,sK4))
% 2.87/1.02      | v1_xboole_0(k9_relat_1(sK5,sK4)) ),
% 2.87/1.02      inference(instantiation,[status(thm)],[c_0]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_2397,plain,
% 2.87/1.02      ( r2_hidden(sK0(k9_relat_1(sK5,sK4)),k9_relat_1(sK5,sK4)) = iProver_top
% 2.87/1.02      | v1_xboole_0(k9_relat_1(sK5,sK4)) = iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_2396]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_2059,plain,
% 2.87/1.02      ( ~ r2_hidden(X0,k9_relat_1(sK5,X1))
% 2.87/1.02      | r2_hidden(k4_tarski(sK1(X0,X1,sK5),X0),sK5)
% 2.87/1.02      | ~ v1_relat_1(sK5) ),
% 2.87/1.02      inference(instantiation,[status(thm)],[c_9]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_2730,plain,
% 2.87/1.02      ( r2_hidden(k4_tarski(sK1(sK0(k9_relat_1(sK5,sK4)),sK4,sK5),sK0(k9_relat_1(sK5,sK4))),sK5)
% 2.87/1.02      | ~ r2_hidden(sK0(k9_relat_1(sK5,sK4)),k9_relat_1(sK5,sK4))
% 2.87/1.02      | ~ v1_relat_1(sK5) ),
% 2.87/1.02      inference(instantiation,[status(thm)],[c_2059]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_2734,plain,
% 2.87/1.02      ( r2_hidden(k4_tarski(sK1(sK0(k9_relat_1(sK5,sK4)),sK4,sK5),sK0(k9_relat_1(sK5,sK4))),sK5) = iProver_top
% 2.87/1.02      | r2_hidden(sK0(k9_relat_1(sK5,sK4)),k9_relat_1(sK5,sK4)) != iProver_top
% 2.87/1.02      | v1_relat_1(sK5) != iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_2730]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_3248,plain,
% 2.87/1.02      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK5) | sK5 != X0 ),
% 2.87/1.02      inference(instantiation,[status(thm)],[c_1393]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_3250,plain,
% 2.87/1.02      ( v1_xboole_0(sK5)
% 2.87/1.02      | ~ v1_xboole_0(k1_xboole_0)
% 2.87/1.02      | sK5 != k1_xboole_0 ),
% 2.87/1.02      inference(instantiation,[status(thm)],[c_3248]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_3430,plain,
% 2.87/1.02      ( ~ r2_hidden(k4_tarski(sK1(sK0(k9_relat_1(sK5,sK4)),sK4,sK5),sK0(k9_relat_1(sK5,sK4))),sK5)
% 2.87/1.02      | ~ v1_xboole_0(sK5) ),
% 2.87/1.02      inference(instantiation,[status(thm)],[c_1]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_3431,plain,
% 2.87/1.02      ( r2_hidden(k4_tarski(sK1(sK0(k9_relat_1(sK5,sK4)),sK4,sK5),sK0(k9_relat_1(sK5,sK4))),sK5) != iProver_top
% 2.87/1.02      | v1_xboole_0(sK5) != iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_3430]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_6,plain,
% 2.87/1.02      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.87/1.02      inference(cnf_transformation,[],[f41]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_1805,plain,
% 2.87/1.02      ( m1_subset_1(X0,X1) != iProver_top
% 2.87/1.02      | r2_hidden(X0,X1) = iProver_top
% 2.87/1.02      | v1_xboole_0(X1) = iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_2597,plain,
% 2.87/1.02      ( r2_hidden(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top
% 2.87/1.02      | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.87/1.02      inference(superposition,[status(thm)],[c_1795,c_1805]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_4255,plain,
% 2.87/1.02      ( r2_hidden(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top
% 2.87/1.02      | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
% 2.87/1.02      inference(demodulation,[status(thm)],[c_4252,c_2597]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_4,plain,
% 2.87/1.02      ( ~ m1_subset_1(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 2.87/1.02      inference(cnf_transformation,[],[f43]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_1806,plain,
% 2.87/1.02      ( m1_subset_1(X0,X1) != iProver_top
% 2.87/1.02      | v1_xboole_0(X1) != iProver_top
% 2.87/1.02      | v1_xboole_0(X0) = iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_2609,plain,
% 2.87/1.02      ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 2.87/1.02      | v1_xboole_0(sK5) = iProver_top ),
% 2.87/1.02      inference(superposition,[status(thm)],[c_1795,c_1806]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_4256,plain,
% 2.87/1.02      ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
% 2.87/1.02      | v1_xboole_0(sK5) = iProver_top ),
% 2.87/1.02      inference(demodulation,[status(thm)],[c_4252,c_2609]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_4661,plain,
% 2.87/1.02      ( sK2 = k1_xboole_0 ),
% 2.87/1.02      inference(global_propositional_subsumption,
% 2.87/1.02                [status(thm)],
% 2.87/1.02                [c_4275,c_25,c_30,c_24,c_31,c_2,c_685,c_1981,c_1982,
% 2.87/1.02                 c_1989,c_1990,c_2208,c_2210,c_2209,c_2396,c_2397,c_2730,
% 2.87/1.02                 c_2734,c_2756,c_3250,c_3430,c_3431,c_3855,c_4186,c_4255,
% 2.87/1.02                 c_4256]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_4258,plain,
% 2.87/1.02      ( k1_relset_1(sK2,k1_xboole_0,sK5) = k1_relat_1(sK5) ),
% 2.87/1.02      inference(demodulation,[status(thm)],[c_4252,c_2542]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_4666,plain,
% 2.87/1.02      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_relat_1(sK5) ),
% 2.87/1.02      inference(demodulation,[status(thm)],[c_4661,c_4258]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_4667,plain,
% 2.87/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 2.87/1.02      inference(demodulation,[status(thm)],[c_4661,c_4262]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_21,plain,
% 2.87/1.02      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 2.87/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.87/1.02      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 2.87/1.02      inference(cnf_transformation,[],[f71]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_543,plain,
% 2.87/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.87/1.02      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 2.87/1.02      | sK3 != X1
% 2.87/1.02      | sK2 != k1_xboole_0
% 2.87/1.02      | sK5 != X0 ),
% 2.87/1.02      inference(resolution_lifted,[status(thm)],[c_21,c_26]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_544,plain,
% 2.87/1.02      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
% 2.87/1.02      | k1_relset_1(k1_xboole_0,sK3,sK5) = k1_xboole_0
% 2.87/1.02      | sK2 != k1_xboole_0 ),
% 2.87/1.02      inference(unflattening,[status(thm)],[c_543]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_1789,plain,
% 2.87/1.02      ( k1_relset_1(k1_xboole_0,sK3,sK5) = k1_xboole_0
% 2.87/1.02      | sK2 != k1_xboole_0
% 2.87/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_544]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_4260,plain,
% 2.87/1.02      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0
% 2.87/1.02      | sK2 != k1_xboole_0
% 2.87/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 2.87/1.02      inference(demodulation,[status(thm)],[c_4252,c_1789]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_4440,plain,
% 2.87/1.02      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0
% 2.87/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 2.87/1.02      inference(global_propositional_subsumption,
% 2.87/1.02                [status(thm)],
% 2.87/1.02                [c_4260,c_25,c_30,c_24,c_31,c_2,c_685,c_1981,c_1982,
% 2.87/1.02                 c_1989,c_1990,c_2208,c_2210,c_2209,c_2396,c_2397,c_2730,
% 2.87/1.02                 c_2734,c_2756,c_3250,c_3430,c_3431,c_3855,c_4186,c_4255,
% 2.87/1.02                 c_4256]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_4750,plain,
% 2.87/1.02      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0 ),
% 2.87/1.02      inference(superposition,[status(thm)],[c_4667,c_4440]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_4922,plain,
% 2.87/1.02      ( k1_relat_1(sK5) = k1_xboole_0 ),
% 2.87/1.02      inference(light_normalisation,[status(thm)],[c_4666,c_4750]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_4377,plain,
% 2.87/1.02      ( ~ v1_xboole_0(X0)
% 2.87/1.02      | v1_xboole_0(k1_relat_1(sK5))
% 2.87/1.02      | k1_relat_1(sK5) != X0 ),
% 2.87/1.02      inference(instantiation,[status(thm)],[c_1393]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_4379,plain,
% 2.87/1.02      ( v1_xboole_0(k1_relat_1(sK5))
% 2.87/1.02      | ~ v1_xboole_0(k1_xboole_0)
% 2.87/1.02      | k1_relat_1(sK5) != k1_xboole_0 ),
% 2.87/1.02      inference(instantiation,[status(thm)],[c_4377]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_3449,plain,
% 2.87/1.02      ( ~ r2_hidden(sK1(sK0(k9_relat_1(sK5,sK4)),sK4,sK5),k1_relat_1(sK5))
% 2.87/1.02      | ~ v1_xboole_0(k1_relat_1(sK5)) ),
% 2.87/1.02      inference(instantiation,[status(thm)],[c_1]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_2060,plain,
% 2.87/1.02      ( ~ r2_hidden(X0,k9_relat_1(sK5,X1))
% 2.87/1.02      | r2_hidden(sK1(X0,X1,sK5),k1_relat_1(sK5))
% 2.87/1.02      | ~ v1_relat_1(sK5) ),
% 2.87/1.02      inference(instantiation,[status(thm)],[c_10]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_2731,plain,
% 2.87/1.02      ( r2_hidden(sK1(sK0(k9_relat_1(sK5,sK4)),sK4,sK5),k1_relat_1(sK5))
% 2.87/1.02      | ~ r2_hidden(sK0(k9_relat_1(sK5,sK4)),k9_relat_1(sK5,sK4))
% 2.87/1.02      | ~ v1_relat_1(sK5) ),
% 2.87/1.02      inference(instantiation,[status(thm)],[c_2060]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(contradiction,plain,
% 2.87/1.02      ( $false ),
% 2.87/1.02      inference(minisat,
% 2.87/1.02                [status(thm)],
% 2.87/1.02                [c_4922,c_4379,c_3449,c_2731,c_2396,c_2209,c_2208,c_1989,
% 2.87/1.02                 c_1981,c_2,c_24,c_25]) ).
% 2.87/1.02  
% 2.87/1.02  
% 2.87/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.87/1.02  
% 2.87/1.02  ------                               Statistics
% 2.87/1.02  
% 2.87/1.02  ------ General
% 2.87/1.02  
% 2.87/1.02  abstr_ref_over_cycles:                  0
% 2.87/1.02  abstr_ref_under_cycles:                 0
% 2.87/1.02  gc_basic_clause_elim:                   0
% 2.87/1.02  forced_gc_time:                         0
% 2.87/1.02  parsing_time:                           0.007
% 2.87/1.02  unif_index_cands_time:                  0.
% 2.87/1.02  unif_index_add_time:                    0.
% 2.87/1.02  orderings_time:                         0.
% 2.87/1.02  out_proof_time:                         0.015
% 2.87/1.02  total_time:                             0.125
% 2.87/1.02  num_of_symbols:                         53
% 2.87/1.02  num_of_terms:                           3047
% 2.87/1.02  
% 2.87/1.02  ------ Preprocessing
% 2.87/1.02  
% 2.87/1.02  num_of_splits:                          0
% 2.87/1.02  num_of_split_atoms:                     0
% 2.87/1.02  num_of_reused_defs:                     0
% 2.87/1.02  num_eq_ax_congr_red:                    25
% 2.87/1.02  num_of_sem_filtered_clauses:            1
% 2.87/1.02  num_of_subtypes:                        0
% 2.87/1.02  monotx_restored_types:                  0
% 2.87/1.02  sat_num_of_epr_types:                   0
% 2.87/1.02  sat_num_of_non_cyclic_types:            0
% 2.87/1.02  sat_guarded_non_collapsed_types:        0
% 2.87/1.02  num_pure_diseq_elim:                    0
% 2.87/1.02  simp_replaced_by:                       0
% 2.87/1.02  res_preprocessed:                       124
% 2.87/1.02  prep_upred:                             0
% 2.87/1.02  prep_unflattend:                        98
% 2.87/1.02  smt_new_axioms:                         0
% 2.87/1.02  pred_elim_cands:                        4
% 2.87/1.02  pred_elim:                              2
% 2.87/1.02  pred_elim_cl:                           5
% 2.87/1.02  pred_elim_cycles:                       6
% 2.87/1.02  merged_defs:                            0
% 2.87/1.02  merged_defs_ncl:                        0
% 2.87/1.02  bin_hyper_res:                          0
% 2.87/1.02  prep_cycles:                            4
% 2.87/1.02  pred_elim_time:                         0.01
% 2.87/1.02  splitting_time:                         0.
% 2.87/1.02  sem_filter_time:                        0.
% 2.87/1.02  monotx_time:                            0.
% 2.87/1.02  subtype_inf_time:                       0.
% 2.87/1.02  
% 2.87/1.02  ------ Problem properties
% 2.87/1.02  
% 2.87/1.02  clauses:                                23
% 2.87/1.02  conjectures:                            3
% 2.87/1.02  epr:                                    6
% 2.87/1.02  horn:                                   19
% 2.87/1.02  ground:                                 6
% 2.87/1.02  unary:                                  3
% 2.87/1.02  binary:                                 7
% 2.87/1.02  lits:                                   59
% 2.87/1.02  lits_eq:                                11
% 2.87/1.02  fd_pure:                                0
% 2.87/1.02  fd_pseudo:                              0
% 2.87/1.02  fd_cond:                                0
% 2.87/1.02  fd_pseudo_cond:                         1
% 2.87/1.02  ac_symbols:                             0
% 2.87/1.02  
% 2.87/1.02  ------ Propositional Solver
% 2.87/1.02  
% 2.87/1.02  prop_solver_calls:                      28
% 2.87/1.02  prop_fast_solver_calls:                 1022
% 2.87/1.02  smt_solver_calls:                       0
% 2.87/1.02  smt_fast_solver_calls:                  0
% 2.87/1.02  prop_num_of_clauses:                    1367
% 2.87/1.02  prop_preprocess_simplified:             4958
% 2.87/1.02  prop_fo_subsumed:                       24
% 2.87/1.02  prop_solver_time:                       0.
% 2.87/1.02  smt_solver_time:                        0.
% 2.87/1.02  smt_fast_solver_time:                   0.
% 2.87/1.02  prop_fast_solver_time:                  0.
% 2.87/1.02  prop_unsat_core_time:                   0.
% 2.87/1.02  
% 2.87/1.02  ------ QBF
% 2.87/1.02  
% 2.87/1.02  qbf_q_res:                              0
% 2.87/1.02  qbf_num_tautologies:                    0
% 2.87/1.02  qbf_prep_cycles:                        0
% 2.87/1.02  
% 2.87/1.02  ------ BMC1
% 2.87/1.02  
% 2.87/1.02  bmc1_current_bound:                     -1
% 2.87/1.02  bmc1_last_solved_bound:                 -1
% 2.87/1.02  bmc1_unsat_core_size:                   -1
% 2.87/1.02  bmc1_unsat_core_parents_size:           -1
% 2.87/1.02  bmc1_merge_next_fun:                    0
% 2.87/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.87/1.02  
% 2.87/1.02  ------ Instantiation
% 2.87/1.02  
% 2.87/1.02  inst_num_of_clauses:                    393
% 2.87/1.02  inst_num_in_passive:                    3
% 2.87/1.02  inst_num_in_active:                     306
% 2.87/1.02  inst_num_in_unprocessed:                84
% 2.87/1.02  inst_num_of_loops:                      340
% 2.87/1.02  inst_num_of_learning_restarts:          0
% 2.87/1.02  inst_num_moves_active_passive:          29
% 2.87/1.02  inst_lit_activity:                      0
% 2.87/1.02  inst_lit_activity_moves:                0
% 2.87/1.02  inst_num_tautologies:                   0
% 2.87/1.02  inst_num_prop_implied:                  0
% 2.87/1.02  inst_num_existing_simplified:           0
% 2.87/1.02  inst_num_eq_res_simplified:             0
% 2.87/1.02  inst_num_child_elim:                    0
% 2.87/1.02  inst_num_of_dismatching_blockings:      49
% 2.87/1.02  inst_num_of_non_proper_insts:           448
% 2.87/1.02  inst_num_of_duplicates:                 0
% 2.87/1.02  inst_inst_num_from_inst_to_res:         0
% 2.87/1.02  inst_dismatching_checking_time:         0.
% 2.87/1.02  
% 2.87/1.02  ------ Resolution
% 2.87/1.02  
% 2.87/1.02  res_num_of_clauses:                     0
% 2.87/1.02  res_num_in_passive:                     0
% 2.87/1.02  res_num_in_active:                      0
% 2.87/1.02  res_num_of_loops:                       128
% 2.87/1.02  res_forward_subset_subsumed:            42
% 2.87/1.02  res_backward_subset_subsumed:           0
% 2.87/1.02  res_forward_subsumed:                   0
% 2.87/1.02  res_backward_subsumed:                  0
% 2.87/1.02  res_forward_subsumption_resolution:     0
% 2.87/1.02  res_backward_subsumption_resolution:    0
% 2.87/1.02  res_clause_to_clause_subsumption:       204
% 2.87/1.02  res_orphan_elimination:                 0
% 2.87/1.02  res_tautology_del:                      87
% 2.87/1.02  res_num_eq_res_simplified:              0
% 2.87/1.02  res_num_sel_changes:                    0
% 2.87/1.02  res_moves_from_active_to_pass:          0
% 2.87/1.02  
% 2.87/1.02  ------ Superposition
% 2.87/1.02  
% 2.87/1.02  sup_time_total:                         0.
% 2.87/1.02  sup_time_generating:                    0.
% 2.87/1.02  sup_time_sim_full:                      0.
% 2.87/1.02  sup_time_sim_immed:                     0.
% 2.87/1.02  
% 2.87/1.02  sup_num_of_clauses:                     68
% 2.87/1.02  sup_num_in_active:                      45
% 2.87/1.02  sup_num_in_passive:                     23
% 2.87/1.02  sup_num_of_loops:                       66
% 2.87/1.02  sup_fw_superposition:                   42
% 2.87/1.02  sup_bw_superposition:                   61
% 2.87/1.02  sup_immediate_simplified:               17
% 2.87/1.02  sup_given_eliminated:                   1
% 2.87/1.02  comparisons_done:                       0
% 2.87/1.02  comparisons_avoided:                    3
% 2.87/1.02  
% 2.87/1.02  ------ Simplifications
% 2.87/1.02  
% 2.87/1.02  
% 2.87/1.02  sim_fw_subset_subsumed:                 13
% 2.87/1.02  sim_bw_subset_subsumed:                 9
% 2.87/1.02  sim_fw_subsumed:                        3
% 2.87/1.02  sim_bw_subsumed:                        2
% 2.87/1.02  sim_fw_subsumption_res:                 1
% 2.87/1.02  sim_bw_subsumption_res:                 0
% 2.87/1.02  sim_tautology_del:                      7
% 2.87/1.02  sim_eq_tautology_del:                   2
% 2.87/1.02  sim_eq_res_simp:                        1
% 2.87/1.02  sim_fw_demodulated:                     0
% 2.87/1.02  sim_bw_demodulated:                     18
% 2.87/1.02  sim_light_normalised:                   2
% 2.87/1.02  sim_joinable_taut:                      0
% 2.87/1.02  sim_joinable_simp:                      0
% 2.87/1.02  sim_ac_normalised:                      0
% 2.87/1.02  sim_smt_subsumption:                    0
% 2.87/1.02  
%------------------------------------------------------------------------------
