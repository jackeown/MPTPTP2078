%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:10:16 EST 2020

% Result     : Theorem 3.77s
% Output     : CNFRefutation 3.77s
% Verified   : 
% Statistics : Number of formulae       :  149 (1175 expanded)
%              Number of clauses        :   84 ( 402 expanded)
%              Number of leaves         :   17 ( 304 expanded)
%              Depth                    :   28
%              Number of atoms          :  484 (6359 expanded)
%              Number of equality atoms :  204 ( 740 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_2(X3,X1,X2)
                & v1_funct_1(X3) )
             => ( ! [X4] :
                    ( m1_subset_1(X4,X1)
                   => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) )
               => r1_tarski(k2_relset_1(X1,X2,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & v1_funct_2(X3,X1,X2)
                  & v1_funct_1(X3) )
               => ( ! [X4] :
                      ( m1_subset_1(X4,X1)
                     => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) )
                 => r1_tarski(k2_relset_1(X1,X2,X3),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f33,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                  | ~ m1_subset_1(X4,X1) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f34,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                  | ~ m1_subset_1(X4,X1) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(X1) ) ),
    inference(flattening,[],[f33])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
          & ! [X4] :
              ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
              | ~ m1_subset_1(X4,X1) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
     => ( ~ r1_tarski(k2_relset_1(X1,X2,sK7),X0)
        & ! [X4] :
            ( r2_hidden(k3_funct_2(X1,X2,sK7,X4),X0)
            | ~ m1_subset_1(X4,X1) )
        & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK7,X1,X2)
        & v1_funct_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                  | ~ m1_subset_1(X4,X1) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
     => ( ? [X3] :
            ( ~ r1_tarski(k2_relset_1(X1,sK6,X3),X0)
            & ! [X4] :
                ( r2_hidden(k3_funct_2(X1,sK6,X3,X4),X0)
                | ~ m1_subset_1(X4,X1) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK6)))
            & v1_funct_2(X3,X1,sK6)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
                & ! [X4] :
                    ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                    | ~ m1_subset_1(X4,X1) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_2(X3,X1,X2)
                & v1_funct_1(X3) )
            & ~ v1_xboole_0(X2) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(sK5,X2,X3),sK4)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(sK5,X2,X3,X4),sK4)
                  | ~ m1_subset_1(X4,sK5) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,X2)))
              & v1_funct_2(X3,sK5,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ~ r1_tarski(k2_relset_1(sK5,sK6,sK7),sK4)
    & ! [X4] :
        ( r2_hidden(k3_funct_2(sK5,sK6,sK7,X4),sK4)
        | ~ m1_subset_1(X4,sK5) )
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & v1_funct_2(sK7,sK5,sK6)
    & v1_funct_1(sK7)
    & ~ v1_xboole_0(sK6)
    & ~ v1_xboole_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f34,f50,f49,f48])).

fof(f89,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f51])).

fof(f12,axiom,(
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

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f88,plain,(
    v1_funct_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f51])).

fof(f14,axiom,(
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

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(k1_funct_1(X2,sK3(X0,X1,X2)),X1)
        & r2_hidden(sK3(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ( ~ r2_hidden(k1_funct_1(X2,sK3(X0,X1,X2)),X1)
        & r2_hidden(sK3(X0,X1,X2),X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f46])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(sK3(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f104,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | r2_hidden(sK3(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f83])).

fof(f87,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f51])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f91,plain,(
    ~ r1_tarski(k2_relset_1(sK5,sK6,sK7),sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f85,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f90,plain,(
    ! [X4] :
      ( r2_hidden(k3_funct_2(sK5,sK6,sK7,X4),sK4)
      | ~ m1_subset_1(X4,sK5) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(k1_funct_1(X2,sK3(X0,X1,X2)),X1)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f103,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | ~ r2_hidden(k1_funct_1(X2,sK3(k1_relat_1(X2),X1,X2)),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f84])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f35])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f92,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f54])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f93,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f53])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1445,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1453,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4723,plain,
    ( k1_relset_1(sK5,sK6,sK7) = sK5
    | sK6 = k1_xboole_0
    | v1_funct_2(sK7,sK5,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1445,c_1453])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1460,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3262,plain,
    ( k1_relset_1(sK5,sK6,sK7) = k1_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_1445,c_1460])).

cnf(c_4733,plain,
    ( k1_relat_1(sK7) = sK5
    | sK6 = k1_xboole_0
    | v1_funct_2(sK7,sK5,sK6) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4723,c_3262])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_43,plain,
    ( v1_funct_2(sK7,sK5,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_4895,plain,
    ( sK6 = k1_xboole_0
    | k1_relat_1(sK7) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4733,c_43])).

cnf(c_4896,plain,
    ( k1_relat_1(sK7) = sK5
    | sK6 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4895])).

cnf(c_28,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | r2_hidden(sK3(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1450,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r2_hidden(sK3(k1_relat_1(X0),X1,X0),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_5425,plain,
    ( sK6 = k1_xboole_0
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),X0))) = iProver_top
    | r2_hidden(sK3(sK5,X0,sK7),sK5) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_4896,c_1450])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_42,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_44,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_6,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1805,plain,
    ( r1_tarski(sK7,k2_zfmisc_1(sK5,sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1806,plain,
    ( r1_tarski(sK7,k2_zfmisc_1(sK5,sK6)) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1805])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_251,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_324,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_7,c_251])).

cnf(c_1952,plain,
    ( ~ r1_tarski(sK7,k2_zfmisc_1(sK5,sK6))
    | ~ v1_relat_1(k2_zfmisc_1(sK5,sK6))
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_324])).

cnf(c_1954,plain,
    ( r1_tarski(sK7,k2_zfmisc_1(sK5,sK6)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK5,sK6)) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1952])).

cnf(c_10,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2082,plain,
    ( v1_relat_1(k2_zfmisc_1(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2083,plain,
    ( v1_relat_1(k2_zfmisc_1(sK5,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2082])).

cnf(c_5943,plain,
    ( sK6 = k1_xboole_0
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),X0))) = iProver_top
    | r2_hidden(sK3(sK5,X0,sK7),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5425,c_42,c_44,c_1806,c_1954,c_2083])).

cnf(c_5953,plain,
    ( sK6 = k1_xboole_0
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,X0))) = iProver_top
    | r2_hidden(sK3(sK5,X0,sK7),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4896,c_5943])).

cnf(c_6138,plain,
    ( k1_relset_1(sK5,X0,sK7) = k1_relat_1(sK7)
    | sK6 = k1_xboole_0
    | r2_hidden(sK3(sK5,X0,sK7),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_5953,c_1460])).

cnf(c_9,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1469,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1459,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2495,plain,
    ( k2_relset_1(sK5,sK6,sK7) = k2_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_1445,c_1459])).

cnf(c_33,negated_conjecture,
    ( ~ r1_tarski(k2_relset_1(sK5,sK6,sK7),sK4) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1447,plain,
    ( r1_tarski(k2_relset_1(sK5,sK6,sK7),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_2715,plain,
    ( r1_tarski(k2_relat_1(sK7),sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2495,c_1447])).

cnf(c_3595,plain,
    ( v5_relat_1(sK7,sK4) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1469,c_2715])).

cnf(c_17,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1461,plain,
    ( v5_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_5958,plain,
    ( sK6 = k1_xboole_0
    | v5_relat_1(sK7,X0) = iProver_top
    | r2_hidden(sK3(sK5,X0,sK7),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_5943,c_1461])).

cnf(c_4,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1473,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6372,plain,
    ( sK6 = k1_xboole_0
    | v5_relat_1(sK7,X0) = iProver_top
    | m1_subset_1(sK3(sK5,X0,sK7),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_5958,c_1473])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1452,plain,
    ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X3,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_6489,plain,
    ( k3_funct_2(sK5,sK6,sK7,X0) = k1_funct_1(sK7,X0)
    | v1_funct_2(sK7,sK5,sK6) != iProver_top
    | m1_subset_1(X0,sK5) != iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1445,c_1452])).

cnf(c_39,negated_conjecture,
    ( ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_40,plain,
    ( v1_xboole_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_6758,plain,
    ( k3_funct_2(sK5,sK6,sK7,X0) = k1_funct_1(sK7,X0)
    | m1_subset_1(X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6489,c_40,c_42,c_43])).

cnf(c_7818,plain,
    ( k3_funct_2(sK5,sK6,sK7,sK3(sK5,X0,sK7)) = k1_funct_1(sK7,sK3(sK5,X0,sK7))
    | sK6 = k1_xboole_0
    | v5_relat_1(sK7,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6372,c_6758])).

cnf(c_3792,plain,
    ( v5_relat_1(sK7,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3595,c_44,c_1806,c_1954,c_2083])).

cnf(c_8332,plain,
    ( k3_funct_2(sK5,sK6,sK7,sK3(sK5,sK4,sK7)) = k1_funct_1(sK7,sK3(sK5,sK4,sK7))
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7818,c_3792])).

cnf(c_34,negated_conjecture,
    ( ~ m1_subset_1(X0,sK5)
    | r2_hidden(k3_funct_2(sK5,sK6,sK7,X0),sK4) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1446,plain,
    ( m1_subset_1(X0,sK5) != iProver_top
    | r2_hidden(k3_funct_2(sK5,sK6,sK7,X0),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_2059,plain,
    ( m1_subset_1(X0,sK5) != iProver_top
    | m1_subset_1(k3_funct_2(sK5,sK6,sK7,X0),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1446,c_1473])).

cnf(c_8552,plain,
    ( sK6 = k1_xboole_0
    | m1_subset_1(sK3(sK5,sK4,sK7),sK5) != iProver_top
    | m1_subset_1(k1_funct_1(sK7,sK3(sK5,sK4,sK7)),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_8332,c_2059])).

cnf(c_8553,plain,
    ( sK6 = k1_xboole_0
    | m1_subset_1(sK3(sK5,sK4,sK7),sK5) != iProver_top
    | r2_hidden(k1_funct_1(sK7,sK3(sK5,sK4,sK7)),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_8332,c_1446])).

cnf(c_27,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r2_hidden(k1_funct_1(X0,sK3(k1_relat_1(X0),X1,X0)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1451,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r2_hidden(k1_funct_1(X0,sK3(k1_relat_1(X0),X1,X0)),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_5795,plain,
    ( sK6 = k1_xboole_0
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),X0))) = iProver_top
    | r2_hidden(k1_funct_1(sK7,sK3(sK5,X0,sK7)),X0) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_4896,c_1451])).

cnf(c_6280,plain,
    ( sK6 = k1_xboole_0
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),X0))) = iProver_top
    | r2_hidden(k1_funct_1(sK7,sK3(sK5,X0,sK7)),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5795,c_42,c_44,c_1806,c_1954,c_2083])).

cnf(c_8783,plain,
    ( sK6 = k1_xboole_0
    | m1_subset_1(sK3(sK5,sK4,sK7),sK5) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8553,c_6280])).

cnf(c_8935,plain,
    ( sK6 = k1_xboole_0
    | v5_relat_1(sK7,sK4) = iProver_top
    | m1_subset_1(sK3(sK5,sK4,sK7),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_8783,c_1461])).

cnf(c_8989,plain,
    ( m1_subset_1(sK3(sK5,sK4,sK7),sK5) != iProver_top
    | sK6 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8552,c_44,c_1806,c_1954,c_2083,c_3595,c_8935])).

cnf(c_8990,plain,
    ( sK6 = k1_xboole_0
    | m1_subset_1(sK3(sK5,sK4,sK7),sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_8989])).

cnf(c_8996,plain,
    ( sK6 = k1_xboole_0
    | v5_relat_1(sK7,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_6372,c_8990])).

cnf(c_9171,plain,
    ( sK6 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6138,c_44,c_1806,c_1954,c_2083,c_3595,c_8996])).

cnf(c_1471,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2149,plain,
    ( r1_tarski(sK7,k2_zfmisc_1(sK5,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1445,c_1471])).

cnf(c_9193,plain,
    ( r1_tarski(sK7,k2_zfmisc_1(sK5,k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9171,c_2149])).

cnf(c_0,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_9215,plain,
    ( r1_tarski(sK7,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9193,c_0])).

cnf(c_1472,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2257,plain,
    ( v5_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_1461])).

cnf(c_2487,plain,
    ( v5_relat_1(X0,X1) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1472,c_2257])).

cnf(c_9347,plain,
    ( v5_relat_1(sK7,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9215,c_2487])).

cnf(c_11604,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_9347,c_3792])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:19:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.77/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.77/0.99  
% 3.77/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.77/0.99  
% 3.77/0.99  ------  iProver source info
% 3.77/0.99  
% 3.77/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.77/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.77/0.99  git: non_committed_changes: false
% 3.77/0.99  git: last_make_outside_of_git: false
% 3.77/0.99  
% 3.77/0.99  ------ 
% 3.77/0.99  ------ Parsing...
% 3.77/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.77/0.99  
% 3.77/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.77/0.99  
% 3.77/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.77/0.99  
% 3.77/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.77/0.99  ------ Proving...
% 3.77/0.99  ------ Problem Properties 
% 3.77/0.99  
% 3.77/0.99  
% 3.77/0.99  clauses                                 38
% 3.77/0.99  conjectures                             7
% 3.77/0.99  EPR                                     7
% 3.77/0.99  Horn                                    28
% 3.77/0.99  unary                                   9
% 3.77/0.99  binary                                  7
% 3.77/0.99  lits                                    109
% 3.77/0.99  lits eq                                 23
% 3.77/0.99  fd_pure                                 0
% 3.77/0.99  fd_pseudo                               0
% 3.77/0.99  fd_cond                                 4
% 3.77/0.99  fd_pseudo_cond                          3
% 3.77/0.99  AC symbols                              0
% 3.77/0.99  
% 3.77/0.99  ------ Input Options Time Limit: Unbounded
% 3.77/0.99  
% 3.77/0.99  
% 3.77/0.99  ------ 
% 3.77/0.99  Current options:
% 3.77/0.99  ------ 
% 3.77/0.99  
% 3.77/0.99  
% 3.77/0.99  
% 3.77/0.99  
% 3.77/0.99  ------ Proving...
% 3.77/0.99  
% 3.77/0.99  
% 3.77/0.99  % SZS status Theorem for theBenchmark.p
% 3.77/0.99  
% 3.77/0.99   Resolution empty clause
% 3.77/0.99  
% 3.77/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.77/0.99  
% 3.77/0.99  fof(f15,conjecture,(
% 3.77/0.99    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 3.77/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f16,negated_conjecture,(
% 3.77/0.99    ~! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 3.77/0.99    inference(negated_conjecture,[],[f15])).
% 3.77/0.99  
% 3.77/0.99  fof(f33,plain,(
% 3.77/0.99    ? [X0,X1] : (? [X2] : (? [X3] : ((~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 3.77/0.99    inference(ennf_transformation,[],[f16])).
% 3.77/0.99  
% 3.77/0.99  fof(f34,plain,(
% 3.77/0.99    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 3.77/0.99    inference(flattening,[],[f33])).
% 3.77/0.99  
% 3.77/0.99  fof(f50,plain,(
% 3.77/0.99    ( ! [X2,X0,X1] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (~r1_tarski(k2_relset_1(X1,X2,sK7),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,sK7,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK7,X1,X2) & v1_funct_1(sK7))) )),
% 3.77/0.99    introduced(choice_axiom,[])).
% 3.77/0.99  
% 3.77/0.99  fof(f49,plain,(
% 3.77/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (~r1_tarski(k2_relset_1(X1,sK6,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,sK6,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK6))) & v1_funct_2(X3,X1,sK6) & v1_funct_1(X3)) & ~v1_xboole_0(sK6))) )),
% 3.77/0.99    introduced(choice_axiom,[])).
% 3.77/0.99  
% 3.77/0.99  fof(f48,plain,(
% 3.77/0.99    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(sK5,X2,X3),sK4) & ! [X4] : (r2_hidden(k3_funct_2(sK5,X2,X3,X4),sK4) | ~m1_subset_1(X4,sK5)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,X2))) & v1_funct_2(X3,sK5,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK5))),
% 3.77/0.99    introduced(choice_axiom,[])).
% 3.77/0.99  
% 3.77/0.99  fof(f51,plain,(
% 3.77/0.99    ((~r1_tarski(k2_relset_1(sK5,sK6,sK7),sK4) & ! [X4] : (r2_hidden(k3_funct_2(sK5,sK6,sK7,X4),sK4) | ~m1_subset_1(X4,sK5)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK7,sK5,sK6) & v1_funct_1(sK7)) & ~v1_xboole_0(sK6)) & ~v1_xboole_0(sK5)),
% 3.77/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f34,f50,f49,f48])).
% 3.77/0.99  
% 3.77/0.99  fof(f89,plain,(
% 3.77/0.99    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 3.77/0.99    inference(cnf_transformation,[],[f51])).
% 3.77/0.99  
% 3.77/0.99  fof(f12,axiom,(
% 3.77/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.77/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f27,plain,(
% 3.77/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.77/0.99    inference(ennf_transformation,[],[f12])).
% 3.77/0.99  
% 3.77/0.99  fof(f28,plain,(
% 3.77/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.77/0.99    inference(flattening,[],[f27])).
% 3.77/0.99  
% 3.77/0.99  fof(f45,plain,(
% 3.77/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.77/0.99    inference(nnf_transformation,[],[f28])).
% 3.77/0.99  
% 3.77/0.99  fof(f72,plain,(
% 3.77/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.77/0.99    inference(cnf_transformation,[],[f45])).
% 3.77/0.99  
% 3.77/0.99  fof(f10,axiom,(
% 3.77/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.77/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f25,plain,(
% 3.77/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.77/0.99    inference(ennf_transformation,[],[f10])).
% 3.77/0.99  
% 3.77/0.99  fof(f70,plain,(
% 3.77/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.77/0.99    inference(cnf_transformation,[],[f25])).
% 3.77/0.99  
% 3.77/0.99  fof(f88,plain,(
% 3.77/0.99    v1_funct_2(sK7,sK5,sK6)),
% 3.77/0.99    inference(cnf_transformation,[],[f51])).
% 3.77/0.99  
% 3.77/0.99  fof(f14,axiom,(
% 3.77/0.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 3.77/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f31,plain,(
% 3.77/0.99    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.77/0.99    inference(ennf_transformation,[],[f14])).
% 3.77/0.99  
% 3.77/0.99  fof(f32,plain,(
% 3.77/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.77/0.99    inference(flattening,[],[f31])).
% 3.77/0.99  
% 3.77/0.99  fof(f46,plain,(
% 3.77/0.99    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) => (~r2_hidden(k1_funct_1(X2,sK3(X0,X1,X2)),X1) & r2_hidden(sK3(X0,X1,X2),X0)))),
% 3.77/0.99    introduced(choice_axiom,[])).
% 3.77/0.99  
% 3.77/0.99  fof(f47,plain,(
% 3.77/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~r2_hidden(k1_funct_1(X2,sK3(X0,X1,X2)),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.77/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f46])).
% 3.77/0.99  
% 3.77/0.99  fof(f83,plain,(
% 3.77/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(sK3(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f47])).
% 3.77/0.99  
% 3.77/0.99  fof(f104,plain,(
% 3.77/0.99    ( ! [X2,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | r2_hidden(sK3(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.77/0.99    inference(equality_resolution,[],[f83])).
% 3.77/0.99  
% 3.77/0.99  fof(f87,plain,(
% 3.77/0.99    v1_funct_1(sK7)),
% 3.77/0.99    inference(cnf_transformation,[],[f51])).
% 3.77/0.99  
% 3.77/0.99  fof(f4,axiom,(
% 3.77/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.77/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f37,plain,(
% 3.77/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.77/0.99    inference(nnf_transformation,[],[f4])).
% 3.77/0.99  
% 3.77/0.99  fof(f57,plain,(
% 3.77/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.77/0.99    inference(cnf_transformation,[],[f37])).
% 3.77/0.99  
% 3.77/0.99  fof(f5,axiom,(
% 3.77/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.77/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f20,plain,(
% 3.77/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.77/0.99    inference(ennf_transformation,[],[f5])).
% 3.77/0.99  
% 3.77/0.99  fof(f59,plain,(
% 3.77/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f20])).
% 3.77/0.99  
% 3.77/0.99  fof(f58,plain,(
% 3.77/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f37])).
% 3.77/0.99  
% 3.77/0.99  fof(f7,axiom,(
% 3.77/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.77/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f62,plain,(
% 3.77/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.77/0.99    inference(cnf_transformation,[],[f7])).
% 3.77/0.99  
% 3.77/0.99  fof(f6,axiom,(
% 3.77/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.77/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f21,plain,(
% 3.77/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.77/0.99    inference(ennf_transformation,[],[f6])).
% 3.77/0.99  
% 3.77/0.99  fof(f38,plain,(
% 3.77/0.99    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.77/0.99    inference(nnf_transformation,[],[f21])).
% 3.77/0.99  
% 3.77/0.99  fof(f60,plain,(
% 3.77/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f38])).
% 3.77/0.99  
% 3.77/0.99  fof(f11,axiom,(
% 3.77/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.77/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f26,plain,(
% 3.77/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.77/0.99    inference(ennf_transformation,[],[f11])).
% 3.77/0.99  
% 3.77/0.99  fof(f71,plain,(
% 3.77/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.77/0.99    inference(cnf_transformation,[],[f26])).
% 3.77/0.99  
% 3.77/0.99  fof(f91,plain,(
% 3.77/0.99    ~r1_tarski(k2_relset_1(sK5,sK6,sK7),sK4)),
% 3.77/0.99    inference(cnf_transformation,[],[f51])).
% 3.77/0.99  
% 3.77/0.99  fof(f9,axiom,(
% 3.77/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.77/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f17,plain,(
% 3.77/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.77/0.99    inference(pure_predicate_removal,[],[f9])).
% 3.77/0.99  
% 3.77/0.99  fof(f24,plain,(
% 3.77/0.99    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.77/0.99    inference(ennf_transformation,[],[f17])).
% 3.77/0.99  
% 3.77/0.99  fof(f69,plain,(
% 3.77/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.77/0.99    inference(cnf_transformation,[],[f24])).
% 3.77/0.99  
% 3.77/0.99  fof(f3,axiom,(
% 3.77/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.77/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f19,plain,(
% 3.77/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.77/0.99    inference(ennf_transformation,[],[f3])).
% 3.77/0.99  
% 3.77/0.99  fof(f56,plain,(
% 3.77/0.99    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f19])).
% 3.77/0.99  
% 3.77/0.99  fof(f13,axiom,(
% 3.77/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3))),
% 3.77/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f29,plain,(
% 3.77/0.99    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 3.77/0.99    inference(ennf_transformation,[],[f13])).
% 3.77/0.99  
% 3.77/0.99  fof(f30,plain,(
% 3.77/0.99    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 3.77/0.99    inference(flattening,[],[f29])).
% 3.77/0.99  
% 3.77/0.99  fof(f78,plain,(
% 3.77/0.99    ( ! [X2,X0,X3,X1] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f30])).
% 3.77/0.99  
% 3.77/0.99  fof(f85,plain,(
% 3.77/0.99    ~v1_xboole_0(sK5)),
% 3.77/0.99    inference(cnf_transformation,[],[f51])).
% 3.77/0.99  
% 3.77/0.99  fof(f90,plain,(
% 3.77/0.99    ( ! [X4] : (r2_hidden(k3_funct_2(sK5,sK6,sK7,X4),sK4) | ~m1_subset_1(X4,sK5)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f51])).
% 3.77/0.99  
% 3.77/0.99  fof(f84,plain,(
% 3.77/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(k1_funct_1(X2,sK3(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f47])).
% 3.77/0.99  
% 3.77/0.99  fof(f103,plain,(
% 3.77/0.99    ( ! [X2,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | ~r2_hidden(k1_funct_1(X2,sK3(k1_relat_1(X2),X1,X2)),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.77/0.99    inference(equality_resolution,[],[f84])).
% 3.77/0.99  
% 3.77/0.99  fof(f1,axiom,(
% 3.77/0.99    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.77/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f35,plain,(
% 3.77/0.99    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.77/0.99    inference(nnf_transformation,[],[f1])).
% 3.77/0.99  
% 3.77/0.99  fof(f36,plain,(
% 3.77/0.99    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.77/0.99    inference(flattening,[],[f35])).
% 3.77/0.99  
% 3.77/0.99  fof(f54,plain,(
% 3.77/0.99    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 3.77/0.99    inference(cnf_transformation,[],[f36])).
% 3.77/0.99  
% 3.77/0.99  fof(f92,plain,(
% 3.77/0.99    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.77/0.99    inference(equality_resolution,[],[f54])).
% 3.77/0.99  
% 3.77/0.99  fof(f53,plain,(
% 3.77/0.99    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 3.77/0.99    inference(cnf_transformation,[],[f36])).
% 3.77/0.99  
% 3.77/0.99  fof(f93,plain,(
% 3.77/0.99    ( ! [X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0) )),
% 3.77/0.99    inference(equality_resolution,[],[f53])).
% 3.77/0.99  
% 3.77/0.99  cnf(c_35,negated_conjecture,
% 3.77/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
% 3.77/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1445,plain,
% 3.77/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_25,plain,
% 3.77/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.77/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.77/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.77/0.99      | k1_xboole_0 = X2 ),
% 3.77/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1453,plain,
% 3.77/0.99      ( k1_relset_1(X0,X1,X2) = X0
% 3.77/0.99      | k1_xboole_0 = X1
% 3.77/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.77/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_4723,plain,
% 3.77/0.99      ( k1_relset_1(sK5,sK6,sK7) = sK5
% 3.77/0.99      | sK6 = k1_xboole_0
% 3.77/0.99      | v1_funct_2(sK7,sK5,sK6) != iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_1445,c_1453]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_18,plain,
% 3.77/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.77/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.77/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1460,plain,
% 3.77/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.77/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_3262,plain,
% 3.77/0.99      ( k1_relset_1(sK5,sK6,sK7) = k1_relat_1(sK7) ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_1445,c_1460]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_4733,plain,
% 3.77/0.99      ( k1_relat_1(sK7) = sK5
% 3.77/0.99      | sK6 = k1_xboole_0
% 3.77/0.99      | v1_funct_2(sK7,sK5,sK6) != iProver_top ),
% 3.77/0.99      inference(demodulation,[status(thm)],[c_4723,c_3262]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_36,negated_conjecture,
% 3.77/0.99      ( v1_funct_2(sK7,sK5,sK6) ),
% 3.77/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_43,plain,
% 3.77/0.99      ( v1_funct_2(sK7,sK5,sK6) = iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_4895,plain,
% 3.77/0.99      ( sK6 = k1_xboole_0 | k1_relat_1(sK7) = sK5 ),
% 3.77/0.99      inference(global_propositional_subsumption,[status(thm)],[c_4733,c_43]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_4896,plain,
% 3.77/0.99      ( k1_relat_1(sK7) = sK5 | sK6 = k1_xboole_0 ),
% 3.77/0.99      inference(renaming,[status(thm)],[c_4895]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_28,plain,
% 3.77/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.77/0.99      | r2_hidden(sK3(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 3.77/0.99      | ~ v1_funct_1(X0)
% 3.77/0.99      | ~ v1_relat_1(X0) ),
% 3.77/0.99      inference(cnf_transformation,[],[f104]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1450,plain,
% 3.77/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 3.77/0.99      | r2_hidden(sK3(k1_relat_1(X0),X1,X0),k1_relat_1(X0)) = iProver_top
% 3.77/0.99      | v1_funct_1(X0) != iProver_top
% 3.77/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_5425,plain,
% 3.77/0.99      ( sK6 = k1_xboole_0
% 3.77/0.99      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),X0))) = iProver_top
% 3.77/0.99      | r2_hidden(sK3(sK5,X0,sK7),sK5) = iProver_top
% 3.77/0.99      | v1_funct_1(sK7) != iProver_top
% 3.77/0.99      | v1_relat_1(sK7) != iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_4896,c_1450]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_37,negated_conjecture,
% 3.77/0.99      ( v1_funct_1(sK7) ),
% 3.77/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_42,plain,
% 3.77/0.99      ( v1_funct_1(sK7) = iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_44,plain,
% 3.77/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_6,plain,
% 3.77/0.99      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.77/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1805,plain,
% 3.77/0.99      ( r1_tarski(sK7,k2_zfmisc_1(sK5,sK6))
% 3.77/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
% 3.77/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1806,plain,
% 3.77/0.99      ( r1_tarski(sK7,k2_zfmisc_1(sK5,sK6)) = iProver_top
% 3.77/0.99      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_1805]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_7,plain,
% 3.77/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.77/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_5,plain,
% 3.77/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.77/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_251,plain,
% 3.77/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.77/0.99      inference(prop_impl,[status(thm)],[c_5]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_324,plain,
% 3.77/0.99      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.77/0.99      inference(bin_hyper_res,[status(thm)],[c_7,c_251]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1952,plain,
% 3.77/0.99      ( ~ r1_tarski(sK7,k2_zfmisc_1(sK5,sK6))
% 3.77/0.99      | ~ v1_relat_1(k2_zfmisc_1(sK5,sK6))
% 3.77/0.99      | v1_relat_1(sK7) ),
% 3.77/0.99      inference(instantiation,[status(thm)],[c_324]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1954,plain,
% 3.77/0.99      ( r1_tarski(sK7,k2_zfmisc_1(sK5,sK6)) != iProver_top
% 3.77/0.99      | v1_relat_1(k2_zfmisc_1(sK5,sK6)) != iProver_top
% 3.77/0.99      | v1_relat_1(sK7) = iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_1952]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_10,plain,
% 3.77/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.77/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_2082,plain,
% 3.77/0.99      ( v1_relat_1(k2_zfmisc_1(sK5,sK6)) ),
% 3.77/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_2083,plain,
% 3.77/0.99      ( v1_relat_1(k2_zfmisc_1(sK5,sK6)) = iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_2082]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_5943,plain,
% 3.77/0.99      ( sK6 = k1_xboole_0
% 3.77/0.99      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),X0))) = iProver_top
% 3.77/0.99      | r2_hidden(sK3(sK5,X0,sK7),sK5) = iProver_top ),
% 3.77/0.99      inference(global_propositional_subsumption,
% 3.77/0.99                [status(thm)],
% 3.77/0.99                [c_5425,c_42,c_44,c_1806,c_1954,c_2083]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_5953,plain,
% 3.77/0.99      ( sK6 = k1_xboole_0
% 3.77/0.99      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,X0))) = iProver_top
% 3.77/0.99      | r2_hidden(sK3(sK5,X0,sK7),sK5) = iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_4896,c_5943]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_6138,plain,
% 3.77/0.99      ( k1_relset_1(sK5,X0,sK7) = k1_relat_1(sK7)
% 3.77/0.99      | sK6 = k1_xboole_0
% 3.77/0.99      | r2_hidden(sK3(sK5,X0,sK7),sK5) = iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_5953,c_1460]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_9,plain,
% 3.77/0.99      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.77/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1469,plain,
% 3.77/0.99      ( v5_relat_1(X0,X1) != iProver_top
% 3.77/0.99      | r1_tarski(k2_relat_1(X0),X1) = iProver_top
% 3.77/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_19,plain,
% 3.77/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.77/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.77/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1459,plain,
% 3.77/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.77/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_2495,plain,
% 3.77/0.99      ( k2_relset_1(sK5,sK6,sK7) = k2_relat_1(sK7) ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_1445,c_1459]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_33,negated_conjecture,
% 3.77/0.99      ( ~ r1_tarski(k2_relset_1(sK5,sK6,sK7),sK4) ),
% 3.77/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1447,plain,
% 3.77/0.99      ( r1_tarski(k2_relset_1(sK5,sK6,sK7),sK4) != iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_2715,plain,
% 3.77/0.99      ( r1_tarski(k2_relat_1(sK7),sK4) != iProver_top ),
% 3.77/0.99      inference(demodulation,[status(thm)],[c_2495,c_1447]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_3595,plain,
% 3.77/0.99      ( v5_relat_1(sK7,sK4) != iProver_top | v1_relat_1(sK7) != iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_1469,c_2715]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_17,plain,
% 3.77/0.99      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.77/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1461,plain,
% 3.77/0.99      ( v5_relat_1(X0,X1) = iProver_top
% 3.77/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_5958,plain,
% 3.77/0.99      ( sK6 = k1_xboole_0
% 3.77/0.99      | v5_relat_1(sK7,X0) = iProver_top
% 3.77/0.99      | r2_hidden(sK3(sK5,X0,sK7),sK5) = iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_5943,c_1461]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_4,plain,
% 3.77/0.99      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.77/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1473,plain,
% 3.77/0.99      ( m1_subset_1(X0,X1) = iProver_top | r2_hidden(X0,X1) != iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_6372,plain,
% 3.77/0.99      ( sK6 = k1_xboole_0
% 3.77/0.99      | v5_relat_1(sK7,X0) = iProver_top
% 3.77/0.99      | m1_subset_1(sK3(sK5,X0,sK7),sK5) = iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_5958,c_1473]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_26,plain,
% 3.77/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.77/0.99      | ~ m1_subset_1(X3,X1)
% 3.77/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.77/0.99      | v1_xboole_0(X1)
% 3.77/0.99      | ~ v1_funct_1(X0)
% 3.77/0.99      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 3.77/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1452,plain,
% 3.77/0.99      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
% 3.77/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.77/0.99      | m1_subset_1(X3,X0) != iProver_top
% 3.77/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.77/0.99      | v1_xboole_0(X0) = iProver_top
% 3.77/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_6489,plain,
% 3.77/0.99      ( k3_funct_2(sK5,sK6,sK7,X0) = k1_funct_1(sK7,X0)
% 3.77/0.99      | v1_funct_2(sK7,sK5,sK6) != iProver_top
% 3.77/0.99      | m1_subset_1(X0,sK5) != iProver_top
% 3.77/0.99      | v1_xboole_0(sK5) = iProver_top
% 3.77/0.99      | v1_funct_1(sK7) != iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_1445,c_1452]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_39,negated_conjecture,
% 3.77/0.99      ( ~ v1_xboole_0(sK5) ),
% 3.77/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_40,plain,
% 3.77/0.99      ( v1_xboole_0(sK5) != iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_6758,plain,
% 3.77/0.99      ( k3_funct_2(sK5,sK6,sK7,X0) = k1_funct_1(sK7,X0)
% 3.77/0.99      | m1_subset_1(X0,sK5) != iProver_top ),
% 3.77/0.99      inference(global_propositional_subsumption,
% 3.77/0.99                [status(thm)],
% 3.77/0.99                [c_6489,c_40,c_42,c_43]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_7818,plain,
% 3.77/0.99      ( k3_funct_2(sK5,sK6,sK7,sK3(sK5,X0,sK7)) = k1_funct_1(sK7,sK3(sK5,X0,sK7))
% 3.77/0.99      | sK6 = k1_xboole_0
% 3.77/0.99      | v5_relat_1(sK7,X0) = iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_6372,c_6758]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_3792,plain,
% 3.77/0.99      ( v5_relat_1(sK7,sK4) != iProver_top ),
% 3.77/0.99      inference(global_propositional_subsumption,
% 3.77/0.99                [status(thm)],
% 3.77/0.99                [c_3595,c_44,c_1806,c_1954,c_2083]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_8332,plain,
% 3.77/0.99      ( k3_funct_2(sK5,sK6,sK7,sK3(sK5,sK4,sK7)) = k1_funct_1(sK7,sK3(sK5,sK4,sK7))
% 3.77/0.99      | sK6 = k1_xboole_0 ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_7818,c_3792]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_34,negated_conjecture,
% 3.77/0.99      ( ~ m1_subset_1(X0,sK5) | r2_hidden(k3_funct_2(sK5,sK6,sK7,X0),sK4) ),
% 3.77/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1446,plain,
% 3.77/0.99      ( m1_subset_1(X0,sK5) != iProver_top
% 3.77/0.99      | r2_hidden(k3_funct_2(sK5,sK6,sK7,X0),sK4) = iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_2059,plain,
% 3.77/0.99      ( m1_subset_1(X0,sK5) != iProver_top
% 3.77/0.99      | m1_subset_1(k3_funct_2(sK5,sK6,sK7,X0),sK4) = iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_1446,c_1473]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_8552,plain,
% 3.77/0.99      ( sK6 = k1_xboole_0
% 3.77/0.99      | m1_subset_1(sK3(sK5,sK4,sK7),sK5) != iProver_top
% 3.77/0.99      | m1_subset_1(k1_funct_1(sK7,sK3(sK5,sK4,sK7)),sK4) = iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_8332,c_2059]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_8553,plain,
% 3.77/0.99      ( sK6 = k1_xboole_0
% 3.77/0.99      | m1_subset_1(sK3(sK5,sK4,sK7),sK5) != iProver_top
% 3.77/0.99      | r2_hidden(k1_funct_1(sK7,sK3(sK5,sK4,sK7)),sK4) = iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_8332,c_1446]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_27,plain,
% 3.77/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.77/0.99      | ~ r2_hidden(k1_funct_1(X0,sK3(k1_relat_1(X0),X1,X0)),X1)
% 3.77/0.99      | ~ v1_funct_1(X0)
% 3.77/0.99      | ~ v1_relat_1(X0) ),
% 3.77/0.99      inference(cnf_transformation,[],[f103]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1451,plain,
% 3.77/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 3.77/0.99      | r2_hidden(k1_funct_1(X0,sK3(k1_relat_1(X0),X1,X0)),X1) != iProver_top
% 3.77/0.99      | v1_funct_1(X0) != iProver_top
% 3.77/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_5795,plain,
% 3.77/0.99      ( sK6 = k1_xboole_0
% 3.77/0.99      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),X0))) = iProver_top
% 3.77/0.99      | r2_hidden(k1_funct_1(sK7,sK3(sK5,X0,sK7)),X0) != iProver_top
% 3.77/0.99      | v1_funct_1(sK7) != iProver_top
% 3.77/0.99      | v1_relat_1(sK7) != iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_4896,c_1451]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_6280,plain,
% 3.77/0.99      ( sK6 = k1_xboole_0
% 3.77/0.99      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),X0))) = iProver_top
% 3.77/0.99      | r2_hidden(k1_funct_1(sK7,sK3(sK5,X0,sK7)),X0) != iProver_top ),
% 3.77/0.99      inference(global_propositional_subsumption,
% 3.77/0.99                [status(thm)],
% 3.77/0.99                [c_5795,c_42,c_44,c_1806,c_1954,c_2083]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_8783,plain,
% 3.77/0.99      ( sK6 = k1_xboole_0
% 3.77/0.99      | m1_subset_1(sK3(sK5,sK4,sK7),sK5) != iProver_top
% 3.77/0.99      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),sK4))) = iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_8553,c_6280]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_8935,plain,
% 3.77/0.99      ( sK6 = k1_xboole_0
% 3.77/0.99      | v5_relat_1(sK7,sK4) = iProver_top
% 3.77/0.99      | m1_subset_1(sK3(sK5,sK4,sK7),sK5) != iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_8783,c_1461]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_8989,plain,
% 3.77/0.99      ( m1_subset_1(sK3(sK5,sK4,sK7),sK5) != iProver_top | sK6 = k1_xboole_0 ),
% 3.77/0.99      inference(global_propositional_subsumption,
% 3.77/0.99                [status(thm)],
% 3.77/0.99                [c_8552,c_44,c_1806,c_1954,c_2083,c_3595,c_8935]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_8990,plain,
% 3.77/0.99      ( sK6 = k1_xboole_0 | m1_subset_1(sK3(sK5,sK4,sK7),sK5) != iProver_top ),
% 3.77/0.99      inference(renaming,[status(thm)],[c_8989]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_8996,plain,
% 3.77/0.99      ( sK6 = k1_xboole_0 | v5_relat_1(sK7,sK4) = iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_6372,c_8990]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_9171,plain,
% 3.77/0.99      ( sK6 = k1_xboole_0 ),
% 3.77/0.99      inference(global_propositional_subsumption,
% 3.77/0.99                [status(thm)],
% 3.77/0.99                [c_6138,c_44,c_1806,c_1954,c_2083,c_3595,c_8996]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1471,plain,
% 3.77/0.99      ( r1_tarski(X0,X1) = iProver_top
% 3.77/0.99      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_2149,plain,
% 3.77/0.99      ( r1_tarski(sK7,k2_zfmisc_1(sK5,sK6)) = iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_1445,c_1471]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_9193,plain,
% 3.77/0.99      ( r1_tarski(sK7,k2_zfmisc_1(sK5,k1_xboole_0)) = iProver_top ),
% 3.77/0.99      inference(demodulation,[status(thm)],[c_9171,c_2149]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_0,plain,
% 3.77/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.77/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_9215,plain,
% 3.77/0.99      ( r1_tarski(sK7,k1_xboole_0) = iProver_top ),
% 3.77/0.99      inference(demodulation,[status(thm)],[c_9193,c_0]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1472,plain,
% 3.77/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.77/0.99      | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1,plain,
% 3.77/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.77/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_2257,plain,
% 3.77/0.99      ( v5_relat_1(X0,X1) = iProver_top
% 3.77/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_1,c_1461]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_2487,plain,
% 3.77/0.99      ( v5_relat_1(X0,X1) = iProver_top
% 3.77/0.99      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_1472,c_2257]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_9347,plain,
% 3.77/0.99      ( v5_relat_1(sK7,X0) = iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_9215,c_2487]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_11604,plain,
% 3.77/0.99      ( $false ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_9347,c_3792]) ).
% 3.77/0.99  
% 3.77/0.99  
% 3.77/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.77/0.99  
% 3.77/0.99  ------                               Statistics
% 3.77/0.99  
% 3.77/0.99  ------ Selected
% 3.77/0.99  
% 3.77/0.99  total_time:                             0.324
% 3.77/0.99  
%------------------------------------------------------------------------------
