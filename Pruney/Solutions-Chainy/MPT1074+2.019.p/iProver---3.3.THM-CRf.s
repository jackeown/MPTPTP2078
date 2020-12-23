%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:10:16 EST 2020

% Result     : Theorem 7.71s
% Output     : CNFRefutation 7.71s
% Verified   : 
% Statistics : Number of formulae       :  143 (1698 expanded)
%              Number of clauses        :   89 ( 557 expanded)
%              Number of leaves         :   15 ( 437 expanded)
%              Depth                    :   33
%              Number of atoms          :  452 (8974 expanded)
%              Number of equality atoms :  161 ( 835 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
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

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1)
        & r2_hidden(sK0(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ( ~ r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1)
        & r2_hidden(sK0(X0,X1,X2),X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f29])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(sK0(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f60,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | r2_hidden(sK0(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f50])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f11,conjecture,(
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

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
          & ! [X4] :
              ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
              | ~ m1_subset_1(X4,X1) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
     => ( ~ r1_tarski(k2_relset_1(X1,X2,sK4),X0)
        & ! [X4] :
            ( r2_hidden(k3_funct_2(X1,X2,sK4,X4),X0)
            | ~ m1_subset_1(X4,X1) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK4,X1,X2)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
            ( ~ r1_tarski(k2_relset_1(X1,sK3,X3),X0)
            & ! [X4] :
                ( r2_hidden(k3_funct_2(X1,sK3,X3,X4),X0)
                | ~ m1_subset_1(X4,X1) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK3)))
            & v1_funct_2(X3,X1,sK3)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
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
              ( ~ r1_tarski(k2_relset_1(sK2,X2,X3),sK1)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(sK2,X2,X3,X4),sK1)
                  | ~ m1_subset_1(X4,sK2) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,X2)))
              & v1_funct_2(X3,sK2,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)
    & ! [X4] :
        ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X4),sK1)
        | ~ m1_subset_1(X4,sK2) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4)
    & ~ v1_xboole_0(sK3)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f26,f33,f32,f31])).

fof(f56,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f52,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f54,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f55,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f57,plain,(
    ! [X4] :
      ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X4),sK1)
      | ~ m1_subset_1(X4,sK2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f59,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | ~ r2_hidden(k1_funct_1(X2,sK0(k1_relat_1(X2),X1,X2)),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f51])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f58,plain,(
    ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_12,plain,
    ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_965,plain,
    ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_976,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_974,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1760,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_976,c_974])).

cnf(c_2819,plain,
    ( r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X2))) = iProver_top
    | m1_subset_1(sK0(k1_relat_1(X0),X2,X0),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_965,c_1760])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_960,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_967,plain,
    ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X3,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1975,plain,
    ( k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0)
    | v1_funct_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(X0,sK2) != iProver_top
    | v1_xboole_0(sK2) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_960,c_967])).

cnf(c_23,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_24,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_26,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_27,plain,
    ( v1_funct_2(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3908,plain,
    ( k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0)
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1975,c_24,c_26,c_27])).

cnf(c_4257,plain,
    ( k3_funct_2(sK2,sK3,sK4,sK0(k1_relat_1(X0),X1,X0)) = k1_funct_1(sK4,sK0(k1_relat_1(X0),X1,X0))
    | r1_tarski(k1_relat_1(X0),sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2819,c_3908])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_975,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_9481,plain,
    ( k3_funct_2(sK2,sK3,sK4,sK0(k1_relat_1(X0),X1,X0)) = k1_funct_1(sK4,sK0(k1_relat_1(X0),X1,X0))
    | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),X1)) = iProver_top
    | r1_tarski(k1_relat_1(X0),sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4257,c_975])).

cnf(c_7,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_970,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1456,plain,
    ( v4_relat_1(sK4,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_960,c_970])).

cnf(c_5,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_972,plain,
    ( v4_relat_1(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_968,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_9485,plain,
    ( k3_funct_2(sK2,sK3,sK4,sK0(k1_relat_1(X0),X1,X0)) = k1_funct_1(sK4,sK0(k1_relat_1(X0),X1,X0))
    | k2_relset_1(k1_relat_1(X0),X1,X0) = k2_relat_1(X0)
    | r1_tarski(k1_relat_1(X0),sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4257,c_968])).

cnf(c_10132,plain,
    ( k3_funct_2(sK2,sK3,sK4,sK0(k1_relat_1(X0),X1,X0)) = k1_funct_1(sK4,sK0(k1_relat_1(X0),X1,X0))
    | k2_relset_1(k1_relat_1(X0),X1,X0) = k2_relat_1(X0)
    | v4_relat_1(X0,sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_972,c_9485])).

cnf(c_10142,plain,
    ( k3_funct_2(sK2,sK3,sK4,sK0(k1_relat_1(sK4),X0,sK4)) = k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4))
    | k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1456,c_10132])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_156,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_0])).

cnf(c_195,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_3,c_156])).

cnf(c_1231,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK2,sK3)) ),
    inference(resolution,[status(thm)],[c_1,c_19])).

cnf(c_1277,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK3))
    | v1_relat_1(sK4) ),
    inference(resolution,[status(thm)],[c_195,c_1231])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1282,plain,
    ( v1_relat_1(sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1277,c_6])).

cnf(c_10229,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k3_funct_2(sK2,sK3,sK4,sK0(k1_relat_1(sK4),X0,sK4)) = k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4))
    | k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_10142])).

cnf(c_11357,plain,
    ( k3_funct_2(sK2,sK3,sK4,sK0(k1_relat_1(sK4),X0,sK4)) = k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4))
    | k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10142,c_21,c_1282,c_10229])).

cnf(c_18,negated_conjecture,
    ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X0),sK1)
    | ~ m1_subset_1(X0,sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_961,plain,
    ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X0),sK1) = iProver_top
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_11363,plain,
    ( k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
    | r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),sK1) = iProver_top
    | m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_11357,c_961])).

cnf(c_28,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1172,plain,
    ( v4_relat_1(sK4,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1173,plain,
    ( v4_relat_1(sK4,sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1172])).

cnf(c_1206,plain,
    ( r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1207,plain,
    ( r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1206])).

cnf(c_1262,plain,
    ( ~ v4_relat_1(sK4,sK2)
    | r1_tarski(k1_relat_1(sK4),sK2)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1263,plain,
    ( v4_relat_1(sK4,sK2) != iProver_top
    | r1_tarski(k1_relat_1(sK4),sK2) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1262])).

cnf(c_1283,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1282])).

cnf(c_1377,plain,
    ( ~ r1_tarski(k1_relat_1(sK4),sK2)
    | m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1378,plain,
    ( r1_tarski(k1_relat_1(sK4),sK2) != iProver_top
    | m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1377])).

cnf(c_1491,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
    | k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1502,plain,
    ( k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1491])).

cnf(c_1302,plain,
    ( ~ r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
    | m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),X1)
    | ~ m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(X1)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2097,plain,
    ( ~ r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
    | m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),sK2)
    | ~ m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1302])).

cnf(c_2099,plain,
    ( r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) != iProver_top
    | m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),sK2) = iProver_top
    | m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2097])).

cnf(c_11469,plain,
    ( r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),sK1) = iProver_top
    | k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11363,c_26,c_28,c_1173,c_1207,c_1263,c_1283,c_1378,c_1502,c_2099])).

cnf(c_11470,plain,
    ( k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
    | r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),sK1) = iProver_top ),
    inference(renaming,[status(thm)],[c_11469])).

cnf(c_11,plain,
    ( ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_966,plain,
    ( r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_11478,plain,
    ( k2_relset_1(k1_relat_1(sK4),sK1,sK4) = k2_relat_1(sK4)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_11470,c_966])).

cnf(c_12123,plain,
    ( k2_relset_1(k1_relat_1(sK4),sK1,sK4) = k2_relat_1(sK4)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11478,c_26,c_1283])).

cnf(c_12129,plain,
    ( k2_relset_1(k1_relat_1(sK4),sK1,sK4) = k2_relat_1(sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_12123,c_968])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_969,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_12131,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_12129,c_969])).

cnf(c_12155,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),sK1)) != iProver_top
    | m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_976,c_12131])).

cnf(c_1548,plain,
    ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_960,c_968])).

cnf(c_17,negated_conjecture,
    ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_962,plain,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2205,plain,
    ( r1_tarski(k2_relat_1(sK4),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1548,c_962])).

cnf(c_1561,plain,
    ( r1_tarski(k2_relset_1(X0,X1,X2),X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_969,c_975])).

cnf(c_2437,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(k2_relset_1(X1,X2,X0),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_976,c_1561])).

cnf(c_12130,plain,
    ( r1_tarski(k2_relat_1(sK4),sK1) = iProver_top
    | r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12129,c_2437])).

cnf(c_12270,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12155,c_2205,c_12130])).

cnf(c_12275,plain,
    ( k3_funct_2(sK2,sK3,sK4,sK0(k1_relat_1(sK4),sK1,sK4)) = k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4))
    | r1_tarski(k1_relat_1(sK4),sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_9481,c_12270])).

cnf(c_14569,plain,
    ( k3_funct_2(sK2,sK3,sK4,sK0(k1_relat_1(sK4),sK1,sK4)) = k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12275,c_26,c_28,c_1173,c_1263,c_1283])).

cnf(c_14573,plain,
    ( r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)),sK1) = iProver_top
    | m1_subset_1(sK0(k1_relat_1(sK4),sK1,sK4),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_14569,c_961])).

cnf(c_14665,plain,
    ( m1_subset_1(sK0(k1_relat_1(sK4),sK1,sK4),sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_14573,c_966])).

cnf(c_15076,plain,
    ( m1_subset_1(sK0(k1_relat_1(sK4),sK1,sK4),sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14665,c_26,c_1283])).

cnf(c_15083,plain,
    ( r1_tarski(k1_relat_1(sK4),sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2819,c_15076])).

cnf(c_15861,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15083,c_26,c_28,c_1173,c_1263,c_1283])).

cnf(c_15866,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_15861,c_975])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15866,c_12130,c_2205])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:49:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.71/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.71/1.50  
% 7.71/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.71/1.50  
% 7.71/1.50  ------  iProver source info
% 7.71/1.50  
% 7.71/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.71/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.71/1.50  git: non_committed_changes: false
% 7.71/1.50  git: last_make_outside_of_git: false
% 7.71/1.50  
% 7.71/1.50  ------ 
% 7.71/1.50  
% 7.71/1.50  ------ Input Options
% 7.71/1.50  
% 7.71/1.50  --out_options                           all
% 7.71/1.50  --tptp_safe_out                         true
% 7.71/1.50  --problem_path                          ""
% 7.71/1.50  --include_path                          ""
% 7.71/1.50  --clausifier                            res/vclausify_rel
% 7.71/1.50  --clausifier_options                    --mode clausify
% 7.71/1.50  --stdin                                 false
% 7.71/1.50  --stats_out                             sel
% 7.71/1.50  
% 7.71/1.50  ------ General Options
% 7.71/1.50  
% 7.71/1.50  --fof                                   false
% 7.71/1.50  --time_out_real                         604.99
% 7.71/1.50  --time_out_virtual                      -1.
% 7.71/1.50  --symbol_type_check                     false
% 7.71/1.50  --clausify_out                          false
% 7.71/1.50  --sig_cnt_out                           false
% 7.71/1.50  --trig_cnt_out                          false
% 7.71/1.50  --trig_cnt_out_tolerance                1.
% 7.71/1.50  --trig_cnt_out_sk_spl                   false
% 7.71/1.50  --abstr_cl_out                          false
% 7.71/1.50  
% 7.71/1.50  ------ Global Options
% 7.71/1.50  
% 7.71/1.50  --schedule                              none
% 7.71/1.50  --add_important_lit                     false
% 7.71/1.50  --prop_solver_per_cl                    1000
% 7.71/1.50  --min_unsat_core                        false
% 7.71/1.50  --soft_assumptions                      false
% 7.71/1.50  --soft_lemma_size                       3
% 7.71/1.50  --prop_impl_unit_size                   0
% 7.71/1.50  --prop_impl_unit                        []
% 7.71/1.50  --share_sel_clauses                     true
% 7.71/1.50  --reset_solvers                         false
% 7.71/1.50  --bc_imp_inh                            [conj_cone]
% 7.71/1.50  --conj_cone_tolerance                   3.
% 7.71/1.50  --extra_neg_conj                        none
% 7.71/1.50  --large_theory_mode                     true
% 7.71/1.50  --prolific_symb_bound                   200
% 7.71/1.50  --lt_threshold                          2000
% 7.71/1.50  --clause_weak_htbl                      true
% 7.71/1.50  --gc_record_bc_elim                     false
% 7.71/1.50  
% 7.71/1.50  ------ Preprocessing Options
% 7.71/1.50  
% 7.71/1.50  --preprocessing_flag                    true
% 7.71/1.50  --time_out_prep_mult                    0.1
% 7.71/1.50  --splitting_mode                        input
% 7.71/1.50  --splitting_grd                         true
% 7.71/1.50  --splitting_cvd                         false
% 7.71/1.50  --splitting_cvd_svl                     false
% 7.71/1.50  --splitting_nvd                         32
% 7.71/1.50  --sub_typing                            true
% 7.71/1.50  --prep_gs_sim                           false
% 7.71/1.50  --prep_unflatten                        true
% 7.71/1.50  --prep_res_sim                          true
% 7.71/1.50  --prep_upred                            true
% 7.71/1.50  --prep_sem_filter                       exhaustive
% 7.71/1.50  --prep_sem_filter_out                   false
% 7.71/1.50  --pred_elim                             false
% 7.71/1.50  --res_sim_input                         true
% 7.71/1.50  --eq_ax_congr_red                       true
% 7.71/1.50  --pure_diseq_elim                       true
% 7.71/1.50  --brand_transform                       false
% 7.71/1.50  --non_eq_to_eq                          false
% 7.71/1.50  --prep_def_merge                        true
% 7.71/1.50  --prep_def_merge_prop_impl              false
% 7.71/1.50  --prep_def_merge_mbd                    true
% 7.71/1.50  --prep_def_merge_tr_red                 false
% 7.71/1.50  --prep_def_merge_tr_cl                  false
% 7.71/1.50  --smt_preprocessing                     true
% 7.71/1.50  --smt_ac_axioms                         fast
% 7.71/1.50  --preprocessed_out                      false
% 7.71/1.50  --preprocessed_stats                    false
% 7.71/1.50  
% 7.71/1.50  ------ Abstraction refinement Options
% 7.71/1.50  
% 7.71/1.50  --abstr_ref                             []
% 7.71/1.50  --abstr_ref_prep                        false
% 7.71/1.50  --abstr_ref_until_sat                   false
% 7.71/1.50  --abstr_ref_sig_restrict                funpre
% 7.71/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.71/1.50  --abstr_ref_under                       []
% 7.71/1.50  
% 7.71/1.50  ------ SAT Options
% 7.71/1.50  
% 7.71/1.50  --sat_mode                              false
% 7.71/1.50  --sat_fm_restart_options                ""
% 7.71/1.50  --sat_gr_def                            false
% 7.71/1.50  --sat_epr_types                         true
% 7.71/1.50  --sat_non_cyclic_types                  false
% 7.71/1.50  --sat_finite_models                     false
% 7.71/1.50  --sat_fm_lemmas                         false
% 7.71/1.50  --sat_fm_prep                           false
% 7.71/1.50  --sat_fm_uc_incr                        true
% 7.71/1.50  --sat_out_model                         small
% 7.71/1.50  --sat_out_clauses                       false
% 7.71/1.50  
% 7.71/1.50  ------ QBF Options
% 7.71/1.50  
% 7.71/1.50  --qbf_mode                              false
% 7.71/1.50  --qbf_elim_univ                         false
% 7.71/1.50  --qbf_dom_inst                          none
% 7.71/1.50  --qbf_dom_pre_inst                      false
% 7.71/1.50  --qbf_sk_in                             false
% 7.71/1.50  --qbf_pred_elim                         true
% 7.71/1.50  --qbf_split                             512
% 7.71/1.50  
% 7.71/1.50  ------ BMC1 Options
% 7.71/1.50  
% 7.71/1.50  --bmc1_incremental                      false
% 7.71/1.50  --bmc1_axioms                           reachable_all
% 7.71/1.50  --bmc1_min_bound                        0
% 7.71/1.50  --bmc1_max_bound                        -1
% 7.71/1.50  --bmc1_max_bound_default                -1
% 7.71/1.50  --bmc1_symbol_reachability              true
% 7.71/1.50  --bmc1_property_lemmas                  false
% 7.71/1.50  --bmc1_k_induction                      false
% 7.71/1.50  --bmc1_non_equiv_states                 false
% 7.71/1.50  --bmc1_deadlock                         false
% 7.71/1.50  --bmc1_ucm                              false
% 7.71/1.50  --bmc1_add_unsat_core                   none
% 7.71/1.50  --bmc1_unsat_core_children              false
% 7.71/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.71/1.50  --bmc1_out_stat                         full
% 7.71/1.50  --bmc1_ground_init                      false
% 7.71/1.50  --bmc1_pre_inst_next_state              false
% 7.71/1.50  --bmc1_pre_inst_state                   false
% 7.71/1.50  --bmc1_pre_inst_reach_state             false
% 7.71/1.50  --bmc1_out_unsat_core                   false
% 7.71/1.50  --bmc1_aig_witness_out                  false
% 7.71/1.50  --bmc1_verbose                          false
% 7.71/1.50  --bmc1_dump_clauses_tptp                false
% 7.71/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.71/1.50  --bmc1_dump_file                        -
% 7.71/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.71/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.71/1.50  --bmc1_ucm_extend_mode                  1
% 7.71/1.50  --bmc1_ucm_init_mode                    2
% 7.71/1.50  --bmc1_ucm_cone_mode                    none
% 7.71/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.71/1.50  --bmc1_ucm_relax_model                  4
% 7.71/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.71/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.71/1.50  --bmc1_ucm_layered_model                none
% 7.71/1.50  --bmc1_ucm_max_lemma_size               10
% 7.71/1.50  
% 7.71/1.50  ------ AIG Options
% 7.71/1.50  
% 7.71/1.50  --aig_mode                              false
% 7.71/1.50  
% 7.71/1.50  ------ Instantiation Options
% 7.71/1.50  
% 7.71/1.50  --instantiation_flag                    true
% 7.71/1.50  --inst_sos_flag                         false
% 7.71/1.50  --inst_sos_phase                        true
% 7.71/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.71/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.71/1.50  --inst_lit_sel_side                     num_symb
% 7.71/1.50  --inst_solver_per_active                1400
% 7.71/1.50  --inst_solver_calls_frac                1.
% 7.71/1.50  --inst_passive_queue_type               priority_queues
% 7.71/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.71/1.50  --inst_passive_queues_freq              [25;2]
% 7.71/1.50  --inst_dismatching                      true
% 7.71/1.50  --inst_eager_unprocessed_to_passive     true
% 7.71/1.50  --inst_prop_sim_given                   true
% 7.71/1.50  --inst_prop_sim_new                     false
% 7.71/1.50  --inst_subs_new                         false
% 7.71/1.50  --inst_eq_res_simp                      false
% 7.71/1.50  --inst_subs_given                       false
% 7.71/1.50  --inst_orphan_elimination               true
% 7.71/1.50  --inst_learning_loop_flag               true
% 7.71/1.50  --inst_learning_start                   3000
% 7.71/1.50  --inst_learning_factor                  2
% 7.71/1.50  --inst_start_prop_sim_after_learn       3
% 7.71/1.50  --inst_sel_renew                        solver
% 7.71/1.50  --inst_lit_activity_flag                true
% 7.71/1.50  --inst_restr_to_given                   false
% 7.71/1.50  --inst_activity_threshold               500
% 7.71/1.50  --inst_out_proof                        true
% 7.71/1.50  
% 7.71/1.50  ------ Resolution Options
% 7.71/1.50  
% 7.71/1.50  --resolution_flag                       true
% 7.71/1.50  --res_lit_sel                           adaptive
% 7.71/1.50  --res_lit_sel_side                      none
% 7.71/1.50  --res_ordering                          kbo
% 7.71/1.50  --res_to_prop_solver                    active
% 7.71/1.50  --res_prop_simpl_new                    false
% 7.71/1.50  --res_prop_simpl_given                  true
% 7.71/1.50  --res_passive_queue_type                priority_queues
% 7.71/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.71/1.50  --res_passive_queues_freq               [15;5]
% 7.71/1.50  --res_forward_subs                      full
% 7.71/1.50  --res_backward_subs                     full
% 7.71/1.50  --res_forward_subs_resolution           true
% 7.71/1.50  --res_backward_subs_resolution          true
% 7.71/1.50  --res_orphan_elimination                true
% 7.71/1.50  --res_time_limit                        2.
% 7.71/1.50  --res_out_proof                         true
% 7.71/1.50  
% 7.71/1.50  ------ Superposition Options
% 7.71/1.50  
% 7.71/1.50  --superposition_flag                    true
% 7.71/1.50  --sup_passive_queue_type                priority_queues
% 7.71/1.50  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.71/1.50  --sup_passive_queues_freq               [1;4]
% 7.71/1.50  --demod_completeness_check              fast
% 7.71/1.50  --demod_use_ground                      true
% 7.71/1.50  --sup_to_prop_solver                    passive
% 7.71/1.50  --sup_prop_simpl_new                    true
% 7.71/1.50  --sup_prop_simpl_given                  true
% 7.71/1.50  --sup_fun_splitting                     false
% 7.71/1.50  --sup_smt_interval                      50000
% 7.71/1.50  
% 7.71/1.50  ------ Superposition Simplification Setup
% 7.71/1.50  
% 7.71/1.50  --sup_indices_passive                   []
% 7.71/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.71/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.71/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.71/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.71/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.71/1.50  --sup_full_bw                           [BwDemod]
% 7.71/1.50  --sup_immed_triv                        [TrivRules]
% 7.71/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.71/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.71/1.50  --sup_immed_bw_main                     []
% 7.71/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.71/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.71/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.71/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.71/1.50  
% 7.71/1.50  ------ Combination Options
% 7.71/1.50  
% 7.71/1.50  --comb_res_mult                         3
% 7.71/1.50  --comb_sup_mult                         2
% 7.71/1.50  --comb_inst_mult                        10
% 7.71/1.50  
% 7.71/1.50  ------ Debug Options
% 7.71/1.50  
% 7.71/1.50  --dbg_backtrace                         false
% 7.71/1.50  --dbg_dump_prop_clauses                 false
% 7.71/1.50  --dbg_dump_prop_clauses_file            -
% 7.71/1.50  --dbg_out_stat                          false
% 7.71/1.50  ------ Parsing...
% 7.71/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.71/1.50  
% 7.71/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 7.71/1.50  
% 7.71/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.71/1.50  
% 7.71/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.71/1.50  ------ Proving...
% 7.71/1.50  ------ Problem Properties 
% 7.71/1.50  
% 7.71/1.50  
% 7.71/1.50  clauses                                 22
% 7.71/1.50  conjectures                             7
% 7.71/1.50  EPR                                     5
% 7.71/1.50  Horn                                    19
% 7.71/1.50  unary                                   7
% 7.71/1.50  binary                                  6
% 7.71/1.50  lits                                    53
% 7.71/1.50  lits eq                                 2
% 7.71/1.50  fd_pure                                 0
% 7.71/1.50  fd_pseudo                               0
% 7.71/1.50  fd_cond                                 0
% 7.71/1.50  fd_pseudo_cond                          0
% 7.71/1.50  AC symbols                              0
% 7.71/1.50  
% 7.71/1.50  ------ Input Options Time Limit: Unbounded
% 7.71/1.50  
% 7.71/1.50  
% 7.71/1.50  ------ 
% 7.71/1.50  Current options:
% 7.71/1.50  ------ 
% 7.71/1.50  
% 7.71/1.50  ------ Input Options
% 7.71/1.50  
% 7.71/1.50  --out_options                           all
% 7.71/1.50  --tptp_safe_out                         true
% 7.71/1.50  --problem_path                          ""
% 7.71/1.50  --include_path                          ""
% 7.71/1.50  --clausifier                            res/vclausify_rel
% 7.71/1.50  --clausifier_options                    --mode clausify
% 7.71/1.50  --stdin                                 false
% 7.71/1.50  --stats_out                             sel
% 7.71/1.50  
% 7.71/1.50  ------ General Options
% 7.71/1.50  
% 7.71/1.50  --fof                                   false
% 7.71/1.50  --time_out_real                         604.99
% 7.71/1.50  --time_out_virtual                      -1.
% 7.71/1.50  --symbol_type_check                     false
% 7.71/1.50  --clausify_out                          false
% 7.71/1.50  --sig_cnt_out                           false
% 7.71/1.50  --trig_cnt_out                          false
% 7.71/1.50  --trig_cnt_out_tolerance                1.
% 7.71/1.50  --trig_cnt_out_sk_spl                   false
% 7.71/1.50  --abstr_cl_out                          false
% 7.71/1.50  
% 7.71/1.50  ------ Global Options
% 7.71/1.50  
% 7.71/1.50  --schedule                              none
% 7.71/1.50  --add_important_lit                     false
% 7.71/1.50  --prop_solver_per_cl                    1000
% 7.71/1.50  --min_unsat_core                        false
% 7.71/1.50  --soft_assumptions                      false
% 7.71/1.50  --soft_lemma_size                       3
% 7.71/1.50  --prop_impl_unit_size                   0
% 7.71/1.50  --prop_impl_unit                        []
% 7.71/1.50  --share_sel_clauses                     true
% 7.71/1.50  --reset_solvers                         false
% 7.71/1.50  --bc_imp_inh                            [conj_cone]
% 7.71/1.50  --conj_cone_tolerance                   3.
% 7.71/1.50  --extra_neg_conj                        none
% 7.71/1.50  --large_theory_mode                     true
% 7.71/1.50  --prolific_symb_bound                   200
% 7.71/1.50  --lt_threshold                          2000
% 7.71/1.50  --clause_weak_htbl                      true
% 7.71/1.50  --gc_record_bc_elim                     false
% 7.71/1.50  
% 7.71/1.50  ------ Preprocessing Options
% 7.71/1.50  
% 7.71/1.50  --preprocessing_flag                    true
% 7.71/1.50  --time_out_prep_mult                    0.1
% 7.71/1.50  --splitting_mode                        input
% 7.71/1.50  --splitting_grd                         true
% 7.71/1.50  --splitting_cvd                         false
% 7.71/1.50  --splitting_cvd_svl                     false
% 7.71/1.50  --splitting_nvd                         32
% 7.71/1.50  --sub_typing                            true
% 7.71/1.50  --prep_gs_sim                           false
% 7.71/1.50  --prep_unflatten                        true
% 7.71/1.50  --prep_res_sim                          true
% 7.71/1.50  --prep_upred                            true
% 7.71/1.50  --prep_sem_filter                       exhaustive
% 7.71/1.50  --prep_sem_filter_out                   false
% 7.71/1.50  --pred_elim                             false
% 7.71/1.50  --res_sim_input                         true
% 7.71/1.50  --eq_ax_congr_red                       true
% 7.71/1.50  --pure_diseq_elim                       true
% 7.71/1.50  --brand_transform                       false
% 7.71/1.50  --non_eq_to_eq                          false
% 7.71/1.50  --prep_def_merge                        true
% 7.71/1.50  --prep_def_merge_prop_impl              false
% 7.71/1.50  --prep_def_merge_mbd                    true
% 7.71/1.50  --prep_def_merge_tr_red                 false
% 7.71/1.50  --prep_def_merge_tr_cl                  false
% 7.71/1.50  --smt_preprocessing                     true
% 7.71/1.50  --smt_ac_axioms                         fast
% 7.71/1.50  --preprocessed_out                      false
% 7.71/1.50  --preprocessed_stats                    false
% 7.71/1.50  
% 7.71/1.50  ------ Abstraction refinement Options
% 7.71/1.50  
% 7.71/1.50  --abstr_ref                             []
% 7.71/1.50  --abstr_ref_prep                        false
% 7.71/1.50  --abstr_ref_until_sat                   false
% 7.71/1.50  --abstr_ref_sig_restrict                funpre
% 7.71/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.71/1.50  --abstr_ref_under                       []
% 7.71/1.50  
% 7.71/1.50  ------ SAT Options
% 7.71/1.50  
% 7.71/1.50  --sat_mode                              false
% 7.71/1.50  --sat_fm_restart_options                ""
% 7.71/1.50  --sat_gr_def                            false
% 7.71/1.50  --sat_epr_types                         true
% 7.71/1.50  --sat_non_cyclic_types                  false
% 7.71/1.50  --sat_finite_models                     false
% 7.71/1.50  --sat_fm_lemmas                         false
% 7.71/1.50  --sat_fm_prep                           false
% 7.71/1.50  --sat_fm_uc_incr                        true
% 7.71/1.50  --sat_out_model                         small
% 7.71/1.50  --sat_out_clauses                       false
% 7.71/1.50  
% 7.71/1.50  ------ QBF Options
% 7.71/1.50  
% 7.71/1.50  --qbf_mode                              false
% 7.71/1.50  --qbf_elim_univ                         false
% 7.71/1.50  --qbf_dom_inst                          none
% 7.71/1.50  --qbf_dom_pre_inst                      false
% 7.71/1.50  --qbf_sk_in                             false
% 7.71/1.50  --qbf_pred_elim                         true
% 7.71/1.50  --qbf_split                             512
% 7.71/1.50  
% 7.71/1.50  ------ BMC1 Options
% 7.71/1.50  
% 7.71/1.50  --bmc1_incremental                      false
% 7.71/1.50  --bmc1_axioms                           reachable_all
% 7.71/1.50  --bmc1_min_bound                        0
% 7.71/1.50  --bmc1_max_bound                        -1
% 7.71/1.50  --bmc1_max_bound_default                -1
% 7.71/1.50  --bmc1_symbol_reachability              true
% 7.71/1.50  --bmc1_property_lemmas                  false
% 7.71/1.50  --bmc1_k_induction                      false
% 7.71/1.50  --bmc1_non_equiv_states                 false
% 7.71/1.50  --bmc1_deadlock                         false
% 7.71/1.50  --bmc1_ucm                              false
% 7.71/1.50  --bmc1_add_unsat_core                   none
% 7.71/1.50  --bmc1_unsat_core_children              false
% 7.71/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.71/1.50  --bmc1_out_stat                         full
% 7.71/1.50  --bmc1_ground_init                      false
% 7.71/1.50  --bmc1_pre_inst_next_state              false
% 7.71/1.50  --bmc1_pre_inst_state                   false
% 7.71/1.50  --bmc1_pre_inst_reach_state             false
% 7.71/1.50  --bmc1_out_unsat_core                   false
% 7.71/1.50  --bmc1_aig_witness_out                  false
% 7.71/1.50  --bmc1_verbose                          false
% 7.71/1.50  --bmc1_dump_clauses_tptp                false
% 7.71/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.71/1.50  --bmc1_dump_file                        -
% 7.71/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.71/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.71/1.50  --bmc1_ucm_extend_mode                  1
% 7.71/1.50  --bmc1_ucm_init_mode                    2
% 7.71/1.50  --bmc1_ucm_cone_mode                    none
% 7.71/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.71/1.50  --bmc1_ucm_relax_model                  4
% 7.71/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.71/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.71/1.50  --bmc1_ucm_layered_model                none
% 7.71/1.50  --bmc1_ucm_max_lemma_size               10
% 7.71/1.50  
% 7.71/1.50  ------ AIG Options
% 7.71/1.50  
% 7.71/1.50  --aig_mode                              false
% 7.71/1.50  
% 7.71/1.50  ------ Instantiation Options
% 7.71/1.50  
% 7.71/1.50  --instantiation_flag                    true
% 7.71/1.50  --inst_sos_flag                         false
% 7.71/1.50  --inst_sos_phase                        true
% 7.71/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.71/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.71/1.50  --inst_lit_sel_side                     num_symb
% 7.71/1.50  --inst_solver_per_active                1400
% 7.71/1.50  --inst_solver_calls_frac                1.
% 7.71/1.50  --inst_passive_queue_type               priority_queues
% 7.71/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.71/1.50  --inst_passive_queues_freq              [25;2]
% 7.71/1.50  --inst_dismatching                      true
% 7.71/1.50  --inst_eager_unprocessed_to_passive     true
% 7.71/1.50  --inst_prop_sim_given                   true
% 7.71/1.50  --inst_prop_sim_new                     false
% 7.71/1.50  --inst_subs_new                         false
% 7.71/1.50  --inst_eq_res_simp                      false
% 7.71/1.50  --inst_subs_given                       false
% 7.71/1.50  --inst_orphan_elimination               true
% 7.71/1.50  --inst_learning_loop_flag               true
% 7.71/1.50  --inst_learning_start                   3000
% 7.71/1.50  --inst_learning_factor                  2
% 7.71/1.50  --inst_start_prop_sim_after_learn       3
% 7.71/1.50  --inst_sel_renew                        solver
% 7.71/1.50  --inst_lit_activity_flag                true
% 7.71/1.50  --inst_restr_to_given                   false
% 7.71/1.50  --inst_activity_threshold               500
% 7.71/1.50  --inst_out_proof                        true
% 7.71/1.50  
% 7.71/1.50  ------ Resolution Options
% 7.71/1.50  
% 7.71/1.50  --resolution_flag                       true
% 7.71/1.50  --res_lit_sel                           adaptive
% 7.71/1.50  --res_lit_sel_side                      none
% 7.71/1.50  --res_ordering                          kbo
% 7.71/1.50  --res_to_prop_solver                    active
% 7.71/1.50  --res_prop_simpl_new                    false
% 7.71/1.50  --res_prop_simpl_given                  true
% 7.71/1.50  --res_passive_queue_type                priority_queues
% 7.71/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.71/1.50  --res_passive_queues_freq               [15;5]
% 7.71/1.50  --res_forward_subs                      full
% 7.71/1.50  --res_backward_subs                     full
% 7.71/1.50  --res_forward_subs_resolution           true
% 7.71/1.50  --res_backward_subs_resolution          true
% 7.71/1.50  --res_orphan_elimination                true
% 7.71/1.50  --res_time_limit                        2.
% 7.71/1.50  --res_out_proof                         true
% 7.71/1.50  
% 7.71/1.50  ------ Superposition Options
% 7.71/1.50  
% 7.71/1.50  --superposition_flag                    true
% 7.71/1.50  --sup_passive_queue_type                priority_queues
% 7.71/1.50  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.71/1.50  --sup_passive_queues_freq               [1;4]
% 7.71/1.50  --demod_completeness_check              fast
% 7.71/1.50  --demod_use_ground                      true
% 7.71/1.50  --sup_to_prop_solver                    passive
% 7.71/1.50  --sup_prop_simpl_new                    true
% 7.71/1.50  --sup_prop_simpl_given                  true
% 7.71/1.50  --sup_fun_splitting                     false
% 7.71/1.50  --sup_smt_interval                      50000
% 7.71/1.50  
% 7.71/1.50  ------ Superposition Simplification Setup
% 7.71/1.50  
% 7.71/1.50  --sup_indices_passive                   []
% 7.71/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.71/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.71/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.71/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.71/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.71/1.50  --sup_full_bw                           [BwDemod]
% 7.71/1.50  --sup_immed_triv                        [TrivRules]
% 7.71/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.71/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.71/1.50  --sup_immed_bw_main                     []
% 7.71/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.71/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.71/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.71/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.71/1.50  
% 7.71/1.50  ------ Combination Options
% 7.71/1.50  
% 7.71/1.50  --comb_res_mult                         3
% 7.71/1.50  --comb_sup_mult                         2
% 7.71/1.50  --comb_inst_mult                        10
% 7.71/1.50  
% 7.71/1.50  ------ Debug Options
% 7.71/1.50  
% 7.71/1.50  --dbg_backtrace                         false
% 7.71/1.50  --dbg_dump_prop_clauses                 false
% 7.71/1.50  --dbg_dump_prop_clauses_file            -
% 7.71/1.50  --dbg_out_stat                          false
% 7.71/1.50  
% 7.71/1.50  
% 7.71/1.50  
% 7.71/1.50  
% 7.71/1.50  ------ Proving...
% 7.71/1.50  
% 7.71/1.50  
% 7.71/1.50  % SZS status Theorem for theBenchmark.p
% 7.71/1.50  
% 7.71/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.71/1.50  
% 7.71/1.50  fof(f10,axiom,(
% 7.71/1.50    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 7.71/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.50  
% 7.71/1.50  fof(f23,plain,(
% 7.71/1.50    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 7.71/1.50    inference(ennf_transformation,[],[f10])).
% 7.71/1.50  
% 7.71/1.50  fof(f24,plain,(
% 7.71/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.71/1.50    inference(flattening,[],[f23])).
% 7.71/1.50  
% 7.71/1.50  fof(f29,plain,(
% 7.71/1.50    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) => (~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) & r2_hidden(sK0(X0,X1,X2),X0)))),
% 7.71/1.50    introduced(choice_axiom,[])).
% 7.71/1.50  
% 7.71/1.50  fof(f30,plain,(
% 7.71/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.71/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f29])).
% 7.71/1.50  
% 7.71/1.50  fof(f50,plain,(
% 7.71/1.50    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(sK0(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.71/1.50    inference(cnf_transformation,[],[f30])).
% 7.71/1.50  
% 7.71/1.50  fof(f60,plain,(
% 7.71/1.50    ( ! [X2,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | r2_hidden(sK0(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.71/1.50    inference(equality_resolution,[],[f50])).
% 7.71/1.50  
% 7.71/1.50  fof(f1,axiom,(
% 7.71/1.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.71/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.50  
% 7.71/1.50  fof(f27,plain,(
% 7.71/1.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.71/1.50    inference(nnf_transformation,[],[f1])).
% 7.71/1.50  
% 7.71/1.50  fof(f36,plain,(
% 7.71/1.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.71/1.50    inference(cnf_transformation,[],[f27])).
% 7.71/1.50  
% 7.71/1.50  fof(f2,axiom,(
% 7.71/1.50    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 7.71/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.50  
% 7.71/1.50  fof(f14,plain,(
% 7.71/1.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 7.71/1.50    inference(ennf_transformation,[],[f2])).
% 7.71/1.50  
% 7.71/1.50  fof(f15,plain,(
% 7.71/1.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 7.71/1.50    inference(flattening,[],[f14])).
% 7.71/1.50  
% 7.71/1.50  fof(f37,plain,(
% 7.71/1.50    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 7.71/1.50    inference(cnf_transformation,[],[f15])).
% 7.71/1.50  
% 7.71/1.50  fof(f11,conjecture,(
% 7.71/1.50    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 7.71/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.50  
% 7.71/1.50  fof(f12,negated_conjecture,(
% 7.71/1.50    ~! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 7.71/1.50    inference(negated_conjecture,[],[f11])).
% 7.71/1.50  
% 7.71/1.50  fof(f25,plain,(
% 7.71/1.50    ? [X0,X1] : (? [X2] : (? [X3] : ((~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 7.71/1.50    inference(ennf_transformation,[],[f12])).
% 7.71/1.50  
% 7.71/1.50  fof(f26,plain,(
% 7.71/1.50    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 7.71/1.50    inference(flattening,[],[f25])).
% 7.71/1.50  
% 7.71/1.50  fof(f33,plain,(
% 7.71/1.50    ( ! [X2,X0,X1] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (~r1_tarski(k2_relset_1(X1,X2,sK4),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,sK4,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK4,X1,X2) & v1_funct_1(sK4))) )),
% 7.71/1.50    introduced(choice_axiom,[])).
% 7.71/1.50  
% 7.71/1.50  fof(f32,plain,(
% 7.71/1.50    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (~r1_tarski(k2_relset_1(X1,sK3,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,sK3,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK3))) & v1_funct_2(X3,X1,sK3) & v1_funct_1(X3)) & ~v1_xboole_0(sK3))) )),
% 7.71/1.50    introduced(choice_axiom,[])).
% 7.71/1.50  
% 7.71/1.50  fof(f31,plain,(
% 7.71/1.50    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(sK2,X2,X3),sK1) & ! [X4] : (r2_hidden(k3_funct_2(sK2,X2,X3,X4),sK1) | ~m1_subset_1(X4,sK2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,X2))) & v1_funct_2(X3,sK2,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK2))),
% 7.71/1.50    introduced(choice_axiom,[])).
% 7.71/1.50  
% 7.71/1.50  fof(f34,plain,(
% 7.71/1.50    ((~r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) & ! [X4] : (r2_hidden(k3_funct_2(sK2,sK3,sK4,X4),sK1) | ~m1_subset_1(X4,sK2)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)) & ~v1_xboole_0(sK3)) & ~v1_xboole_0(sK2)),
% 7.71/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f26,f33,f32,f31])).
% 7.71/1.50  
% 7.71/1.50  fof(f56,plain,(
% 7.71/1.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 7.71/1.50    inference(cnf_transformation,[],[f34])).
% 7.71/1.50  
% 7.71/1.50  fof(f9,axiom,(
% 7.71/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 7.71/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.50  
% 7.71/1.50  fof(f21,plain,(
% 7.71/1.50    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 7.71/1.50    inference(ennf_transformation,[],[f9])).
% 7.71/1.50  
% 7.71/1.50  fof(f22,plain,(
% 7.71/1.50    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 7.71/1.50    inference(flattening,[],[f21])).
% 7.71/1.50  
% 7.71/1.50  fof(f45,plain,(
% 7.71/1.50    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 7.71/1.50    inference(cnf_transformation,[],[f22])).
% 7.71/1.50  
% 7.71/1.50  fof(f52,plain,(
% 7.71/1.50    ~v1_xboole_0(sK2)),
% 7.71/1.50    inference(cnf_transformation,[],[f34])).
% 7.71/1.50  
% 7.71/1.50  fof(f54,plain,(
% 7.71/1.50    v1_funct_1(sK4)),
% 7.71/1.50    inference(cnf_transformation,[],[f34])).
% 7.71/1.50  
% 7.71/1.50  fof(f55,plain,(
% 7.71/1.50    v1_funct_2(sK4,sK2,sK3)),
% 7.71/1.50    inference(cnf_transformation,[],[f34])).
% 7.71/1.50  
% 7.71/1.50  fof(f35,plain,(
% 7.71/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.71/1.50    inference(cnf_transformation,[],[f27])).
% 7.71/1.50  
% 7.71/1.50  fof(f6,axiom,(
% 7.71/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.71/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.50  
% 7.71/1.50  fof(f13,plain,(
% 7.71/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.71/1.50    inference(pure_predicate_removal,[],[f6])).
% 7.71/1.50  
% 7.71/1.50  fof(f18,plain,(
% 7.71/1.50    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.71/1.50    inference(ennf_transformation,[],[f13])).
% 7.71/1.50  
% 7.71/1.50  fof(f42,plain,(
% 7.71/1.50    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.71/1.50    inference(cnf_transformation,[],[f18])).
% 7.71/1.50  
% 7.71/1.50  fof(f4,axiom,(
% 7.71/1.50    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 7.71/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.50  
% 7.71/1.50  fof(f17,plain,(
% 7.71/1.50    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.71/1.50    inference(ennf_transformation,[],[f4])).
% 7.71/1.50  
% 7.71/1.50  fof(f28,plain,(
% 7.71/1.50    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.71/1.50    inference(nnf_transformation,[],[f17])).
% 7.71/1.50  
% 7.71/1.50  fof(f39,plain,(
% 7.71/1.50    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.71/1.50    inference(cnf_transformation,[],[f28])).
% 7.71/1.50  
% 7.71/1.50  fof(f8,axiom,(
% 7.71/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 7.71/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.50  
% 7.71/1.50  fof(f20,plain,(
% 7.71/1.50    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.71/1.50    inference(ennf_transformation,[],[f8])).
% 7.71/1.50  
% 7.71/1.50  fof(f44,plain,(
% 7.71/1.50    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.71/1.50    inference(cnf_transformation,[],[f20])).
% 7.71/1.50  
% 7.71/1.50  fof(f3,axiom,(
% 7.71/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.71/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.50  
% 7.71/1.50  fof(f16,plain,(
% 7.71/1.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.71/1.50    inference(ennf_transformation,[],[f3])).
% 7.71/1.50  
% 7.71/1.50  fof(f38,plain,(
% 7.71/1.50    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.71/1.50    inference(cnf_transformation,[],[f16])).
% 7.71/1.50  
% 7.71/1.50  fof(f5,axiom,(
% 7.71/1.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.71/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.50  
% 7.71/1.50  fof(f41,plain,(
% 7.71/1.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.71/1.50    inference(cnf_transformation,[],[f5])).
% 7.71/1.50  
% 7.71/1.50  fof(f57,plain,(
% 7.71/1.50    ( ! [X4] : (r2_hidden(k3_funct_2(sK2,sK3,sK4,X4),sK1) | ~m1_subset_1(X4,sK2)) )),
% 7.71/1.50    inference(cnf_transformation,[],[f34])).
% 7.71/1.50  
% 7.71/1.50  fof(f51,plain,(
% 7.71/1.50    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(k1_funct_1(X2,sK0(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.71/1.50    inference(cnf_transformation,[],[f30])).
% 7.71/1.50  
% 7.71/1.50  fof(f59,plain,(
% 7.71/1.50    ( ! [X2,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | ~r2_hidden(k1_funct_1(X2,sK0(k1_relat_1(X2),X1,X2)),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.71/1.50    inference(equality_resolution,[],[f51])).
% 7.71/1.50  
% 7.71/1.50  fof(f7,axiom,(
% 7.71/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 7.71/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.50  
% 7.71/1.50  fof(f19,plain,(
% 7.71/1.50    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.71/1.50    inference(ennf_transformation,[],[f7])).
% 7.71/1.50  
% 7.71/1.50  fof(f43,plain,(
% 7.71/1.50    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.71/1.50    inference(cnf_transformation,[],[f19])).
% 7.71/1.50  
% 7.71/1.50  fof(f58,plain,(
% 7.71/1.50    ~r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1)),
% 7.71/1.50    inference(cnf_transformation,[],[f34])).
% 7.71/1.50  
% 7.71/1.50  cnf(c_12,plain,
% 7.71/1.50      ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 7.71/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 7.71/1.50      | ~ v1_funct_1(X0)
% 7.71/1.50      | ~ v1_relat_1(X0) ),
% 7.71/1.50      inference(cnf_transformation,[],[f60]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_965,plain,
% 7.71/1.50      ( r2_hidden(sK0(k1_relat_1(X0),X1,X0),k1_relat_1(X0)) = iProver_top
% 7.71/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 7.71/1.50      | v1_funct_1(X0) != iProver_top
% 7.71/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.71/1.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_0,plain,
% 7.71/1.50      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.71/1.50      inference(cnf_transformation,[],[f36]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_976,plain,
% 7.71/1.50      ( r1_tarski(X0,X1) != iProver_top
% 7.71/1.50      | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 7.71/1.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_2,plain,
% 7.71/1.50      ( ~ r2_hidden(X0,X1)
% 7.71/1.50      | m1_subset_1(X0,X2)
% 7.71/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 7.71/1.50      inference(cnf_transformation,[],[f37]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_974,plain,
% 7.71/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.71/1.50      | m1_subset_1(X0,X2) = iProver_top
% 7.71/1.50      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 7.71/1.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_1760,plain,
% 7.71/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.71/1.50      | r1_tarski(X1,X2) != iProver_top
% 7.71/1.50      | m1_subset_1(X0,X2) = iProver_top ),
% 7.71/1.50      inference(superposition,[status(thm)],[c_976,c_974]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_2819,plain,
% 7.71/1.50      ( r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 7.71/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X2))) = iProver_top
% 7.71/1.50      | m1_subset_1(sK0(k1_relat_1(X0),X2,X0),X1) = iProver_top
% 7.71/1.50      | v1_funct_1(X0) != iProver_top
% 7.71/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.71/1.50      inference(superposition,[status(thm)],[c_965,c_1760]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_19,negated_conjecture,
% 7.71/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 7.71/1.50      inference(cnf_transformation,[],[f56]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_960,plain,
% 7.71/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 7.71/1.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_10,plain,
% 7.71/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.71/1.50      | ~ m1_subset_1(X3,X1)
% 7.71/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.71/1.50      | v1_xboole_0(X1)
% 7.71/1.50      | ~ v1_funct_1(X0)
% 7.71/1.50      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 7.71/1.50      inference(cnf_transformation,[],[f45]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_967,plain,
% 7.71/1.50      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
% 7.71/1.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.71/1.50      | m1_subset_1(X3,X0) != iProver_top
% 7.71/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.71/1.50      | v1_xboole_0(X0) = iProver_top
% 7.71/1.50      | v1_funct_1(X2) != iProver_top ),
% 7.71/1.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_1975,plain,
% 7.71/1.50      ( k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0)
% 7.71/1.50      | v1_funct_2(sK4,sK2,sK3) != iProver_top
% 7.71/1.50      | m1_subset_1(X0,sK2) != iProver_top
% 7.71/1.50      | v1_xboole_0(sK2) = iProver_top
% 7.71/1.50      | v1_funct_1(sK4) != iProver_top ),
% 7.71/1.50      inference(superposition,[status(thm)],[c_960,c_967]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_23,negated_conjecture,
% 7.71/1.50      ( ~ v1_xboole_0(sK2) ),
% 7.71/1.50      inference(cnf_transformation,[],[f52]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_24,plain,
% 7.71/1.50      ( v1_xboole_0(sK2) != iProver_top ),
% 7.71/1.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_21,negated_conjecture,
% 7.71/1.50      ( v1_funct_1(sK4) ),
% 7.71/1.50      inference(cnf_transformation,[],[f54]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_26,plain,
% 7.71/1.50      ( v1_funct_1(sK4) = iProver_top ),
% 7.71/1.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_20,negated_conjecture,
% 7.71/1.50      ( v1_funct_2(sK4,sK2,sK3) ),
% 7.71/1.50      inference(cnf_transformation,[],[f55]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_27,plain,
% 7.71/1.50      ( v1_funct_2(sK4,sK2,sK3) = iProver_top ),
% 7.71/1.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_3908,plain,
% 7.71/1.50      ( k3_funct_2(sK2,sK3,sK4,X0) = k1_funct_1(sK4,X0)
% 7.71/1.50      | m1_subset_1(X0,sK2) != iProver_top ),
% 7.71/1.50      inference(global_propositional_subsumption,
% 7.71/1.50                [status(thm)],
% 7.71/1.50                [c_1975,c_24,c_26,c_27]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_4257,plain,
% 7.71/1.50      ( k3_funct_2(sK2,sK3,sK4,sK0(k1_relat_1(X0),X1,X0)) = k1_funct_1(sK4,sK0(k1_relat_1(X0),X1,X0))
% 7.71/1.50      | r1_tarski(k1_relat_1(X0),sK2) != iProver_top
% 7.71/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 7.71/1.50      | v1_funct_1(X0) != iProver_top
% 7.71/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.71/1.50      inference(superposition,[status(thm)],[c_2819,c_3908]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_1,plain,
% 7.71/1.50      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.71/1.50      inference(cnf_transformation,[],[f35]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_975,plain,
% 7.71/1.50      ( r1_tarski(X0,X1) = iProver_top
% 7.71/1.50      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 7.71/1.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_9481,plain,
% 7.71/1.50      ( k3_funct_2(sK2,sK3,sK4,sK0(k1_relat_1(X0),X1,X0)) = k1_funct_1(sK4,sK0(k1_relat_1(X0),X1,X0))
% 7.71/1.50      | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),X1)) = iProver_top
% 7.71/1.50      | r1_tarski(k1_relat_1(X0),sK2) != iProver_top
% 7.71/1.50      | v1_funct_1(X0) != iProver_top
% 7.71/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.71/1.50      inference(superposition,[status(thm)],[c_4257,c_975]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_7,plain,
% 7.71/1.50      ( v4_relat_1(X0,X1)
% 7.71/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.71/1.50      inference(cnf_transformation,[],[f42]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_970,plain,
% 7.71/1.50      ( v4_relat_1(X0,X1) = iProver_top
% 7.71/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 7.71/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_1456,plain,
% 7.71/1.50      ( v4_relat_1(sK4,sK2) = iProver_top ),
% 7.71/1.50      inference(superposition,[status(thm)],[c_960,c_970]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_5,plain,
% 7.71/1.50      ( ~ v4_relat_1(X0,X1)
% 7.71/1.50      | r1_tarski(k1_relat_1(X0),X1)
% 7.71/1.50      | ~ v1_relat_1(X0) ),
% 7.71/1.50      inference(cnf_transformation,[],[f39]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_972,plain,
% 7.71/1.50      ( v4_relat_1(X0,X1) != iProver_top
% 7.71/1.50      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 7.71/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.71/1.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_9,plain,
% 7.71/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.71/1.50      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.71/1.50      inference(cnf_transformation,[],[f44]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_968,plain,
% 7.71/1.50      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.71/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.71/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_9485,plain,
% 7.71/1.50      ( k3_funct_2(sK2,sK3,sK4,sK0(k1_relat_1(X0),X1,X0)) = k1_funct_1(sK4,sK0(k1_relat_1(X0),X1,X0))
% 7.71/1.50      | k2_relset_1(k1_relat_1(X0),X1,X0) = k2_relat_1(X0)
% 7.71/1.50      | r1_tarski(k1_relat_1(X0),sK2) != iProver_top
% 7.71/1.50      | v1_funct_1(X0) != iProver_top
% 7.71/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.71/1.50      inference(superposition,[status(thm)],[c_4257,c_968]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_10132,plain,
% 7.71/1.50      ( k3_funct_2(sK2,sK3,sK4,sK0(k1_relat_1(X0),X1,X0)) = k1_funct_1(sK4,sK0(k1_relat_1(X0),X1,X0))
% 7.71/1.50      | k2_relset_1(k1_relat_1(X0),X1,X0) = k2_relat_1(X0)
% 7.71/1.50      | v4_relat_1(X0,sK2) != iProver_top
% 7.71/1.50      | v1_funct_1(X0) != iProver_top
% 7.71/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.71/1.50      inference(superposition,[status(thm)],[c_972,c_9485]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_10142,plain,
% 7.71/1.50      ( k3_funct_2(sK2,sK3,sK4,sK0(k1_relat_1(sK4),X0,sK4)) = k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4))
% 7.71/1.50      | k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
% 7.71/1.50      | v1_funct_1(sK4) != iProver_top
% 7.71/1.50      | v1_relat_1(sK4) != iProver_top ),
% 7.71/1.50      inference(superposition,[status(thm)],[c_1456,c_10132]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_3,plain,
% 7.71/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.71/1.50      | ~ v1_relat_1(X1)
% 7.71/1.50      | v1_relat_1(X0) ),
% 7.71/1.50      inference(cnf_transformation,[],[f38]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_156,plain,
% 7.71/1.50      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.71/1.50      inference(prop_impl,[status(thm)],[c_0]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_195,plain,
% 7.71/1.50      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 7.71/1.50      inference(bin_hyper_res,[status(thm)],[c_3,c_156]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_1231,plain,
% 7.71/1.50      ( r1_tarski(sK4,k2_zfmisc_1(sK2,sK3)) ),
% 7.71/1.50      inference(resolution,[status(thm)],[c_1,c_19]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_1277,plain,
% 7.71/1.50      ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK3)) | v1_relat_1(sK4) ),
% 7.71/1.50      inference(resolution,[status(thm)],[c_195,c_1231]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_6,plain,
% 7.71/1.50      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.71/1.50      inference(cnf_transformation,[],[f41]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_1282,plain,
% 7.71/1.50      ( v1_relat_1(sK4) ),
% 7.71/1.50      inference(forward_subsumption_resolution,
% 7.71/1.50                [status(thm)],
% 7.71/1.50                [c_1277,c_6]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_10229,plain,
% 7.71/1.50      ( ~ v1_funct_1(sK4)
% 7.71/1.50      | ~ v1_relat_1(sK4)
% 7.71/1.50      | k3_funct_2(sK2,sK3,sK4,sK0(k1_relat_1(sK4),X0,sK4)) = k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4))
% 7.71/1.50      | k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4) ),
% 7.71/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_10142]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_11357,plain,
% 7.71/1.50      ( k3_funct_2(sK2,sK3,sK4,sK0(k1_relat_1(sK4),X0,sK4)) = k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4))
% 7.71/1.50      | k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4) ),
% 7.71/1.50      inference(global_propositional_subsumption,
% 7.71/1.50                [status(thm)],
% 7.71/1.50                [c_10142,c_21,c_1282,c_10229]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_18,negated_conjecture,
% 7.71/1.50      ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X0),sK1)
% 7.71/1.50      | ~ m1_subset_1(X0,sK2) ),
% 7.71/1.50      inference(cnf_transformation,[],[f57]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_961,plain,
% 7.71/1.50      ( r2_hidden(k3_funct_2(sK2,sK3,sK4,X0),sK1) = iProver_top
% 7.71/1.50      | m1_subset_1(X0,sK2) != iProver_top ),
% 7.71/1.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_11363,plain,
% 7.71/1.50      ( k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
% 7.71/1.50      | r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),sK1) = iProver_top
% 7.71/1.50      | m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),sK2) != iProver_top ),
% 7.71/1.50      inference(superposition,[status(thm)],[c_11357,c_961]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_28,plain,
% 7.71/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 7.71/1.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_1172,plain,
% 7.71/1.50      ( v4_relat_1(sK4,sK2)
% 7.71/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 7.71/1.50      inference(instantiation,[status(thm)],[c_7]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_1173,plain,
% 7.71/1.50      ( v4_relat_1(sK4,sK2) = iProver_top
% 7.71/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
% 7.71/1.50      inference(predicate_to_equality,[status(thm)],[c_1172]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_1206,plain,
% 7.71/1.50      ( r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
% 7.71/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
% 7.71/1.50      | ~ v1_funct_1(sK4)
% 7.71/1.50      | ~ v1_relat_1(sK4) ),
% 7.71/1.50      inference(instantiation,[status(thm)],[c_12]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_1207,plain,
% 7.71/1.50      ( r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) = iProver_top
% 7.71/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) = iProver_top
% 7.71/1.50      | v1_funct_1(sK4) != iProver_top
% 7.71/1.50      | v1_relat_1(sK4) != iProver_top ),
% 7.71/1.50      inference(predicate_to_equality,[status(thm)],[c_1206]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_1262,plain,
% 7.71/1.50      ( ~ v4_relat_1(sK4,sK2)
% 7.71/1.50      | r1_tarski(k1_relat_1(sK4),sK2)
% 7.71/1.50      | ~ v1_relat_1(sK4) ),
% 7.71/1.50      inference(instantiation,[status(thm)],[c_5]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_1263,plain,
% 7.71/1.50      ( v4_relat_1(sK4,sK2) != iProver_top
% 7.71/1.50      | r1_tarski(k1_relat_1(sK4),sK2) = iProver_top
% 7.71/1.50      | v1_relat_1(sK4) != iProver_top ),
% 7.71/1.50      inference(predicate_to_equality,[status(thm)],[c_1262]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_1283,plain,
% 7.71/1.50      ( v1_relat_1(sK4) = iProver_top ),
% 7.71/1.50      inference(predicate_to_equality,[status(thm)],[c_1282]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_1377,plain,
% 7.71/1.50      ( ~ r1_tarski(k1_relat_1(sK4),sK2)
% 7.71/1.50      | m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(sK2)) ),
% 7.71/1.50      inference(instantiation,[status(thm)],[c_0]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_1378,plain,
% 7.71/1.50      ( r1_tarski(k1_relat_1(sK4),sK2) != iProver_top
% 7.71/1.50      | m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(sK2)) = iProver_top ),
% 7.71/1.50      inference(predicate_to_equality,[status(thm)],[c_1377]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_1491,plain,
% 7.71/1.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
% 7.71/1.50      | k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4) ),
% 7.71/1.50      inference(instantiation,[status(thm)],[c_9]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_1502,plain,
% 7.71/1.50      ( k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
% 7.71/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) != iProver_top ),
% 7.71/1.50      inference(predicate_to_equality,[status(thm)],[c_1491]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_1302,plain,
% 7.71/1.50      ( ~ r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
% 7.71/1.50      | m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),X1)
% 7.71/1.50      | ~ m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(X1)) ),
% 7.71/1.50      inference(instantiation,[status(thm)],[c_2]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_2097,plain,
% 7.71/1.50      ( ~ r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4))
% 7.71/1.50      | m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),sK2)
% 7.71/1.50      | ~ m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(sK2)) ),
% 7.71/1.50      inference(instantiation,[status(thm)],[c_1302]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_2099,plain,
% 7.71/1.50      ( r2_hidden(sK0(k1_relat_1(sK4),X0,sK4),k1_relat_1(sK4)) != iProver_top
% 7.71/1.50      | m1_subset_1(sK0(k1_relat_1(sK4),X0,sK4),sK2) = iProver_top
% 7.71/1.50      | m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(sK2)) != iProver_top ),
% 7.71/1.50      inference(predicate_to_equality,[status(thm)],[c_2097]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_11469,plain,
% 7.71/1.50      ( r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),sK1) = iProver_top
% 7.71/1.50      | k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4) ),
% 7.71/1.50      inference(global_propositional_subsumption,
% 7.71/1.50                [status(thm)],
% 7.71/1.50                [c_11363,c_26,c_28,c_1173,c_1207,c_1263,c_1283,c_1378,
% 7.71/1.50                 c_1502,c_2099]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_11470,plain,
% 7.71/1.50      ( k2_relset_1(k1_relat_1(sK4),X0,sK4) = k2_relat_1(sK4)
% 7.71/1.50      | r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),X0,sK4)),sK1) = iProver_top ),
% 7.71/1.50      inference(renaming,[status(thm)],[c_11469]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_11,plain,
% 7.71/1.50      ( ~ r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1)
% 7.71/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 7.71/1.50      | ~ v1_funct_1(X0)
% 7.71/1.50      | ~ v1_relat_1(X0) ),
% 7.71/1.50      inference(cnf_transformation,[],[f59]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_966,plain,
% 7.71/1.50      ( r2_hidden(k1_funct_1(X0,sK0(k1_relat_1(X0),X1,X0)),X1) != iProver_top
% 7.71/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 7.71/1.50      | v1_funct_1(X0) != iProver_top
% 7.71/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.71/1.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_11478,plain,
% 7.71/1.50      ( k2_relset_1(k1_relat_1(sK4),sK1,sK4) = k2_relat_1(sK4)
% 7.71/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top
% 7.71/1.50      | v1_funct_1(sK4) != iProver_top
% 7.71/1.50      | v1_relat_1(sK4) != iProver_top ),
% 7.71/1.50      inference(superposition,[status(thm)],[c_11470,c_966]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_12123,plain,
% 7.71/1.50      ( k2_relset_1(k1_relat_1(sK4),sK1,sK4) = k2_relat_1(sK4)
% 7.71/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top ),
% 7.71/1.50      inference(global_propositional_subsumption,
% 7.71/1.50                [status(thm)],
% 7.71/1.50                [c_11478,c_26,c_1283]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_12129,plain,
% 7.71/1.50      ( k2_relset_1(k1_relat_1(sK4),sK1,sK4) = k2_relat_1(sK4) ),
% 7.71/1.50      inference(forward_subsumption_resolution,
% 7.71/1.50                [status(thm)],
% 7.71/1.50                [c_12123,c_968]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_8,plain,
% 7.71/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.71/1.50      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 7.71/1.50      inference(cnf_transformation,[],[f43]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_969,plain,
% 7.71/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.71/1.50      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 7.71/1.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_12131,plain,
% 7.71/1.50      ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK1)) = iProver_top
% 7.71/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) != iProver_top ),
% 7.71/1.50      inference(superposition,[status(thm)],[c_12129,c_969]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_12155,plain,
% 7.71/1.50      ( r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),sK1)) != iProver_top
% 7.71/1.50      | m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK1)) = iProver_top ),
% 7.71/1.50      inference(superposition,[status(thm)],[c_976,c_12131]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_1548,plain,
% 7.71/1.50      ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
% 7.71/1.50      inference(superposition,[status(thm)],[c_960,c_968]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_17,negated_conjecture,
% 7.71/1.50      ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) ),
% 7.71/1.50      inference(cnf_transformation,[],[f58]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_962,plain,
% 7.71/1.50      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),sK1) != iProver_top ),
% 7.71/1.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_2205,plain,
% 7.71/1.50      ( r1_tarski(k2_relat_1(sK4),sK1) != iProver_top ),
% 7.71/1.50      inference(demodulation,[status(thm)],[c_1548,c_962]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_1561,plain,
% 7.71/1.50      ( r1_tarski(k2_relset_1(X0,X1,X2),X1) = iProver_top
% 7.71/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.71/1.50      inference(superposition,[status(thm)],[c_969,c_975]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_2437,plain,
% 7.71/1.50      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 7.71/1.50      | r1_tarski(k2_relset_1(X1,X2,X0),X2) = iProver_top ),
% 7.71/1.50      inference(superposition,[status(thm)],[c_976,c_1561]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_12130,plain,
% 7.71/1.50      ( r1_tarski(k2_relat_1(sK4),sK1) = iProver_top
% 7.71/1.50      | r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),sK1)) != iProver_top ),
% 7.71/1.50      inference(superposition,[status(thm)],[c_12129,c_2437]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_12270,plain,
% 7.71/1.50      ( r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),sK1)) != iProver_top ),
% 7.71/1.50      inference(global_propositional_subsumption,
% 7.71/1.50                [status(thm)],
% 7.71/1.50                [c_12155,c_2205,c_12130]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_12275,plain,
% 7.71/1.50      ( k3_funct_2(sK2,sK3,sK4,sK0(k1_relat_1(sK4),sK1,sK4)) = k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4))
% 7.71/1.50      | r1_tarski(k1_relat_1(sK4),sK2) != iProver_top
% 7.71/1.50      | v1_funct_1(sK4) != iProver_top
% 7.71/1.50      | v1_relat_1(sK4) != iProver_top ),
% 7.71/1.50      inference(superposition,[status(thm)],[c_9481,c_12270]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_14569,plain,
% 7.71/1.50      ( k3_funct_2(sK2,sK3,sK4,sK0(k1_relat_1(sK4),sK1,sK4)) = k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)) ),
% 7.71/1.50      inference(global_propositional_subsumption,
% 7.71/1.50                [status(thm)],
% 7.71/1.50                [c_12275,c_26,c_28,c_1173,c_1263,c_1283]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_14573,plain,
% 7.71/1.50      ( r2_hidden(k1_funct_1(sK4,sK0(k1_relat_1(sK4),sK1,sK4)),sK1) = iProver_top
% 7.71/1.50      | m1_subset_1(sK0(k1_relat_1(sK4),sK1,sK4),sK2) != iProver_top ),
% 7.71/1.50      inference(superposition,[status(thm)],[c_14569,c_961]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_14665,plain,
% 7.71/1.50      ( m1_subset_1(sK0(k1_relat_1(sK4),sK1,sK4),sK2) != iProver_top
% 7.71/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top
% 7.71/1.50      | v1_funct_1(sK4) != iProver_top
% 7.71/1.50      | v1_relat_1(sK4) != iProver_top ),
% 7.71/1.50      inference(superposition,[status(thm)],[c_14573,c_966]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_15076,plain,
% 7.71/1.50      ( m1_subset_1(sK0(k1_relat_1(sK4),sK1,sK4),sK2) != iProver_top
% 7.71/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top ),
% 7.71/1.50      inference(global_propositional_subsumption,
% 7.71/1.50                [status(thm)],
% 7.71/1.50                [c_14665,c_26,c_1283]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_15083,plain,
% 7.71/1.50      ( r1_tarski(k1_relat_1(sK4),sK2) != iProver_top
% 7.71/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top
% 7.71/1.50      | v1_funct_1(sK4) != iProver_top
% 7.71/1.50      | v1_relat_1(sK4) != iProver_top ),
% 7.71/1.50      inference(superposition,[status(thm)],[c_2819,c_15076]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_15861,plain,
% 7.71/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK1))) = iProver_top ),
% 7.71/1.50      inference(global_propositional_subsumption,
% 7.71/1.50                [status(thm)],
% 7.71/1.50                [c_15083,c_26,c_28,c_1173,c_1263,c_1283]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(c_15866,plain,
% 7.71/1.50      ( r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),sK1)) = iProver_top ),
% 7.71/1.50      inference(superposition,[status(thm)],[c_15861,c_975]) ).
% 7.71/1.50  
% 7.71/1.50  cnf(contradiction,plain,
% 7.71/1.50      ( $false ),
% 7.71/1.50      inference(minisat,[status(thm)],[c_15866,c_12130,c_2205]) ).
% 7.71/1.50  
% 7.71/1.50  
% 7.71/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.71/1.50  
% 7.71/1.50  ------                               Statistics
% 7.71/1.50  
% 7.71/1.50  ------ Selected
% 7.71/1.50  
% 7.71/1.50  total_time:                             0.508
% 7.71/1.50  
%------------------------------------------------------------------------------
