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
% DateTime   : Thu Dec  3 12:06:05 EST 2020

% Result     : Theorem 4.05s
% Output     : CNFRefutation 4.05s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 318 expanded)
%              Number of clauses        :   62 (  86 expanded)
%              Number of leaves         :   20 (  70 expanded)
%              Depth                    :   20
%              Number of atoms          :  501 (1312 expanded)
%              Number of equality atoms :  234 ( 563 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f27,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f26])).

fof(f45,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( k1_funct_1(sK8,sK7) != sK6
      & r2_hidden(sK7,sK5)
      & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6))))
      & v1_funct_2(sK8,sK5,k1_tarski(sK6))
      & v1_funct_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( k1_funct_1(sK8,sK7) != sK6
    & r2_hidden(sK7,sK5)
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6))))
    & v1_funct_2(sK8,sK5,k1_tarski(sK6))
    & v1_funct_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f27,f45])).

fof(f80,plain,(
    r2_hidden(sK7,sK5) ),
    inference(cnf_transformation,[],[f46])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f79,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6)))) ),
    inference(cnf_transformation,[],[f46])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f82,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f57,f58])).

fof(f89,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_enumset1(sK6,sK6,sK6)))) ),
    inference(definition_unfolding,[],[f79,f82])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

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

fof(f38,plain,(
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

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f42,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X5)) = X5
        & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1)) = X2
        & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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
              ( k1_funct_1(X0,X3) != sK2(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK2(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK2(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK2(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK3(X0,X1)) = sK2(X0,X1)
                  & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK2(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK4(X0,X5)) = X5
                    & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f39,f42,f41,f40])).

fof(f63,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f96,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f97,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f96])).

fof(f77,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f46])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f32])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK1(X0,X1,X2) != X1
            & sK1(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( sK1(X0,X1,X2) = X1
          | sK1(X0,X1,X2) = X0
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK1(X0,X1,X2) != X1
              & sK1(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( sK1(X0,X1,X2) = X1
            | sK1(X0,X1,X2) = X0
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f88,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f51,f58])).

fof(f95,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k1_enumset1(X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f88])).

fof(f78,plain,(
    v1_funct_2(sK8,sK5,k1_tarski(sK6)) ),
    inference(cnf_transformation,[],[f46])).

fof(f90,plain,(
    v1_funct_2(sK8,sK5,k1_enumset1(sK6,sK6,sK6)) ),
    inference(definition_unfolding,[],[f78,f82])).

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
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f87,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f52,f58])).

fof(f93,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k1_enumset1(X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f87])).

fof(f94,plain,(
    ! [X4,X1] : r2_hidden(X4,k1_enumset1(X4,X4,X1)) ),
    inference(equality_resolution,[],[f93])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f81,plain,(
    k1_funct_1(sK8,sK7) != sK6 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_29,negated_conjecture,
    ( r2_hidden(sK7,sK5) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1766,plain,
    ( r2_hidden(sK7,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_11,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_355,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X3),X4)
    | ~ v1_relat_1(X3)
    | X0 != X3
    | X2 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_20])).

cnf(c_356,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_355])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_360,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_356,c_19])).

cnf(c_361,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_360])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_enumset1(sK6,sK6,sK6)))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_488,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK5,k1_enumset1(sK6,sK6,sK6))) != k1_zfmisc_1(k2_zfmisc_1(X2,X1))
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_361,c_30])).

cnf(c_489,plain,
    ( r1_tarski(k2_relat_1(sK8),X0)
    | k1_zfmisc_1(k2_zfmisc_1(sK5,k1_enumset1(sK6,sK6,sK6))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0)) ),
    inference(unflattening,[status(thm)],[c_488])).

cnf(c_1765,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK5,k1_enumset1(sK6,sK6,sK6))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | r1_tarski(k2_relat_1(sK8),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_489])).

cnf(c_2109,plain,
    ( r1_tarski(k2_relat_1(sK8),k1_enumset1(sK6,sK6,sK6)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1765])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_826,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_32])).

cnf(c_827,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK8))
    | r2_hidden(k1_funct_1(sK8,X0),k2_relat_1(sK8))
    | ~ v1_relat_1(sK8) ),
    inference(unflattening,[status(thm)],[c_826])).

cnf(c_1759,plain,
    ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(k1_funct_1(sK8,X0),k2_relat_1(sK8)) = iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_827])).

cnf(c_828,plain,
    ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(k1_funct_1(sK8,X0),k2_relat_1(sK8)) = iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_827])).

cnf(c_545,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(sK5,k1_enumset1(sK6,sK6,sK6))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_30])).

cnf(c_546,plain,
    ( v1_relat_1(sK8)
    | k1_zfmisc_1(k2_zfmisc_1(sK5,k1_enumset1(sK6,sK6,sK6))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_545])).

cnf(c_1838,plain,
    ( v1_relat_1(sK8)
    | k1_zfmisc_1(k2_zfmisc_1(sK5,k1_enumset1(sK6,sK6,sK6))) != k1_zfmisc_1(k2_zfmisc_1(sK5,k1_enumset1(sK6,sK6,sK6))) ),
    inference(instantiation,[status(thm)],[c_546])).

cnf(c_1839,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK5,k1_enumset1(sK6,sK6,sK6))) != k1_zfmisc_1(k2_zfmisc_1(sK5,k1_enumset1(sK6,sK6,sK6)))
    | v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1838])).

cnf(c_1413,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1905,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK5,k1_enumset1(sK6,sK6,sK6))) = k1_zfmisc_1(k2_zfmisc_1(sK5,k1_enumset1(sK6,sK6,sK6))) ),
    inference(instantiation,[status(thm)],[c_1413])).

cnf(c_2501,plain,
    ( r2_hidden(k1_funct_1(sK8,X0),k2_relat_1(sK8)) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1759,c_828,c_1839,c_1905])).

cnf(c_2502,plain,
    ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(k1_funct_1(sK8,X0),k2_relat_1(sK8)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2501])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1775,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3098,plain,
    ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(k1_funct_1(sK8,X0),X1) = iProver_top
    | r1_tarski(k2_relat_1(sK8),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2502,c_1775])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1768,plain,
    ( X0 = X1
    | X0 = X2
    | r2_hidden(X0,k1_enumset1(X1,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3557,plain,
    ( k1_funct_1(sK8,X0) = X1
    | k1_funct_1(sK8,X0) = X2
    | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | r1_tarski(k2_relat_1(sK8),k1_enumset1(X1,X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3098,c_1768])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK8,sK5,k1_enumset1(sK6,sK6,sK6)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_500,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(sK5,k1_enumset1(sK6,sK6,sK6))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK8 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_30])).

cnf(c_501,plain,
    ( ~ v1_funct_2(sK8,X0,X1)
    | k1_relset_1(X0,X1,sK8) = X0
    | k1_zfmisc_1(k2_zfmisc_1(sK5,k1_enumset1(sK6,sK6,sK6))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_500])).

cnf(c_1012,plain,
    ( k1_relset_1(X0,X1,sK8) = X0
    | k1_enumset1(sK6,sK6,sK6) != X1
    | k1_zfmisc_1(k2_zfmisc_1(sK5,k1_enumset1(sK6,sK6,sK6))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK5 != X0
    | sK8 != sK8
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_501])).

cnf(c_1013,plain,
    ( k1_relset_1(sK5,k1_enumset1(sK6,sK6,sK6),sK8) = sK5
    | k1_zfmisc_1(k2_zfmisc_1(sK5,k1_enumset1(sK6,sK6,sK6))) != k1_zfmisc_1(k2_zfmisc_1(sK5,k1_enumset1(sK6,sK6,sK6)))
    | k1_xboole_0 = k1_enumset1(sK6,sK6,sK6) ),
    inference(unflattening,[status(thm)],[c_1012])).

cnf(c_1086,plain,
    ( k1_relset_1(sK5,k1_enumset1(sK6,sK6,sK6),sK8) = sK5
    | k1_xboole_0 = k1_enumset1(sK6,sK6,sK6) ),
    inference(equality_resolution_simp,[status(thm)],[c_1013])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_536,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(sK5,k1_enumset1(sK6,sK6,sK6))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_30])).

cnf(c_537,plain,
    ( k1_relset_1(X0,X1,sK8) = k1_relat_1(sK8)
    | k1_zfmisc_1(k2_zfmisc_1(sK5,k1_enumset1(sK6,sK6,sK6))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_536])).

cnf(c_1908,plain,
    ( k1_relset_1(sK5,k1_enumset1(sK6,sK6,sK6),sK8) = k1_relat_1(sK8) ),
    inference(equality_resolution,[status(thm)],[c_537])).

cnf(c_2144,plain,
    ( k1_enumset1(sK6,sK6,sK6) = k1_xboole_0
    | k1_relat_1(sK8) = sK5 ),
    inference(demodulation,[status(thm)],[c_1086,c_1908])).

cnf(c_8,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1769,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2222,plain,
    ( k1_relat_1(sK8) = sK5
    | r2_hidden(sK6,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2144,c_1769])).

cnf(c_3080,plain,
    ( k1_relat_1(sK8) = sK5
    | sK6 = X0
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2144,c_1768])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_451,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_18])).

cnf(c_452,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_451])).

cnf(c_453,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_452])).

cnf(c_4812,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3080,c_453])).

cnf(c_4820,plain,
    ( k1_relat_1(sK8) = sK5 ),
    inference(superposition,[status(thm)],[c_2222,c_4812])).

cnf(c_14201,plain,
    ( k1_funct_1(sK8,X0) = X1
    | k1_funct_1(sK8,X0) = X2
    | r2_hidden(X0,sK5) != iProver_top
    | r1_tarski(k2_relat_1(sK8),k1_enumset1(X1,X1,X2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3557,c_4820])).

cnf(c_14207,plain,
    ( k1_funct_1(sK8,X0) = sK6
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2109,c_14201])).

cnf(c_14398,plain,
    ( k1_funct_1(sK8,sK7) = sK6 ),
    inference(superposition,[status(thm)],[c_1766,c_14207])).

cnf(c_28,negated_conjecture,
    ( k1_funct_1(sK8,sK7) != sK6 ),
    inference(cnf_transformation,[],[f81])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14398,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:42:17 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 4.05/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.05/0.98  
% 4.05/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.05/0.98  
% 4.05/0.98  ------  iProver source info
% 4.05/0.98  
% 4.05/0.98  git: date: 2020-06-30 10:37:57 +0100
% 4.05/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.05/0.98  git: non_committed_changes: false
% 4.05/0.98  git: last_make_outside_of_git: false
% 4.05/0.98  
% 4.05/0.98  ------ 
% 4.05/0.98  
% 4.05/0.98  ------ Input Options
% 4.05/0.98  
% 4.05/0.98  --out_options                           all
% 4.05/0.98  --tptp_safe_out                         true
% 4.05/0.98  --problem_path                          ""
% 4.05/0.98  --include_path                          ""
% 4.05/0.98  --clausifier                            res/vclausify_rel
% 4.05/0.98  --clausifier_options                    ""
% 4.05/0.98  --stdin                                 false
% 4.05/0.98  --stats_out                             all
% 4.05/0.98  
% 4.05/0.98  ------ General Options
% 4.05/0.98  
% 4.05/0.98  --fof                                   false
% 4.05/0.98  --time_out_real                         305.
% 4.05/0.98  --time_out_virtual                      -1.
% 4.05/0.98  --symbol_type_check                     false
% 4.05/0.98  --clausify_out                          false
% 4.05/0.98  --sig_cnt_out                           false
% 4.05/0.98  --trig_cnt_out                          false
% 4.05/0.98  --trig_cnt_out_tolerance                1.
% 4.05/0.98  --trig_cnt_out_sk_spl                   false
% 4.05/0.98  --abstr_cl_out                          false
% 4.05/0.98  
% 4.05/0.98  ------ Global Options
% 4.05/0.98  
% 4.05/0.98  --schedule                              default
% 4.05/0.98  --add_important_lit                     false
% 4.05/0.98  --prop_solver_per_cl                    1000
% 4.05/0.98  --min_unsat_core                        false
% 4.05/0.98  --soft_assumptions                      false
% 4.05/0.98  --soft_lemma_size                       3
% 4.05/0.98  --prop_impl_unit_size                   0
% 4.05/0.98  --prop_impl_unit                        []
% 4.05/0.98  --share_sel_clauses                     true
% 4.05/0.98  --reset_solvers                         false
% 4.05/0.98  --bc_imp_inh                            [conj_cone]
% 4.05/0.98  --conj_cone_tolerance                   3.
% 4.05/0.98  --extra_neg_conj                        none
% 4.05/0.98  --large_theory_mode                     true
% 4.05/0.98  --prolific_symb_bound                   200
% 4.05/0.98  --lt_threshold                          2000
% 4.05/0.98  --clause_weak_htbl                      true
% 4.05/0.98  --gc_record_bc_elim                     false
% 4.05/0.98  
% 4.05/0.98  ------ Preprocessing Options
% 4.05/0.98  
% 4.05/0.98  --preprocessing_flag                    true
% 4.05/0.98  --time_out_prep_mult                    0.1
% 4.05/0.98  --splitting_mode                        input
% 4.05/0.98  --splitting_grd                         true
% 4.05/0.98  --splitting_cvd                         false
% 4.05/0.98  --splitting_cvd_svl                     false
% 4.05/0.98  --splitting_nvd                         32
% 4.05/0.98  --sub_typing                            true
% 4.05/0.98  --prep_gs_sim                           true
% 4.05/0.98  --prep_unflatten                        true
% 4.05/0.98  --prep_res_sim                          true
% 4.05/0.98  --prep_upred                            true
% 4.05/0.98  --prep_sem_filter                       exhaustive
% 4.05/0.98  --prep_sem_filter_out                   false
% 4.05/0.98  --pred_elim                             true
% 4.05/0.98  --res_sim_input                         true
% 4.05/0.98  --eq_ax_congr_red                       true
% 4.05/0.98  --pure_diseq_elim                       true
% 4.05/0.98  --brand_transform                       false
% 4.05/0.98  --non_eq_to_eq                          false
% 4.05/0.98  --prep_def_merge                        true
% 4.05/0.98  --prep_def_merge_prop_impl              false
% 4.05/0.98  --prep_def_merge_mbd                    true
% 4.05/0.98  --prep_def_merge_tr_red                 false
% 4.05/0.98  --prep_def_merge_tr_cl                  false
% 4.05/0.98  --smt_preprocessing                     true
% 4.05/0.98  --smt_ac_axioms                         fast
% 4.05/0.98  --preprocessed_out                      false
% 4.05/0.98  --preprocessed_stats                    false
% 4.05/0.98  
% 4.05/0.98  ------ Abstraction refinement Options
% 4.05/0.98  
% 4.05/0.98  --abstr_ref                             []
% 4.05/0.98  --abstr_ref_prep                        false
% 4.05/0.98  --abstr_ref_until_sat                   false
% 4.05/0.98  --abstr_ref_sig_restrict                funpre
% 4.05/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 4.05/0.98  --abstr_ref_under                       []
% 4.05/0.98  
% 4.05/0.98  ------ SAT Options
% 4.05/0.98  
% 4.05/0.98  --sat_mode                              false
% 4.05/0.98  --sat_fm_restart_options                ""
% 4.05/0.98  --sat_gr_def                            false
% 4.05/0.98  --sat_epr_types                         true
% 4.05/0.98  --sat_non_cyclic_types                  false
% 4.05/0.98  --sat_finite_models                     false
% 4.05/0.98  --sat_fm_lemmas                         false
% 4.05/0.98  --sat_fm_prep                           false
% 4.05/0.98  --sat_fm_uc_incr                        true
% 4.05/0.98  --sat_out_model                         small
% 4.05/0.98  --sat_out_clauses                       false
% 4.05/0.98  
% 4.05/0.98  ------ QBF Options
% 4.05/0.98  
% 4.05/0.98  --qbf_mode                              false
% 4.05/0.98  --qbf_elim_univ                         false
% 4.05/0.98  --qbf_dom_inst                          none
% 4.05/0.98  --qbf_dom_pre_inst                      false
% 4.05/0.98  --qbf_sk_in                             false
% 4.05/0.98  --qbf_pred_elim                         true
% 4.05/0.98  --qbf_split                             512
% 4.05/0.98  
% 4.05/0.98  ------ BMC1 Options
% 4.05/0.98  
% 4.05/0.98  --bmc1_incremental                      false
% 4.05/0.98  --bmc1_axioms                           reachable_all
% 4.05/0.98  --bmc1_min_bound                        0
% 4.05/0.98  --bmc1_max_bound                        -1
% 4.05/0.98  --bmc1_max_bound_default                -1
% 4.05/0.98  --bmc1_symbol_reachability              true
% 4.05/0.98  --bmc1_property_lemmas                  false
% 4.05/0.98  --bmc1_k_induction                      false
% 4.05/0.98  --bmc1_non_equiv_states                 false
% 4.05/0.98  --bmc1_deadlock                         false
% 4.05/0.98  --bmc1_ucm                              false
% 4.05/0.98  --bmc1_add_unsat_core                   none
% 4.05/0.98  --bmc1_unsat_core_children              false
% 4.05/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 4.05/0.98  --bmc1_out_stat                         full
% 4.05/0.98  --bmc1_ground_init                      false
% 4.05/0.98  --bmc1_pre_inst_next_state              false
% 4.05/0.98  --bmc1_pre_inst_state                   false
% 4.05/0.98  --bmc1_pre_inst_reach_state             false
% 4.05/0.98  --bmc1_out_unsat_core                   false
% 4.05/0.98  --bmc1_aig_witness_out                  false
% 4.05/0.98  --bmc1_verbose                          false
% 4.05/0.98  --bmc1_dump_clauses_tptp                false
% 4.05/0.98  --bmc1_dump_unsat_core_tptp             false
% 4.05/0.98  --bmc1_dump_file                        -
% 4.05/0.98  --bmc1_ucm_expand_uc_limit              128
% 4.05/0.98  --bmc1_ucm_n_expand_iterations          6
% 4.05/0.98  --bmc1_ucm_extend_mode                  1
% 4.05/0.98  --bmc1_ucm_init_mode                    2
% 4.05/0.98  --bmc1_ucm_cone_mode                    none
% 4.05/0.98  --bmc1_ucm_reduced_relation_type        0
% 4.05/0.98  --bmc1_ucm_relax_model                  4
% 4.05/0.98  --bmc1_ucm_full_tr_after_sat            true
% 4.05/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 4.05/0.98  --bmc1_ucm_layered_model                none
% 4.05/0.98  --bmc1_ucm_max_lemma_size               10
% 4.05/0.98  
% 4.05/0.98  ------ AIG Options
% 4.05/0.98  
% 4.05/0.98  --aig_mode                              false
% 4.05/0.98  
% 4.05/0.98  ------ Instantiation Options
% 4.05/0.98  
% 4.05/0.98  --instantiation_flag                    true
% 4.05/0.98  --inst_sos_flag                         true
% 4.05/0.98  --inst_sos_phase                        true
% 4.05/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.05/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.05/0.98  --inst_lit_sel_side                     num_symb
% 4.05/0.98  --inst_solver_per_active                1400
% 4.05/0.98  --inst_solver_calls_frac                1.
% 4.05/0.98  --inst_passive_queue_type               priority_queues
% 4.05/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.05/0.98  --inst_passive_queues_freq              [25;2]
% 4.05/0.98  --inst_dismatching                      true
% 4.05/0.98  --inst_eager_unprocessed_to_passive     true
% 4.05/0.98  --inst_prop_sim_given                   true
% 4.05/0.98  --inst_prop_sim_new                     false
% 4.05/0.98  --inst_subs_new                         false
% 4.05/0.98  --inst_eq_res_simp                      false
% 4.05/0.98  --inst_subs_given                       false
% 4.05/0.98  --inst_orphan_elimination               true
% 4.05/0.98  --inst_learning_loop_flag               true
% 4.05/0.98  --inst_learning_start                   3000
% 4.05/0.98  --inst_learning_factor                  2
% 4.05/0.98  --inst_start_prop_sim_after_learn       3
% 4.05/0.98  --inst_sel_renew                        solver
% 4.05/0.98  --inst_lit_activity_flag                true
% 4.05/0.98  --inst_restr_to_given                   false
% 4.05/0.98  --inst_activity_threshold               500
% 4.05/0.98  --inst_out_proof                        true
% 4.05/0.98  
% 4.05/0.98  ------ Resolution Options
% 4.05/0.98  
% 4.05/0.98  --resolution_flag                       true
% 4.05/0.98  --res_lit_sel                           adaptive
% 4.05/0.98  --res_lit_sel_side                      none
% 4.05/0.98  --res_ordering                          kbo
% 4.05/0.98  --res_to_prop_solver                    active
% 4.05/0.98  --res_prop_simpl_new                    false
% 4.05/0.98  --res_prop_simpl_given                  true
% 4.05/0.98  --res_passive_queue_type                priority_queues
% 4.05/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.05/0.98  --res_passive_queues_freq               [15;5]
% 4.05/0.98  --res_forward_subs                      full
% 4.05/0.98  --res_backward_subs                     full
% 4.05/0.98  --res_forward_subs_resolution           true
% 4.05/0.98  --res_backward_subs_resolution          true
% 4.05/0.98  --res_orphan_elimination                true
% 4.05/0.98  --res_time_limit                        2.
% 4.05/0.98  --res_out_proof                         true
% 4.05/0.98  
% 4.05/0.98  ------ Superposition Options
% 4.05/0.98  
% 4.05/0.98  --superposition_flag                    true
% 4.05/0.98  --sup_passive_queue_type                priority_queues
% 4.05/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.05/0.98  --sup_passive_queues_freq               [8;1;4]
% 4.05/0.98  --demod_completeness_check              fast
% 4.05/0.98  --demod_use_ground                      true
% 4.05/0.98  --sup_to_prop_solver                    passive
% 4.05/0.98  --sup_prop_simpl_new                    true
% 4.05/0.98  --sup_prop_simpl_given                  true
% 4.05/0.98  --sup_fun_splitting                     true
% 4.05/0.98  --sup_smt_interval                      50000
% 4.05/0.98  
% 4.05/0.98  ------ Superposition Simplification Setup
% 4.05/0.98  
% 4.05/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.05/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.05/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.05/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.05/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 4.05/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.05/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.05/0.98  --sup_immed_triv                        [TrivRules]
% 4.05/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.05/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.05/0.98  --sup_immed_bw_main                     []
% 4.05/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.05/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 4.05/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.05/0.98  --sup_input_bw                          []
% 4.05/0.98  
% 4.05/0.98  ------ Combination Options
% 4.05/0.98  
% 4.05/0.98  --comb_res_mult                         3
% 4.05/0.98  --comb_sup_mult                         2
% 4.05/0.98  --comb_inst_mult                        10
% 4.05/0.98  
% 4.05/0.98  ------ Debug Options
% 4.05/0.98  
% 4.05/0.98  --dbg_backtrace                         false
% 4.05/0.98  --dbg_dump_prop_clauses                 false
% 4.05/0.98  --dbg_dump_prop_clauses_file            -
% 4.05/0.98  --dbg_out_stat                          false
% 4.05/0.98  ------ Parsing...
% 4.05/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.05/0.98  
% 4.05/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 4.05/0.98  
% 4.05/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.05/0.98  
% 4.05/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.05/0.98  ------ Proving...
% 4.05/0.98  ------ Problem Properties 
% 4.05/0.98  
% 4.05/0.98  
% 4.05/0.98  clauses                                 25
% 4.05/0.98  conjectures                             2
% 4.05/0.98  EPR                                     4
% 4.05/0.98  Horn                                    18
% 4.05/0.98  unary                                   5
% 4.05/0.98  binary                                  7
% 4.05/0.98  lits                                    64
% 4.05/0.98  lits eq                                 29
% 4.05/0.98  fd_pure                                 0
% 4.05/0.98  fd_pseudo                               0
% 4.05/0.98  fd_cond                                 3
% 4.05/0.98  fd_pseudo_cond                          3
% 4.05/0.98  AC symbols                              0
% 4.05/0.98  
% 4.05/0.98  ------ Schedule dynamic 5 is on 
% 4.05/0.98  
% 4.05/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.05/0.98  
% 4.05/0.98  
% 4.05/0.98  ------ 
% 4.05/0.98  Current options:
% 4.05/0.98  ------ 
% 4.05/0.98  
% 4.05/0.98  ------ Input Options
% 4.05/0.98  
% 4.05/0.98  --out_options                           all
% 4.05/0.98  --tptp_safe_out                         true
% 4.05/0.98  --problem_path                          ""
% 4.05/0.98  --include_path                          ""
% 4.05/0.98  --clausifier                            res/vclausify_rel
% 4.05/0.98  --clausifier_options                    ""
% 4.05/0.98  --stdin                                 false
% 4.05/0.98  --stats_out                             all
% 4.05/0.98  
% 4.05/0.98  ------ General Options
% 4.05/0.98  
% 4.05/0.98  --fof                                   false
% 4.05/0.98  --time_out_real                         305.
% 4.05/0.98  --time_out_virtual                      -1.
% 4.05/0.98  --symbol_type_check                     false
% 4.05/0.98  --clausify_out                          false
% 4.05/0.98  --sig_cnt_out                           false
% 4.05/0.98  --trig_cnt_out                          false
% 4.05/0.98  --trig_cnt_out_tolerance                1.
% 4.05/0.98  --trig_cnt_out_sk_spl                   false
% 4.05/0.98  --abstr_cl_out                          false
% 4.05/0.98  
% 4.05/0.98  ------ Global Options
% 4.05/0.98  
% 4.05/0.98  --schedule                              default
% 4.05/0.98  --add_important_lit                     false
% 4.05/0.98  --prop_solver_per_cl                    1000
% 4.05/0.98  --min_unsat_core                        false
% 4.05/0.98  --soft_assumptions                      false
% 4.05/0.98  --soft_lemma_size                       3
% 4.05/0.98  --prop_impl_unit_size                   0
% 4.05/0.98  --prop_impl_unit                        []
% 4.05/0.98  --share_sel_clauses                     true
% 4.05/0.98  --reset_solvers                         false
% 4.05/0.98  --bc_imp_inh                            [conj_cone]
% 4.05/0.98  --conj_cone_tolerance                   3.
% 4.05/0.98  --extra_neg_conj                        none
% 4.05/0.98  --large_theory_mode                     true
% 4.05/0.98  --prolific_symb_bound                   200
% 4.05/0.98  --lt_threshold                          2000
% 4.05/0.98  --clause_weak_htbl                      true
% 4.05/0.98  --gc_record_bc_elim                     false
% 4.05/0.98  
% 4.05/0.98  ------ Preprocessing Options
% 4.05/0.98  
% 4.05/0.98  --preprocessing_flag                    true
% 4.05/0.98  --time_out_prep_mult                    0.1
% 4.05/0.98  --splitting_mode                        input
% 4.05/0.98  --splitting_grd                         true
% 4.05/0.98  --splitting_cvd                         false
% 4.05/0.98  --splitting_cvd_svl                     false
% 4.05/0.98  --splitting_nvd                         32
% 4.05/0.98  --sub_typing                            true
% 4.05/0.98  --prep_gs_sim                           true
% 4.05/0.98  --prep_unflatten                        true
% 4.05/0.98  --prep_res_sim                          true
% 4.05/0.98  --prep_upred                            true
% 4.05/0.98  --prep_sem_filter                       exhaustive
% 4.05/0.98  --prep_sem_filter_out                   false
% 4.05/0.98  --pred_elim                             true
% 4.05/0.98  --res_sim_input                         true
% 4.05/0.98  --eq_ax_congr_red                       true
% 4.05/0.98  --pure_diseq_elim                       true
% 4.05/0.98  --brand_transform                       false
% 4.05/0.98  --non_eq_to_eq                          false
% 4.05/0.98  --prep_def_merge                        true
% 4.05/0.98  --prep_def_merge_prop_impl              false
% 4.05/0.98  --prep_def_merge_mbd                    true
% 4.05/0.98  --prep_def_merge_tr_red                 false
% 4.05/0.98  --prep_def_merge_tr_cl                  false
% 4.05/0.98  --smt_preprocessing                     true
% 4.05/0.98  --smt_ac_axioms                         fast
% 4.05/0.98  --preprocessed_out                      false
% 4.05/0.98  --preprocessed_stats                    false
% 4.05/0.98  
% 4.05/0.98  ------ Abstraction refinement Options
% 4.05/0.98  
% 4.05/0.98  --abstr_ref                             []
% 4.05/0.98  --abstr_ref_prep                        false
% 4.05/0.98  --abstr_ref_until_sat                   false
% 4.05/0.98  --abstr_ref_sig_restrict                funpre
% 4.05/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 4.05/0.98  --abstr_ref_under                       []
% 4.05/0.98  
% 4.05/0.98  ------ SAT Options
% 4.05/0.98  
% 4.05/0.98  --sat_mode                              false
% 4.05/0.98  --sat_fm_restart_options                ""
% 4.05/0.98  --sat_gr_def                            false
% 4.05/0.98  --sat_epr_types                         true
% 4.05/0.98  --sat_non_cyclic_types                  false
% 4.05/0.98  --sat_finite_models                     false
% 4.05/0.98  --sat_fm_lemmas                         false
% 4.05/0.98  --sat_fm_prep                           false
% 4.05/0.98  --sat_fm_uc_incr                        true
% 4.05/0.98  --sat_out_model                         small
% 4.05/0.98  --sat_out_clauses                       false
% 4.05/0.98  
% 4.05/0.98  ------ QBF Options
% 4.05/0.98  
% 4.05/0.98  --qbf_mode                              false
% 4.05/0.98  --qbf_elim_univ                         false
% 4.05/0.98  --qbf_dom_inst                          none
% 4.05/0.98  --qbf_dom_pre_inst                      false
% 4.05/0.98  --qbf_sk_in                             false
% 4.05/0.98  --qbf_pred_elim                         true
% 4.05/0.98  --qbf_split                             512
% 4.05/0.98  
% 4.05/0.98  ------ BMC1 Options
% 4.05/0.98  
% 4.05/0.98  --bmc1_incremental                      false
% 4.05/0.98  --bmc1_axioms                           reachable_all
% 4.05/0.98  --bmc1_min_bound                        0
% 4.05/0.98  --bmc1_max_bound                        -1
% 4.05/0.98  --bmc1_max_bound_default                -1
% 4.05/0.98  --bmc1_symbol_reachability              true
% 4.05/0.98  --bmc1_property_lemmas                  false
% 4.05/0.98  --bmc1_k_induction                      false
% 4.05/0.98  --bmc1_non_equiv_states                 false
% 4.05/0.98  --bmc1_deadlock                         false
% 4.05/0.98  --bmc1_ucm                              false
% 4.05/0.98  --bmc1_add_unsat_core                   none
% 4.05/0.98  --bmc1_unsat_core_children              false
% 4.05/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 4.05/0.98  --bmc1_out_stat                         full
% 4.05/0.98  --bmc1_ground_init                      false
% 4.05/0.98  --bmc1_pre_inst_next_state              false
% 4.05/0.98  --bmc1_pre_inst_state                   false
% 4.05/0.98  --bmc1_pre_inst_reach_state             false
% 4.05/0.98  --bmc1_out_unsat_core                   false
% 4.05/0.98  --bmc1_aig_witness_out                  false
% 4.05/0.98  --bmc1_verbose                          false
% 4.05/0.98  --bmc1_dump_clauses_tptp                false
% 4.05/0.98  --bmc1_dump_unsat_core_tptp             false
% 4.05/0.98  --bmc1_dump_file                        -
% 4.05/0.98  --bmc1_ucm_expand_uc_limit              128
% 4.05/0.98  --bmc1_ucm_n_expand_iterations          6
% 4.05/0.98  --bmc1_ucm_extend_mode                  1
% 4.05/0.98  --bmc1_ucm_init_mode                    2
% 4.05/0.98  --bmc1_ucm_cone_mode                    none
% 4.05/0.98  --bmc1_ucm_reduced_relation_type        0
% 4.05/0.98  --bmc1_ucm_relax_model                  4
% 4.05/0.98  --bmc1_ucm_full_tr_after_sat            true
% 4.05/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 4.05/0.98  --bmc1_ucm_layered_model                none
% 4.05/0.98  --bmc1_ucm_max_lemma_size               10
% 4.05/0.98  
% 4.05/0.98  ------ AIG Options
% 4.05/0.98  
% 4.05/0.98  --aig_mode                              false
% 4.05/0.98  
% 4.05/0.98  ------ Instantiation Options
% 4.05/0.98  
% 4.05/0.98  --instantiation_flag                    true
% 4.05/0.98  --inst_sos_flag                         true
% 4.05/0.98  --inst_sos_phase                        true
% 4.05/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.05/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.05/0.98  --inst_lit_sel_side                     none
% 4.05/0.98  --inst_solver_per_active                1400
% 4.05/0.98  --inst_solver_calls_frac                1.
% 4.05/0.98  --inst_passive_queue_type               priority_queues
% 4.05/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.05/0.98  --inst_passive_queues_freq              [25;2]
% 4.05/0.98  --inst_dismatching                      true
% 4.05/0.98  --inst_eager_unprocessed_to_passive     true
% 4.05/0.98  --inst_prop_sim_given                   true
% 4.05/0.98  --inst_prop_sim_new                     false
% 4.05/0.98  --inst_subs_new                         false
% 4.05/0.98  --inst_eq_res_simp                      false
% 4.05/0.98  --inst_subs_given                       false
% 4.05/0.98  --inst_orphan_elimination               true
% 4.05/0.98  --inst_learning_loop_flag               true
% 4.05/0.98  --inst_learning_start                   3000
% 4.05/0.98  --inst_learning_factor                  2
% 4.05/0.98  --inst_start_prop_sim_after_learn       3
% 4.05/0.98  --inst_sel_renew                        solver
% 4.05/0.98  --inst_lit_activity_flag                true
% 4.05/0.98  --inst_restr_to_given                   false
% 4.05/0.98  --inst_activity_threshold               500
% 4.05/0.98  --inst_out_proof                        true
% 4.05/0.98  
% 4.05/0.98  ------ Resolution Options
% 4.05/0.98  
% 4.05/0.98  --resolution_flag                       false
% 4.05/0.98  --res_lit_sel                           adaptive
% 4.05/0.98  --res_lit_sel_side                      none
% 4.05/0.98  --res_ordering                          kbo
% 4.05/0.98  --res_to_prop_solver                    active
% 4.05/0.98  --res_prop_simpl_new                    false
% 4.05/0.98  --res_prop_simpl_given                  true
% 4.05/0.98  --res_passive_queue_type                priority_queues
% 4.05/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.05/0.98  --res_passive_queues_freq               [15;5]
% 4.05/0.98  --res_forward_subs                      full
% 4.05/0.98  --res_backward_subs                     full
% 4.05/0.98  --res_forward_subs_resolution           true
% 4.05/0.98  --res_backward_subs_resolution          true
% 4.05/0.98  --res_orphan_elimination                true
% 4.05/0.98  --res_time_limit                        2.
% 4.05/0.98  --res_out_proof                         true
% 4.05/0.98  
% 4.05/0.98  ------ Superposition Options
% 4.05/0.98  
% 4.05/0.98  --superposition_flag                    true
% 4.05/0.98  --sup_passive_queue_type                priority_queues
% 4.05/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.05/0.98  --sup_passive_queues_freq               [8;1;4]
% 4.05/0.98  --demod_completeness_check              fast
% 4.05/0.98  --demod_use_ground                      true
% 4.05/0.98  --sup_to_prop_solver                    passive
% 4.05/0.98  --sup_prop_simpl_new                    true
% 4.05/0.98  --sup_prop_simpl_given                  true
% 4.05/0.98  --sup_fun_splitting                     true
% 4.05/0.98  --sup_smt_interval                      50000
% 4.05/0.98  
% 4.05/0.98  ------ Superposition Simplification Setup
% 4.05/0.98  
% 4.05/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.05/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.05/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.05/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.05/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 4.05/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.05/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.05/0.98  --sup_immed_triv                        [TrivRules]
% 4.05/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.05/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.05/0.98  --sup_immed_bw_main                     []
% 4.05/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.05/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 4.05/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.05/0.98  --sup_input_bw                          []
% 4.05/0.98  
% 4.05/0.98  ------ Combination Options
% 4.05/0.98  
% 4.05/0.98  --comb_res_mult                         3
% 4.05/0.98  --comb_sup_mult                         2
% 4.05/0.98  --comb_inst_mult                        10
% 4.05/0.98  
% 4.05/0.98  ------ Debug Options
% 4.05/0.98  
% 4.05/0.98  --dbg_backtrace                         false
% 4.05/0.98  --dbg_dump_prop_clauses                 false
% 4.05/0.98  --dbg_dump_prop_clauses_file            -
% 4.05/0.98  --dbg_out_stat                          false
% 4.05/0.98  
% 4.05/0.98  
% 4.05/0.98  
% 4.05/0.98  
% 4.05/0.98  ------ Proving...
% 4.05/0.98  
% 4.05/0.98  
% 4.05/0.98  % SZS status Theorem for theBenchmark.p
% 4.05/0.98  
% 4.05/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 4.05/0.98  
% 4.05/0.98  fof(f13,conjecture,(
% 4.05/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 4.05/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/0.98  
% 4.05/0.98  fof(f14,negated_conjecture,(
% 4.05/0.98    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 4.05/0.98    inference(negated_conjecture,[],[f13])).
% 4.05/0.98  
% 4.05/0.98  fof(f26,plain,(
% 4.05/0.98    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 4.05/0.98    inference(ennf_transformation,[],[f14])).
% 4.05/0.98  
% 4.05/0.98  fof(f27,plain,(
% 4.05/0.98    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 4.05/0.98    inference(flattening,[],[f26])).
% 4.05/0.98  
% 4.05/0.98  fof(f45,plain,(
% 4.05/0.98    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (k1_funct_1(sK8,sK7) != sK6 & r2_hidden(sK7,sK5) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6)))) & v1_funct_2(sK8,sK5,k1_tarski(sK6)) & v1_funct_1(sK8))),
% 4.05/0.98    introduced(choice_axiom,[])).
% 4.05/0.98  
% 4.05/0.98  fof(f46,plain,(
% 4.05/0.98    k1_funct_1(sK8,sK7) != sK6 & r2_hidden(sK7,sK5) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6)))) & v1_funct_2(sK8,sK5,k1_tarski(sK6)) & v1_funct_1(sK8)),
% 4.05/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f27,f45])).
% 4.05/0.98  
% 4.05/0.98  fof(f80,plain,(
% 4.05/0.98    r2_hidden(sK7,sK5)),
% 4.05/0.98    inference(cnf_transformation,[],[f46])).
% 4.05/0.98  
% 4.05/0.98  fof(f6,axiom,(
% 4.05/0.98    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 4.05/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/0.98  
% 4.05/0.98  fof(f17,plain,(
% 4.05/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 4.05/0.98    inference(ennf_transformation,[],[f6])).
% 4.05/0.98  
% 4.05/0.98  fof(f37,plain,(
% 4.05/0.98    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 4.05/0.98    inference(nnf_transformation,[],[f17])).
% 4.05/0.98  
% 4.05/0.98  fof(f59,plain,(
% 4.05/0.98    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 4.05/0.98    inference(cnf_transformation,[],[f37])).
% 4.05/0.98  
% 4.05/0.98  fof(f10,axiom,(
% 4.05/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 4.05/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/0.98  
% 4.05/0.98  fof(f15,plain,(
% 4.05/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 4.05/0.98    inference(pure_predicate_removal,[],[f10])).
% 4.05/0.98  
% 4.05/0.98  fof(f22,plain,(
% 4.05/0.98    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.05/0.98    inference(ennf_transformation,[],[f15])).
% 4.05/0.98  
% 4.05/0.98  fof(f69,plain,(
% 4.05/0.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.05/0.98    inference(cnf_transformation,[],[f22])).
% 4.05/0.98  
% 4.05/0.98  fof(f9,axiom,(
% 4.05/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 4.05/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/0.98  
% 4.05/0.98  fof(f21,plain,(
% 4.05/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.05/0.98    inference(ennf_transformation,[],[f9])).
% 4.05/0.98  
% 4.05/0.98  fof(f68,plain,(
% 4.05/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.05/0.98    inference(cnf_transformation,[],[f21])).
% 4.05/0.98  
% 4.05/0.98  fof(f79,plain,(
% 4.05/0.98    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6))))),
% 4.05/0.98    inference(cnf_transformation,[],[f46])).
% 4.05/0.98  
% 4.05/0.98  fof(f4,axiom,(
% 4.05/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 4.05/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/0.98  
% 4.05/0.98  fof(f57,plain,(
% 4.05/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 4.05/0.98    inference(cnf_transformation,[],[f4])).
% 4.05/0.98  
% 4.05/0.98  fof(f5,axiom,(
% 4.05/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 4.05/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/0.98  
% 4.05/0.98  fof(f58,plain,(
% 4.05/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 4.05/0.98    inference(cnf_transformation,[],[f5])).
% 4.05/0.98  
% 4.05/0.98  fof(f82,plain,(
% 4.05/0.98    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 4.05/0.98    inference(definition_unfolding,[],[f57,f58])).
% 4.05/0.98  
% 4.05/0.98  fof(f89,plain,(
% 4.05/0.98    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_enumset1(sK6,sK6,sK6))))),
% 4.05/0.98    inference(definition_unfolding,[],[f79,f82])).
% 4.05/0.98  
% 4.05/0.98  fof(f7,axiom,(
% 4.05/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 4.05/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/0.98  
% 4.05/0.98  fof(f18,plain,(
% 4.05/0.98    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.05/0.98    inference(ennf_transformation,[],[f7])).
% 4.05/0.98  
% 4.05/0.98  fof(f19,plain,(
% 4.05/0.98    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.05/0.98    inference(flattening,[],[f18])).
% 4.05/0.98  
% 4.05/0.98  fof(f38,plain,(
% 4.05/0.98    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.05/0.98    inference(nnf_transformation,[],[f19])).
% 4.05/0.98  
% 4.05/0.98  fof(f39,plain,(
% 4.05/0.98    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.05/0.98    inference(rectify,[],[f38])).
% 4.05/0.98  
% 4.05/0.98  fof(f42,plain,(
% 4.05/0.98    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))))),
% 4.05/0.98    introduced(choice_axiom,[])).
% 4.05/0.98  
% 4.05/0.98  fof(f41,plain,(
% 4.05/0.98    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X1)) = X2 & r2_hidden(sK3(X0,X1),k1_relat_1(X0))))) )),
% 4.05/0.98    introduced(choice_axiom,[])).
% 4.05/0.98  
% 4.05/0.98  fof(f40,plain,(
% 4.05/0.98    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK2(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1))))),
% 4.05/0.98    introduced(choice_axiom,[])).
% 4.05/0.98  
% 4.05/0.98  fof(f43,plain,(
% 4.05/0.98    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & ((k1_funct_1(X0,sK3(X0,X1)) = sK2(X0,X1) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.05/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f39,f42,f41,f40])).
% 4.05/0.98  
% 4.05/0.98  fof(f63,plain,(
% 4.05/0.98    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.05/0.98    inference(cnf_transformation,[],[f43])).
% 4.05/0.98  
% 4.05/0.98  fof(f96,plain,(
% 4.05/0.98    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.05/0.98    inference(equality_resolution,[],[f63])).
% 4.05/0.98  
% 4.05/0.98  fof(f97,plain,(
% 4.05/0.98    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.05/0.98    inference(equality_resolution,[],[f96])).
% 4.05/0.98  
% 4.05/0.98  fof(f77,plain,(
% 4.05/0.98    v1_funct_1(sK8)),
% 4.05/0.98    inference(cnf_transformation,[],[f46])).
% 4.05/0.98  
% 4.05/0.98  fof(f1,axiom,(
% 4.05/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 4.05/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/0.98  
% 4.05/0.98  fof(f16,plain,(
% 4.05/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 4.05/0.98    inference(ennf_transformation,[],[f1])).
% 4.05/0.98  
% 4.05/0.98  fof(f28,plain,(
% 4.05/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 4.05/0.98    inference(nnf_transformation,[],[f16])).
% 4.05/0.98  
% 4.05/0.98  fof(f29,plain,(
% 4.05/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 4.05/0.98    inference(rectify,[],[f28])).
% 4.05/0.98  
% 4.05/0.98  fof(f30,plain,(
% 4.05/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 4.05/0.98    introduced(choice_axiom,[])).
% 4.05/0.98  
% 4.05/0.98  fof(f31,plain,(
% 4.05/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 4.05/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 4.05/0.98  
% 4.05/0.98  fof(f47,plain,(
% 4.05/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 4.05/0.98    inference(cnf_transformation,[],[f31])).
% 4.05/0.98  
% 4.05/0.98  fof(f3,axiom,(
% 4.05/0.98    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 4.05/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/0.98  
% 4.05/0.98  fof(f32,plain,(
% 4.05/0.98    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 4.05/0.98    inference(nnf_transformation,[],[f3])).
% 4.05/0.98  
% 4.05/0.98  fof(f33,plain,(
% 4.05/0.98    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 4.05/0.98    inference(flattening,[],[f32])).
% 4.05/0.98  
% 4.05/0.98  fof(f34,plain,(
% 4.05/0.98    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 4.05/0.98    inference(rectify,[],[f33])).
% 4.05/0.98  
% 4.05/0.98  fof(f35,plain,(
% 4.05/0.98    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2))))),
% 4.05/0.98    introduced(choice_axiom,[])).
% 4.05/0.98  
% 4.05/0.98  fof(f36,plain,(
% 4.05/0.98    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 4.05/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).
% 4.05/0.98  
% 4.05/0.98  fof(f51,plain,(
% 4.05/0.98    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 4.05/0.98    inference(cnf_transformation,[],[f36])).
% 4.05/0.98  
% 4.05/0.98  fof(f88,plain,(
% 4.05/0.98    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 4.05/0.98    inference(definition_unfolding,[],[f51,f58])).
% 4.05/0.98  
% 4.05/0.98  fof(f95,plain,(
% 4.05/0.98    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k1_enumset1(X0,X0,X1))) )),
% 4.05/0.98    inference(equality_resolution,[],[f88])).
% 4.05/0.98  
% 4.05/0.98  fof(f78,plain,(
% 4.05/0.98    v1_funct_2(sK8,sK5,k1_tarski(sK6))),
% 4.05/0.98    inference(cnf_transformation,[],[f46])).
% 4.05/0.98  
% 4.05/0.98  fof(f90,plain,(
% 4.05/0.98    v1_funct_2(sK8,sK5,k1_enumset1(sK6,sK6,sK6))),
% 4.05/0.98    inference(definition_unfolding,[],[f78,f82])).
% 4.05/0.98  
% 4.05/0.98  fof(f12,axiom,(
% 4.05/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 4.05/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/0.98  
% 4.05/0.98  fof(f24,plain,(
% 4.05/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.05/0.98    inference(ennf_transformation,[],[f12])).
% 4.05/0.98  
% 4.05/0.98  fof(f25,plain,(
% 4.05/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.05/0.98    inference(flattening,[],[f24])).
% 4.05/0.98  
% 4.05/0.98  fof(f44,plain,(
% 4.05/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.05/0.98    inference(nnf_transformation,[],[f25])).
% 4.05/0.98  
% 4.05/0.98  fof(f71,plain,(
% 4.05/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.05/0.98    inference(cnf_transformation,[],[f44])).
% 4.05/0.98  
% 4.05/0.98  fof(f11,axiom,(
% 4.05/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 4.05/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/0.98  
% 4.05/0.98  fof(f23,plain,(
% 4.05/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.05/0.98    inference(ennf_transformation,[],[f11])).
% 4.05/0.98  
% 4.05/0.98  fof(f70,plain,(
% 4.05/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.05/0.98    inference(cnf_transformation,[],[f23])).
% 4.05/0.98  
% 4.05/0.98  fof(f52,plain,(
% 4.05/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 4.05/0.98    inference(cnf_transformation,[],[f36])).
% 4.05/0.98  
% 4.05/0.98  fof(f87,plain,(
% 4.05/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k1_enumset1(X0,X0,X1) != X2) )),
% 4.05/0.98    inference(definition_unfolding,[],[f52,f58])).
% 4.05/0.98  
% 4.05/0.98  fof(f93,plain,(
% 4.05/0.98    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k1_enumset1(X4,X4,X1) != X2) )),
% 4.05/0.98    inference(equality_resolution,[],[f87])).
% 4.05/0.98  
% 4.05/0.98  fof(f94,plain,(
% 4.05/0.98    ( ! [X4,X1] : (r2_hidden(X4,k1_enumset1(X4,X4,X1))) )),
% 4.05/0.98    inference(equality_resolution,[],[f93])).
% 4.05/0.98  
% 4.05/0.98  fof(f2,axiom,(
% 4.05/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 4.05/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/0.98  
% 4.05/0.98  fof(f50,plain,(
% 4.05/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 4.05/0.98    inference(cnf_transformation,[],[f2])).
% 4.05/0.98  
% 4.05/0.98  fof(f8,axiom,(
% 4.05/0.98    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 4.05/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/0.98  
% 4.05/0.98  fof(f20,plain,(
% 4.05/0.98    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 4.05/0.98    inference(ennf_transformation,[],[f8])).
% 4.05/0.98  
% 4.05/0.98  fof(f67,plain,(
% 4.05/0.98    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 4.05/0.98    inference(cnf_transformation,[],[f20])).
% 4.05/0.98  
% 4.05/0.98  fof(f81,plain,(
% 4.05/0.98    k1_funct_1(sK8,sK7) != sK6),
% 4.05/0.98    inference(cnf_transformation,[],[f46])).
% 4.05/0.98  
% 4.05/0.98  cnf(c_29,negated_conjecture,
% 4.05/0.98      ( r2_hidden(sK7,sK5) ),
% 4.05/0.98      inference(cnf_transformation,[],[f80]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_1766,plain,
% 4.05/0.98      ( r2_hidden(sK7,sK5) = iProver_top ),
% 4.05/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_11,plain,
% 4.05/0.98      ( ~ v5_relat_1(X0,X1)
% 4.05/0.98      | r1_tarski(k2_relat_1(X0),X1)
% 4.05/0.98      | ~ v1_relat_1(X0) ),
% 4.05/0.98      inference(cnf_transformation,[],[f59]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_20,plain,
% 4.05/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.05/0.98      | v5_relat_1(X0,X2) ),
% 4.05/0.98      inference(cnf_transformation,[],[f69]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_355,plain,
% 4.05/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.05/0.98      | r1_tarski(k2_relat_1(X3),X4)
% 4.05/0.98      | ~ v1_relat_1(X3)
% 4.05/0.98      | X0 != X3
% 4.05/0.98      | X2 != X4 ),
% 4.05/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_20]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_356,plain,
% 4.05/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.05/0.98      | r1_tarski(k2_relat_1(X0),X2)
% 4.05/0.98      | ~ v1_relat_1(X0) ),
% 4.05/0.98      inference(unflattening,[status(thm)],[c_355]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_19,plain,
% 4.05/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.05/0.98      | v1_relat_1(X0) ),
% 4.05/0.98      inference(cnf_transformation,[],[f68]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_360,plain,
% 4.05/0.98      ( r1_tarski(k2_relat_1(X0),X2)
% 4.05/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 4.05/0.98      inference(global_propositional_subsumption,
% 4.05/0.98                [status(thm)],
% 4.05/0.98                [c_356,c_19]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_361,plain,
% 4.05/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.05/0.98      | r1_tarski(k2_relat_1(X0),X2) ),
% 4.05/0.98      inference(renaming,[status(thm)],[c_360]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_30,negated_conjecture,
% 4.05/0.98      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_enumset1(sK6,sK6,sK6)))) ),
% 4.05/0.98      inference(cnf_transformation,[],[f89]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_488,plain,
% 4.05/0.98      ( r1_tarski(k2_relat_1(X0),X1)
% 4.05/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK5,k1_enumset1(sK6,sK6,sK6))) != k1_zfmisc_1(k2_zfmisc_1(X2,X1))
% 4.05/0.98      | sK8 != X0 ),
% 4.05/0.98      inference(resolution_lifted,[status(thm)],[c_361,c_30]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_489,plain,
% 4.05/0.98      ( r1_tarski(k2_relat_1(sK8),X0)
% 4.05/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK5,k1_enumset1(sK6,sK6,sK6))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0)) ),
% 4.05/0.98      inference(unflattening,[status(thm)],[c_488]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_1765,plain,
% 4.05/0.98      ( k1_zfmisc_1(k2_zfmisc_1(sK5,k1_enumset1(sK6,sK6,sK6))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 4.05/0.98      | r1_tarski(k2_relat_1(sK8),X1) = iProver_top ),
% 4.05/0.98      inference(predicate_to_equality,[status(thm)],[c_489]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_2109,plain,
% 4.05/0.98      ( r1_tarski(k2_relat_1(sK8),k1_enumset1(sK6,sK6,sK6)) = iProver_top ),
% 4.05/0.98      inference(equality_resolution,[status(thm)],[c_1765]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_15,plain,
% 4.05/0.98      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 4.05/0.98      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 4.05/0.98      | ~ v1_funct_1(X1)
% 4.05/0.98      | ~ v1_relat_1(X1) ),
% 4.05/0.98      inference(cnf_transformation,[],[f97]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_32,negated_conjecture,
% 4.05/0.98      ( v1_funct_1(sK8) ),
% 4.05/0.98      inference(cnf_transformation,[],[f77]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_826,plain,
% 4.05/0.98      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 4.05/0.98      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 4.05/0.98      | ~ v1_relat_1(X1)
% 4.05/0.98      | sK8 != X1 ),
% 4.05/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_32]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_827,plain,
% 4.05/0.98      ( ~ r2_hidden(X0,k1_relat_1(sK8))
% 4.05/0.98      | r2_hidden(k1_funct_1(sK8,X0),k2_relat_1(sK8))
% 4.05/0.98      | ~ v1_relat_1(sK8) ),
% 4.05/0.98      inference(unflattening,[status(thm)],[c_826]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_1759,plain,
% 4.05/0.98      ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 4.05/0.98      | r2_hidden(k1_funct_1(sK8,X0),k2_relat_1(sK8)) = iProver_top
% 4.05/0.98      | v1_relat_1(sK8) != iProver_top ),
% 4.05/0.98      inference(predicate_to_equality,[status(thm)],[c_827]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_828,plain,
% 4.05/0.98      ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 4.05/0.98      | r2_hidden(k1_funct_1(sK8,X0),k2_relat_1(sK8)) = iProver_top
% 4.05/0.98      | v1_relat_1(sK8) != iProver_top ),
% 4.05/0.98      inference(predicate_to_equality,[status(thm)],[c_827]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_545,plain,
% 4.05/0.98      ( v1_relat_1(X0)
% 4.05/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK5,k1_enumset1(sK6,sK6,sK6))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 4.05/0.98      | sK8 != X0 ),
% 4.05/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_30]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_546,plain,
% 4.05/0.98      ( v1_relat_1(sK8)
% 4.05/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK5,k1_enumset1(sK6,sK6,sK6))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 4.05/0.98      inference(unflattening,[status(thm)],[c_545]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_1838,plain,
% 4.05/0.98      ( v1_relat_1(sK8)
% 4.05/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK5,k1_enumset1(sK6,sK6,sK6))) != k1_zfmisc_1(k2_zfmisc_1(sK5,k1_enumset1(sK6,sK6,sK6))) ),
% 4.05/0.98      inference(instantiation,[status(thm)],[c_546]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_1839,plain,
% 4.05/0.98      ( k1_zfmisc_1(k2_zfmisc_1(sK5,k1_enumset1(sK6,sK6,sK6))) != k1_zfmisc_1(k2_zfmisc_1(sK5,k1_enumset1(sK6,sK6,sK6)))
% 4.05/0.98      | v1_relat_1(sK8) = iProver_top ),
% 4.05/0.98      inference(predicate_to_equality,[status(thm)],[c_1838]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_1413,plain,( X0 = X0 ),theory(equality) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_1905,plain,
% 4.05/0.98      ( k1_zfmisc_1(k2_zfmisc_1(sK5,k1_enumset1(sK6,sK6,sK6))) = k1_zfmisc_1(k2_zfmisc_1(sK5,k1_enumset1(sK6,sK6,sK6))) ),
% 4.05/0.98      inference(instantiation,[status(thm)],[c_1413]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_2501,plain,
% 4.05/0.98      ( r2_hidden(k1_funct_1(sK8,X0),k2_relat_1(sK8)) = iProver_top
% 4.05/0.98      | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top ),
% 4.05/0.98      inference(global_propositional_subsumption,
% 4.05/0.98                [status(thm)],
% 4.05/0.98                [c_1759,c_828,c_1839,c_1905]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_2502,plain,
% 4.05/0.98      ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 4.05/0.98      | r2_hidden(k1_funct_1(sK8,X0),k2_relat_1(sK8)) = iProver_top ),
% 4.05/0.98      inference(renaming,[status(thm)],[c_2501]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_2,plain,
% 4.05/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 4.05/0.98      inference(cnf_transformation,[],[f47]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_1775,plain,
% 4.05/0.98      ( r2_hidden(X0,X1) != iProver_top
% 4.05/0.98      | r2_hidden(X0,X2) = iProver_top
% 4.05/0.98      | r1_tarski(X1,X2) != iProver_top ),
% 4.05/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_3098,plain,
% 4.05/0.98      ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 4.05/0.98      | r2_hidden(k1_funct_1(sK8,X0),X1) = iProver_top
% 4.05/0.98      | r1_tarski(k2_relat_1(sK8),X1) != iProver_top ),
% 4.05/0.98      inference(superposition,[status(thm)],[c_2502,c_1775]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_9,plain,
% 4.05/0.98      ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 4.05/0.98      inference(cnf_transformation,[],[f95]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_1768,plain,
% 4.05/0.98      ( X0 = X1
% 4.05/0.98      | X0 = X2
% 4.05/0.98      | r2_hidden(X0,k1_enumset1(X1,X1,X2)) != iProver_top ),
% 4.05/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_3557,plain,
% 4.05/0.98      ( k1_funct_1(sK8,X0) = X1
% 4.05/0.98      | k1_funct_1(sK8,X0) = X2
% 4.05/0.98      | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 4.05/0.98      | r1_tarski(k2_relat_1(sK8),k1_enumset1(X1,X1,X2)) != iProver_top ),
% 4.05/0.98      inference(superposition,[status(thm)],[c_3098,c_1768]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_31,negated_conjecture,
% 4.05/0.98      ( v1_funct_2(sK8,sK5,k1_enumset1(sK6,sK6,sK6)) ),
% 4.05/0.98      inference(cnf_transformation,[],[f90]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_27,plain,
% 4.05/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 4.05/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.05/0.98      | k1_relset_1(X1,X2,X0) = X1
% 4.05/0.98      | k1_xboole_0 = X2 ),
% 4.05/0.98      inference(cnf_transformation,[],[f71]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_500,plain,
% 4.05/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 4.05/0.98      | k1_relset_1(X1,X2,X0) = X1
% 4.05/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK5,k1_enumset1(sK6,sK6,sK6))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 4.05/0.98      | sK8 != X0
% 4.05/0.98      | k1_xboole_0 = X2 ),
% 4.05/0.98      inference(resolution_lifted,[status(thm)],[c_27,c_30]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_501,plain,
% 4.05/0.98      ( ~ v1_funct_2(sK8,X0,X1)
% 4.05/0.98      | k1_relset_1(X0,X1,sK8) = X0
% 4.05/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK5,k1_enumset1(sK6,sK6,sK6))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 4.05/0.98      | k1_xboole_0 = X1 ),
% 4.05/0.98      inference(unflattening,[status(thm)],[c_500]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_1012,plain,
% 4.05/0.98      ( k1_relset_1(X0,X1,sK8) = X0
% 4.05/0.98      | k1_enumset1(sK6,sK6,sK6) != X1
% 4.05/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK5,k1_enumset1(sK6,sK6,sK6))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 4.05/0.98      | sK5 != X0
% 4.05/0.98      | sK8 != sK8
% 4.05/0.98      | k1_xboole_0 = X1 ),
% 4.05/0.98      inference(resolution_lifted,[status(thm)],[c_31,c_501]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_1013,plain,
% 4.05/0.98      ( k1_relset_1(sK5,k1_enumset1(sK6,sK6,sK6),sK8) = sK5
% 4.05/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK5,k1_enumset1(sK6,sK6,sK6))) != k1_zfmisc_1(k2_zfmisc_1(sK5,k1_enumset1(sK6,sK6,sK6)))
% 4.05/0.98      | k1_xboole_0 = k1_enumset1(sK6,sK6,sK6) ),
% 4.05/0.98      inference(unflattening,[status(thm)],[c_1012]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_1086,plain,
% 4.05/0.98      ( k1_relset_1(sK5,k1_enumset1(sK6,sK6,sK6),sK8) = sK5
% 4.05/0.98      | k1_xboole_0 = k1_enumset1(sK6,sK6,sK6) ),
% 4.05/0.98      inference(equality_resolution_simp,[status(thm)],[c_1013]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_21,plain,
% 4.05/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.05/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 4.05/0.98      inference(cnf_transformation,[],[f70]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_536,plain,
% 4.05/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 4.05/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK5,k1_enumset1(sK6,sK6,sK6))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 4.05/0.98      | sK8 != X2 ),
% 4.05/0.98      inference(resolution_lifted,[status(thm)],[c_21,c_30]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_537,plain,
% 4.05/0.98      ( k1_relset_1(X0,X1,sK8) = k1_relat_1(sK8)
% 4.05/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK5,k1_enumset1(sK6,sK6,sK6))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 4.05/0.98      inference(unflattening,[status(thm)],[c_536]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_1908,plain,
% 4.05/0.98      ( k1_relset_1(sK5,k1_enumset1(sK6,sK6,sK6),sK8) = k1_relat_1(sK8) ),
% 4.05/0.98      inference(equality_resolution,[status(thm)],[c_537]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_2144,plain,
% 4.05/0.98      ( k1_enumset1(sK6,sK6,sK6) = k1_xboole_0 | k1_relat_1(sK8) = sK5 ),
% 4.05/0.98      inference(demodulation,[status(thm)],[c_1086,c_1908]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_8,plain,
% 4.05/0.98      ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) ),
% 4.05/0.98      inference(cnf_transformation,[],[f94]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_1769,plain,
% 4.05/0.98      ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) = iProver_top ),
% 4.05/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_2222,plain,
% 4.05/0.98      ( k1_relat_1(sK8) = sK5
% 4.05/0.98      | r2_hidden(sK6,k1_xboole_0) = iProver_top ),
% 4.05/0.98      inference(superposition,[status(thm)],[c_2144,c_1769]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_3080,plain,
% 4.05/0.98      ( k1_relat_1(sK8) = sK5
% 4.05/0.98      | sK6 = X0
% 4.05/0.98      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 4.05/0.98      inference(superposition,[status(thm)],[c_2144,c_1768]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_3,plain,
% 4.05/0.98      ( r1_tarski(k1_xboole_0,X0) ),
% 4.05/0.98      inference(cnf_transformation,[],[f50]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_18,plain,
% 4.05/0.98      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 4.05/0.98      inference(cnf_transformation,[],[f67]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_451,plain,
% 4.05/0.98      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 4.05/0.98      inference(resolution_lifted,[status(thm)],[c_3,c_18]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_452,plain,
% 4.05/0.98      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 4.05/0.98      inference(unflattening,[status(thm)],[c_451]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_453,plain,
% 4.05/0.98      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 4.05/0.98      inference(predicate_to_equality,[status(thm)],[c_452]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_4812,plain,
% 4.05/0.98      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 4.05/0.98      inference(global_propositional_subsumption,
% 4.05/0.98                [status(thm)],
% 4.05/0.98                [c_3080,c_453]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_4820,plain,
% 4.05/0.98      ( k1_relat_1(sK8) = sK5 ),
% 4.05/0.98      inference(superposition,[status(thm)],[c_2222,c_4812]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_14201,plain,
% 4.05/0.98      ( k1_funct_1(sK8,X0) = X1
% 4.05/0.98      | k1_funct_1(sK8,X0) = X2
% 4.05/0.98      | r2_hidden(X0,sK5) != iProver_top
% 4.05/0.98      | r1_tarski(k2_relat_1(sK8),k1_enumset1(X1,X1,X2)) != iProver_top ),
% 4.05/0.98      inference(light_normalisation,[status(thm)],[c_3557,c_4820]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_14207,plain,
% 4.05/0.98      ( k1_funct_1(sK8,X0) = sK6 | r2_hidden(X0,sK5) != iProver_top ),
% 4.05/0.98      inference(superposition,[status(thm)],[c_2109,c_14201]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_14398,plain,
% 4.05/0.98      ( k1_funct_1(sK8,sK7) = sK6 ),
% 4.05/0.98      inference(superposition,[status(thm)],[c_1766,c_14207]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(c_28,negated_conjecture,
% 4.05/0.98      ( k1_funct_1(sK8,sK7) != sK6 ),
% 4.05/0.98      inference(cnf_transformation,[],[f81]) ).
% 4.05/0.98  
% 4.05/0.98  cnf(contradiction,plain,
% 4.05/0.98      ( $false ),
% 4.05/0.98      inference(minisat,[status(thm)],[c_14398,c_28]) ).
% 4.05/0.98  
% 4.05/0.98  
% 4.05/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 4.05/0.98  
% 4.05/0.98  ------                               Statistics
% 4.05/0.98  
% 4.05/0.98  ------ General
% 4.05/0.98  
% 4.05/0.98  abstr_ref_over_cycles:                  0
% 4.05/0.98  abstr_ref_under_cycles:                 0
% 4.05/0.98  gc_basic_clause_elim:                   0
% 4.05/0.98  forced_gc_time:                         0
% 4.05/0.98  parsing_time:                           0.008
% 4.05/0.98  unif_index_cands_time:                  0.
% 4.05/0.98  unif_index_add_time:                    0.
% 4.05/0.98  orderings_time:                         0.
% 4.05/0.98  out_proof_time:                         0.01
% 4.05/0.98  total_time:                             0.453
% 4.05/0.98  num_of_symbols:                         55
% 4.05/0.98  num_of_terms:                           13463
% 4.05/0.98  
% 4.05/0.98  ------ Preprocessing
% 4.05/0.98  
% 4.05/0.98  num_of_splits:                          0
% 4.05/0.98  num_of_split_atoms:                     0
% 4.05/0.98  num_of_reused_defs:                     0
% 4.05/0.98  num_eq_ax_congr_red:                    37
% 4.05/0.98  num_of_sem_filtered_clauses:            1
% 4.05/0.98  num_of_subtypes:                        0
% 4.05/0.98  monotx_restored_types:                  0
% 4.05/0.98  sat_num_of_epr_types:                   0
% 4.05/0.98  sat_num_of_non_cyclic_types:            0
% 4.05/0.98  sat_guarded_non_collapsed_types:        0
% 4.05/0.98  num_pure_diseq_elim:                    0
% 4.05/0.98  simp_replaced_by:                       0
% 4.05/0.98  res_preprocessed:                       139
% 4.05/0.98  prep_upred:                             0
% 4.05/0.98  prep_unflattend:                        81
% 4.05/0.98  smt_new_axioms:                         0
% 4.05/0.98  pred_elim_cands:                        3
% 4.05/0.98  pred_elim:                              4
% 4.05/0.98  pred_elim_cl:                           8
% 4.05/0.98  pred_elim_cycles:                       10
% 4.05/0.98  merged_defs:                            0
% 4.05/0.98  merged_defs_ncl:                        0
% 4.05/0.98  bin_hyper_res:                          0
% 4.05/0.98  prep_cycles:                            4
% 4.05/0.98  pred_elim_time:                         0.016
% 4.05/0.98  splitting_time:                         0.
% 4.05/0.98  sem_filter_time:                        0.
% 4.05/0.98  monotx_time:                            0.
% 4.05/0.98  subtype_inf_time:                       0.
% 4.05/0.98  
% 4.05/0.98  ------ Problem properties
% 4.05/0.98  
% 4.05/0.98  clauses:                                25
% 4.05/0.98  conjectures:                            2
% 4.05/0.98  epr:                                    4
% 4.05/0.98  horn:                                   18
% 4.05/0.98  ground:                                 5
% 4.05/0.98  unary:                                  5
% 4.05/0.98  binary:                                 7
% 4.05/0.98  lits:                                   64
% 4.05/0.98  lits_eq:                                29
% 4.05/0.98  fd_pure:                                0
% 4.05/0.98  fd_pseudo:                              0
% 4.05/0.98  fd_cond:                                3
% 4.05/0.98  fd_pseudo_cond:                         3
% 4.05/0.98  ac_symbols:                             0
% 4.05/0.98  
% 4.05/0.98  ------ Propositional Solver
% 4.05/0.98  
% 4.05/0.98  prop_solver_calls:                      29
% 4.05/0.98  prop_fast_solver_calls:                 1484
% 4.05/0.98  smt_solver_calls:                       0
% 4.05/0.98  smt_fast_solver_calls:                  0
% 4.05/0.98  prop_num_of_clauses:                    6482
% 4.05/0.98  prop_preprocess_simplified:             13529
% 4.05/0.98  prop_fo_subsumed:                       37
% 4.05/0.98  prop_solver_time:                       0.
% 4.05/0.98  smt_solver_time:                        0.
% 4.05/0.98  smt_fast_solver_time:                   0.
% 4.05/0.98  prop_fast_solver_time:                  0.
% 4.05/0.98  prop_unsat_core_time:                   0.
% 4.05/0.98  
% 4.05/0.98  ------ QBF
% 4.05/0.98  
% 4.05/0.98  qbf_q_res:                              0
% 4.05/0.98  qbf_num_tautologies:                    0
% 4.05/0.98  qbf_prep_cycles:                        0
% 4.05/0.98  
% 4.05/0.98  ------ BMC1
% 4.05/0.98  
% 4.05/0.98  bmc1_current_bound:                     -1
% 4.05/0.98  bmc1_last_solved_bound:                 -1
% 4.05/0.98  bmc1_unsat_core_size:                   -1
% 4.05/0.98  bmc1_unsat_core_parents_size:           -1
% 4.05/0.98  bmc1_merge_next_fun:                    0
% 4.05/0.98  bmc1_unsat_core_clauses_time:           0.
% 4.05/0.98  
% 4.05/0.98  ------ Instantiation
% 4.05/0.98  
% 4.05/0.98  inst_num_of_clauses:                    1598
% 4.05/0.98  inst_num_in_passive:                    592
% 4.05/0.98  inst_num_in_active:                     556
% 4.05/0.98  inst_num_in_unprocessed:                450
% 4.05/0.98  inst_num_of_loops:                      730
% 4.05/0.98  inst_num_of_learning_restarts:          0
% 4.05/0.98  inst_num_moves_active_passive:          173
% 4.05/0.98  inst_lit_activity:                      0
% 4.05/0.98  inst_lit_activity_moves:                0
% 4.05/0.98  inst_num_tautologies:                   0
% 4.05/0.98  inst_num_prop_implied:                  0
% 4.05/0.98  inst_num_existing_simplified:           0
% 4.05/0.98  inst_num_eq_res_simplified:             0
% 4.05/0.98  inst_num_child_elim:                    0
% 4.05/0.98  inst_num_of_dismatching_blockings:      918
% 4.05/0.98  inst_num_of_non_proper_insts:           1857
% 4.05/0.98  inst_num_of_duplicates:                 0
% 4.05/0.98  inst_inst_num_from_inst_to_res:         0
% 4.05/0.98  inst_dismatching_checking_time:         0.
% 4.05/0.98  
% 4.05/0.98  ------ Resolution
% 4.05/0.98  
% 4.05/0.98  res_num_of_clauses:                     0
% 4.05/0.98  res_num_in_passive:                     0
% 4.05/0.98  res_num_in_active:                      0
% 4.05/0.98  res_num_of_loops:                       143
% 4.05/0.98  res_forward_subset_subsumed:            195
% 4.05/0.98  res_backward_subset_subsumed:           0
% 4.05/0.98  res_forward_subsumed:                   0
% 4.05/0.98  res_backward_subsumed:                  1
% 4.05/0.98  res_forward_subsumption_resolution:     0
% 4.05/0.98  res_backward_subsumption_resolution:    0
% 4.05/0.98  res_clause_to_clause_subsumption:       1831
% 4.05/0.98  res_orphan_elimination:                 0
% 4.05/0.98  res_tautology_del:                      113
% 4.05/0.98  res_num_eq_res_simplified:              1
% 4.05/0.98  res_num_sel_changes:                    0
% 4.05/0.98  res_moves_from_active_to_pass:          0
% 4.05/0.98  
% 4.05/0.98  ------ Superposition
% 4.05/0.98  
% 4.05/0.98  sup_time_total:                         0.
% 4.05/0.98  sup_time_generating:                    0.
% 4.05/0.98  sup_time_sim_full:                      0.
% 4.05/0.98  sup_time_sim_immed:                     0.
% 4.05/0.98  
% 4.05/0.98  sup_num_of_clauses:                     555
% 4.05/0.98  sup_num_in_active:                      136
% 4.05/0.98  sup_num_in_passive:                     419
% 4.05/0.98  sup_num_of_loops:                       145
% 4.05/0.98  sup_fw_superposition:                   385
% 4.05/0.98  sup_bw_superposition:                   463
% 4.05/0.98  sup_immediate_simplified:               263
% 4.05/0.98  sup_given_eliminated:                   0
% 4.05/0.98  comparisons_done:                       0
% 4.05/0.98  comparisons_avoided:                    181
% 4.05/0.98  
% 4.05/0.98  ------ Simplifications
% 4.05/0.98  
% 4.05/0.98  
% 4.05/0.98  sim_fw_subset_subsumed:                 44
% 4.05/0.98  sim_bw_subset_subsumed:                 43
% 4.05/0.98  sim_fw_subsumed:                        42
% 4.05/0.98  sim_bw_subsumed:                        9
% 4.05/0.98  sim_fw_subsumption_res:                 0
% 4.05/0.98  sim_bw_subsumption_res:                 0
% 4.05/0.98  sim_tautology_del:                      4
% 4.05/0.98  sim_eq_tautology_del:                   66
% 4.05/0.98  sim_eq_res_simp:                        0
% 4.05/0.98  sim_fw_demodulated:                     2
% 4.05/0.98  sim_bw_demodulated:                     2
% 4.05/0.98  sim_light_normalised:                   185
% 4.05/0.98  sim_joinable_taut:                      0
% 4.05/0.98  sim_joinable_simp:                      0
% 4.05/0.98  sim_ac_normalised:                      0
% 4.05/0.98  sim_smt_subsumption:                    0
% 4.05/0.98  
%------------------------------------------------------------------------------
