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
% DateTime   : Thu Dec  3 12:02:55 EST 2020

% Result     : Theorem 3.18s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 832 expanded)
%              Number of clauses        :   78 ( 214 expanded)
%              Number of leaves         :   12 ( 169 expanded)
%              Depth                    :   19
%              Number of atoms          :  408 (4750 expanded)
%              Number of equality atoms :  123 ( 314 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f16,plain,(
    ~ ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X3) )
               => ! [X4] :
                    ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                      & v1_funct_1(X4) )
                   => ( ( v2_funct_2(X4,X2)
                        & v2_funct_2(X3,X1) )
                     => v2_funct_2(k1_partfun1(X0,X1,X1,X2,X3,X4),X2) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f17,plain,(
    ~ ! [X1,X0,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_1(X4) )
           => ( ( v2_funct_2(X4,X2)
                & v2_funct_2(X3,X1) )
             => v2_funct_2(k1_partfun1(X0,X1,X1,X2,X3,X4),X2) ) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f34,plain,(
    ? [X1,X0,X2,X3] :
      ( ? [X4] :
          ( ~ v2_funct_2(k1_partfun1(X0,X1,X1,X2,X3,X4),X2)
          & v2_funct_2(X4,X2)
          & v2_funct_2(X3,X1)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f35,plain,(
    ? [X1,X0,X2,X3] :
      ( ? [X4] :
          ( ~ v2_funct_2(k1_partfun1(X0,X1,X1,X2,X3,X4),X2)
          & v2_funct_2(X4,X2)
          & v2_funct_2(X3,X1)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f34])).

fof(f37,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ~ v2_funct_2(k1_partfun1(X1,X0,X0,X2,X3,X4),X2)
          & v2_funct_2(X4,X2)
          & v2_funct_2(X3,X0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      & v1_funct_1(X3) ) ),
    inference(rectify,[],[f35])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ~ v2_funct_2(k1_partfun1(X1,X0,X0,X2,X3,X4),X2)
          & v2_funct_2(X4,X2)
          & v2_funct_2(X3,X0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          & v1_funct_1(X4) )
     => ( ~ v2_funct_2(k1_partfun1(X1,X0,X0,X2,X3,sK4),X2)
        & v2_funct_2(sK4,X2)
        & v2_funct_2(X3,X0)
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ~ v2_funct_2(k1_partfun1(X1,X0,X0,X2,X3,X4),X2)
            & v2_funct_2(X4,X2)
            & v2_funct_2(X3,X0)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ~ v2_funct_2(k1_partfun1(sK1,sK0,sK0,sK2,sK3,X4),sK2)
          & v2_funct_2(X4,sK2)
          & v2_funct_2(sK3,sK0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ~ v2_funct_2(k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4),sK2)
    & v2_funct_2(sK4,sK2)
    & v2_funct_2(sK3,sK0)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f37,f39,f38])).

fof(f58,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f60,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f40])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f32])).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f59,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f57,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f30])).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f64,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f53])).

fof(f63,plain,(
    ~ v2_funct_2(k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4),sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f61,plain,(
    v2_funct_2(sK3,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f62,plain,(
    v2_funct_2(sK4,sK2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_821,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_823,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_824,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2279,plain,
    ( k1_partfun1(X0,X1,sK0,sK2,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_823,c_824])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_25,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2908,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK0,sK2,X2,sK4) = k5_relat_1(X2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2279,c_25])).

cnf(c_2909,plain,
    ( k1_partfun1(X0,X1,sK0,sK2,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_2908])).

cnf(c_2918,plain,
    ( k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_821,c_2909])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1072,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK4)
    | k1_partfun1(X1,X2,X3,X4,X0,sK4) = k5_relat_1(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1259,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X2,X3,X0,X1,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1072])).

cnf(c_1584,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X0,X1,sK0,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1259])).

cnf(c_2540,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1584])).

cnf(c_3147,plain,
    ( k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2918,c_22,c_21,c_20,c_19,c_2540])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_826,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3433,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3147,c_826])).

cnf(c_23,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_24,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_26,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_6427,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3433,c_23,c_24,c_25,c_26])).

cnf(c_9,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_827,plain,
    ( v5_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_6435,plain,
    ( v5_relat_1(k5_relat_1(sK3,sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_6427,c_827])).

cnf(c_11,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_16,negated_conjecture,
    ( ~ v2_funct_2(k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4),sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_267,plain,
    ( ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0)
    | k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4) != X0
    | k2_relat_1(X0) != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_16])).

cnf(c_268,plain,
    ( ~ v5_relat_1(k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4),k2_relat_1(k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4)))
    | ~ v1_relat_1(k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4))
    | k2_relat_1(k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4)) != sK2 ),
    inference(unflattening,[status(thm)],[c_267])).

cnf(c_818,plain,
    ( k2_relat_1(k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4)) != sK2
    | v5_relat_1(k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4),k2_relat_1(k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4))) != iProver_top
    | v1_relat_1(k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_268])).

cnf(c_3150,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) != sK2
    | v5_relat_1(k5_relat_1(sK3,sK4),k2_relat_1(k5_relat_1(sK3,sK4))) != iProver_top
    | v1_relat_1(k5_relat_1(sK3,sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3147,c_818])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_998,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_999,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_998])).

cnf(c_1001,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1002,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1001])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1111,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k5_relat_1(X0,sK4))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1344,plain,
    ( v1_relat_1(k5_relat_1(sK3,sK4))
    | ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1111])).

cnf(c_1345,plain,
    ( v1_relat_1(k5_relat_1(sK3,sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1344])).

cnf(c_828,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1554,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_821,c_828])).

cnf(c_1553,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_823,c_828])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_829,plain,
    ( k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2681,plain,
    ( k9_relat_1(sK4,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,sK4))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1553,c_829])).

cnf(c_4830,plain,
    ( k9_relat_1(sK4,k2_relat_1(sK3)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_1554,c_2681])).

cnf(c_12,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_18,negated_conjecture,
    ( v2_funct_2(sK3,sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_293,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1
    | sK3 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_18])).

cnf(c_294,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) = sK0 ),
    inference(unflattening,[status(thm)],[c_293])).

cnf(c_816,plain,
    ( k2_relat_1(sK3) = sK0
    | v5_relat_1(sK3,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_294])).

cnf(c_1019,plain,
    ( v5_relat_1(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1179,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_816,c_21,c_294,c_1001,c_1019])).

cnf(c_10,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_7,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_245,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_10,c_7])).

cnf(c_249,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_245,c_10,c_8,c_7])).

cnf(c_819,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_249])).

cnf(c_2119,plain,
    ( k7_relat_1(sK4,sK0) = sK4 ),
    inference(superposition,[status(thm)],[c_823,c_819])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_830,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1620,plain,
    ( k2_relat_1(k7_relat_1(sK4,X0)) = k9_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_1553,c_830])).

cnf(c_2271,plain,
    ( k9_relat_1(sK4,sK0) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2119,c_1620])).

cnf(c_17,negated_conjecture,
    ( v2_funct_2(sK4,sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_280,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1
    | sK4 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_17])).

cnf(c_281,plain,
    ( ~ v5_relat_1(sK4,sK2)
    | ~ v1_relat_1(sK4)
    | k2_relat_1(sK4) = sK2 ),
    inference(unflattening,[status(thm)],[c_280])).

cnf(c_817,plain,
    ( k2_relat_1(sK4) = sK2
    | v5_relat_1(sK4,sK2) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_281])).

cnf(c_1016,plain,
    ( v5_relat_1(sK4,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1183,plain,
    ( k2_relat_1(sK4) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_817,c_19,c_281,c_998,c_1016])).

cnf(c_2272,plain,
    ( k9_relat_1(sK4,sK0) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_2271,c_1183])).

cnf(c_4832,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_4830,c_1179,c_2272])).

cnf(c_6116,plain,
    ( v5_relat_1(k5_relat_1(sK3,sK4),k2_relat_1(k5_relat_1(sK3,sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3150,c_24,c_26,c_999,c_1002,c_1345,c_4832])).

cnf(c_6120,plain,
    ( v5_relat_1(k5_relat_1(sK3,sK4),sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6116,c_4832])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6435,c_6120])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:37:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.18/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/0.99  
% 3.18/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.18/0.99  
% 3.18/0.99  ------  iProver source info
% 3.18/0.99  
% 3.18/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.18/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.18/0.99  git: non_committed_changes: false
% 3.18/0.99  git: last_make_outside_of_git: false
% 3.18/0.99  
% 3.18/0.99  ------ 
% 3.18/0.99  
% 3.18/0.99  ------ Input Options
% 3.18/0.99  
% 3.18/0.99  --out_options                           all
% 3.18/0.99  --tptp_safe_out                         true
% 3.18/0.99  --problem_path                          ""
% 3.18/0.99  --include_path                          ""
% 3.18/0.99  --clausifier                            res/vclausify_rel
% 3.18/0.99  --clausifier_options                    --mode clausify
% 3.18/0.99  --stdin                                 false
% 3.18/0.99  --stats_out                             all
% 3.18/0.99  
% 3.18/0.99  ------ General Options
% 3.18/0.99  
% 3.18/0.99  --fof                                   false
% 3.18/0.99  --time_out_real                         305.
% 3.18/0.99  --time_out_virtual                      -1.
% 3.18/0.99  --symbol_type_check                     false
% 3.18/0.99  --clausify_out                          false
% 3.18/0.99  --sig_cnt_out                           false
% 3.18/0.99  --trig_cnt_out                          false
% 3.18/0.99  --trig_cnt_out_tolerance                1.
% 3.18/0.99  --trig_cnt_out_sk_spl                   false
% 3.18/0.99  --abstr_cl_out                          false
% 3.18/0.99  
% 3.18/0.99  ------ Global Options
% 3.18/0.99  
% 3.18/0.99  --schedule                              default
% 3.18/0.99  --add_important_lit                     false
% 3.18/0.99  --prop_solver_per_cl                    1000
% 3.18/0.99  --min_unsat_core                        false
% 3.18/0.99  --soft_assumptions                      false
% 3.18/0.99  --soft_lemma_size                       3
% 3.18/0.99  --prop_impl_unit_size                   0
% 3.18/0.99  --prop_impl_unit                        []
% 3.18/0.99  --share_sel_clauses                     true
% 3.18/0.99  --reset_solvers                         false
% 3.18/0.99  --bc_imp_inh                            [conj_cone]
% 3.18/0.99  --conj_cone_tolerance                   3.
% 3.18/0.99  --extra_neg_conj                        none
% 3.18/0.99  --large_theory_mode                     true
% 3.18/0.99  --prolific_symb_bound                   200
% 3.18/0.99  --lt_threshold                          2000
% 3.18/0.99  --clause_weak_htbl                      true
% 3.18/0.99  --gc_record_bc_elim                     false
% 3.18/0.99  
% 3.18/0.99  ------ Preprocessing Options
% 3.18/0.99  
% 3.18/0.99  --preprocessing_flag                    true
% 3.18/0.99  --time_out_prep_mult                    0.1
% 3.18/0.99  --splitting_mode                        input
% 3.18/0.99  --splitting_grd                         true
% 3.18/0.99  --splitting_cvd                         false
% 3.18/0.99  --splitting_cvd_svl                     false
% 3.18/0.99  --splitting_nvd                         32
% 3.18/0.99  --sub_typing                            true
% 3.18/0.99  --prep_gs_sim                           true
% 3.18/0.99  --prep_unflatten                        true
% 3.18/0.99  --prep_res_sim                          true
% 3.18/0.99  --prep_upred                            true
% 3.18/0.99  --prep_sem_filter                       exhaustive
% 3.18/0.99  --prep_sem_filter_out                   false
% 3.18/0.99  --pred_elim                             true
% 3.18/0.99  --res_sim_input                         true
% 3.18/0.99  --eq_ax_congr_red                       true
% 3.18/0.99  --pure_diseq_elim                       true
% 3.18/0.99  --brand_transform                       false
% 3.18/0.99  --non_eq_to_eq                          false
% 3.18/0.99  --prep_def_merge                        true
% 3.18/0.99  --prep_def_merge_prop_impl              false
% 3.18/0.99  --prep_def_merge_mbd                    true
% 3.18/0.99  --prep_def_merge_tr_red                 false
% 3.18/0.99  --prep_def_merge_tr_cl                  false
% 3.18/0.99  --smt_preprocessing                     true
% 3.18/0.99  --smt_ac_axioms                         fast
% 3.18/0.99  --preprocessed_out                      false
% 3.18/0.99  --preprocessed_stats                    false
% 3.18/0.99  
% 3.18/0.99  ------ Abstraction refinement Options
% 3.18/0.99  
% 3.18/0.99  --abstr_ref                             []
% 3.18/0.99  --abstr_ref_prep                        false
% 3.18/0.99  --abstr_ref_until_sat                   false
% 3.18/0.99  --abstr_ref_sig_restrict                funpre
% 3.18/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.18/0.99  --abstr_ref_under                       []
% 3.18/0.99  
% 3.18/0.99  ------ SAT Options
% 3.18/0.99  
% 3.18/0.99  --sat_mode                              false
% 3.18/0.99  --sat_fm_restart_options                ""
% 3.18/0.99  --sat_gr_def                            false
% 3.18/0.99  --sat_epr_types                         true
% 3.18/0.99  --sat_non_cyclic_types                  false
% 3.18/0.99  --sat_finite_models                     false
% 3.18/0.99  --sat_fm_lemmas                         false
% 3.18/0.99  --sat_fm_prep                           false
% 3.18/0.99  --sat_fm_uc_incr                        true
% 3.18/0.99  --sat_out_model                         small
% 3.18/0.99  --sat_out_clauses                       false
% 3.18/0.99  
% 3.18/0.99  ------ QBF Options
% 3.18/0.99  
% 3.18/0.99  --qbf_mode                              false
% 3.18/0.99  --qbf_elim_univ                         false
% 3.18/0.99  --qbf_dom_inst                          none
% 3.18/0.99  --qbf_dom_pre_inst                      false
% 3.18/0.99  --qbf_sk_in                             false
% 3.18/0.99  --qbf_pred_elim                         true
% 3.18/0.99  --qbf_split                             512
% 3.18/0.99  
% 3.18/0.99  ------ BMC1 Options
% 3.18/0.99  
% 3.18/0.99  --bmc1_incremental                      false
% 3.18/0.99  --bmc1_axioms                           reachable_all
% 3.18/0.99  --bmc1_min_bound                        0
% 3.18/0.99  --bmc1_max_bound                        -1
% 3.18/0.99  --bmc1_max_bound_default                -1
% 3.18/0.99  --bmc1_symbol_reachability              true
% 3.18/0.99  --bmc1_property_lemmas                  false
% 3.18/0.99  --bmc1_k_induction                      false
% 3.18/0.99  --bmc1_non_equiv_states                 false
% 3.18/0.99  --bmc1_deadlock                         false
% 3.18/0.99  --bmc1_ucm                              false
% 3.18/0.99  --bmc1_add_unsat_core                   none
% 3.18/0.99  --bmc1_unsat_core_children              false
% 3.18/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.18/0.99  --bmc1_out_stat                         full
% 3.18/0.99  --bmc1_ground_init                      false
% 3.18/0.99  --bmc1_pre_inst_next_state              false
% 3.18/0.99  --bmc1_pre_inst_state                   false
% 3.18/0.99  --bmc1_pre_inst_reach_state             false
% 3.18/0.99  --bmc1_out_unsat_core                   false
% 3.18/0.99  --bmc1_aig_witness_out                  false
% 3.18/0.99  --bmc1_verbose                          false
% 3.18/0.99  --bmc1_dump_clauses_tptp                false
% 3.18/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.18/0.99  --bmc1_dump_file                        -
% 3.18/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.18/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.18/0.99  --bmc1_ucm_extend_mode                  1
% 3.18/0.99  --bmc1_ucm_init_mode                    2
% 3.18/0.99  --bmc1_ucm_cone_mode                    none
% 3.18/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.18/0.99  --bmc1_ucm_relax_model                  4
% 3.18/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.18/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.18/0.99  --bmc1_ucm_layered_model                none
% 3.18/0.99  --bmc1_ucm_max_lemma_size               10
% 3.18/0.99  
% 3.18/0.99  ------ AIG Options
% 3.18/0.99  
% 3.18/0.99  --aig_mode                              false
% 3.18/0.99  
% 3.18/0.99  ------ Instantiation Options
% 3.18/0.99  
% 3.18/0.99  --instantiation_flag                    true
% 3.18/0.99  --inst_sos_flag                         false
% 3.18/0.99  --inst_sos_phase                        true
% 3.18/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.18/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.18/0.99  --inst_lit_sel_side                     num_symb
% 3.18/0.99  --inst_solver_per_active                1400
% 3.18/0.99  --inst_solver_calls_frac                1.
% 3.18/0.99  --inst_passive_queue_type               priority_queues
% 3.18/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.18/0.99  --inst_passive_queues_freq              [25;2]
% 3.18/0.99  --inst_dismatching                      true
% 3.18/0.99  --inst_eager_unprocessed_to_passive     true
% 3.18/0.99  --inst_prop_sim_given                   true
% 3.18/0.99  --inst_prop_sim_new                     false
% 3.18/0.99  --inst_subs_new                         false
% 3.18/0.99  --inst_eq_res_simp                      false
% 3.18/0.99  --inst_subs_given                       false
% 3.18/0.99  --inst_orphan_elimination               true
% 3.18/0.99  --inst_learning_loop_flag               true
% 3.18/0.99  --inst_learning_start                   3000
% 3.18/0.99  --inst_learning_factor                  2
% 3.18/0.99  --inst_start_prop_sim_after_learn       3
% 3.18/0.99  --inst_sel_renew                        solver
% 3.18/0.99  --inst_lit_activity_flag                true
% 3.18/0.99  --inst_restr_to_given                   false
% 3.18/0.99  --inst_activity_threshold               500
% 3.18/0.99  --inst_out_proof                        true
% 3.18/0.99  
% 3.18/0.99  ------ Resolution Options
% 3.18/0.99  
% 3.18/0.99  --resolution_flag                       true
% 3.18/0.99  --res_lit_sel                           adaptive
% 3.18/0.99  --res_lit_sel_side                      none
% 3.18/0.99  --res_ordering                          kbo
% 3.18/0.99  --res_to_prop_solver                    active
% 3.18/0.99  --res_prop_simpl_new                    false
% 3.18/0.99  --res_prop_simpl_given                  true
% 3.18/0.99  --res_passive_queue_type                priority_queues
% 3.18/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.18/0.99  --res_passive_queues_freq               [15;5]
% 3.18/0.99  --res_forward_subs                      full
% 3.18/0.99  --res_backward_subs                     full
% 3.18/0.99  --res_forward_subs_resolution           true
% 3.18/0.99  --res_backward_subs_resolution          true
% 3.18/0.99  --res_orphan_elimination                true
% 3.18/0.99  --res_time_limit                        2.
% 3.18/0.99  --res_out_proof                         true
% 3.18/0.99  
% 3.18/0.99  ------ Superposition Options
% 3.18/0.99  
% 3.18/0.99  --superposition_flag                    true
% 3.18/0.99  --sup_passive_queue_type                priority_queues
% 3.18/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.18/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.18/0.99  --demod_completeness_check              fast
% 3.18/0.99  --demod_use_ground                      true
% 3.18/0.99  --sup_to_prop_solver                    passive
% 3.18/0.99  --sup_prop_simpl_new                    true
% 3.18/0.99  --sup_prop_simpl_given                  true
% 3.18/0.99  --sup_fun_splitting                     false
% 3.18/0.99  --sup_smt_interval                      50000
% 3.18/0.99  
% 3.18/0.99  ------ Superposition Simplification Setup
% 3.18/0.99  
% 3.18/0.99  --sup_indices_passive                   []
% 3.18/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.18/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.99  --sup_full_bw                           [BwDemod]
% 3.18/0.99  --sup_immed_triv                        [TrivRules]
% 3.18/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.18/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.99  --sup_immed_bw_main                     []
% 3.18/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.18/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/0.99  
% 3.18/0.99  ------ Combination Options
% 3.18/0.99  
% 3.18/0.99  --comb_res_mult                         3
% 3.18/0.99  --comb_sup_mult                         2
% 3.18/0.99  --comb_inst_mult                        10
% 3.18/0.99  
% 3.18/0.99  ------ Debug Options
% 3.18/0.99  
% 3.18/0.99  --dbg_backtrace                         false
% 3.18/0.99  --dbg_dump_prop_clauses                 false
% 3.18/0.99  --dbg_dump_prop_clauses_file            -
% 3.18/0.99  --dbg_out_stat                          false
% 3.18/0.99  ------ Parsing...
% 3.18/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.18/0.99  
% 3.18/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.18/0.99  
% 3.18/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.18/0.99  
% 3.18/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.18/0.99  ------ Proving...
% 3.18/0.99  ------ Problem Properties 
% 3.18/0.99  
% 3.18/0.99  
% 3.18/0.99  clauses                                 22
% 3.18/0.99  conjectures                             4
% 3.18/0.99  EPR                                     2
% 3.18/0.99  Horn                                    22
% 3.18/0.99  unary                                   8
% 3.18/0.99  binary                                  5
% 3.18/0.99  lits                                    52
% 3.18/0.99  lits eq                                 11
% 3.18/0.99  fd_pure                                 0
% 3.18/0.99  fd_pseudo                               0
% 3.18/0.99  fd_cond                                 0
% 3.18/0.99  fd_pseudo_cond                          0
% 3.18/0.99  AC symbols                              0
% 3.18/0.99  
% 3.18/0.99  ------ Schedule dynamic 5 is on 
% 3.18/0.99  
% 3.18/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.18/0.99  
% 3.18/0.99  
% 3.18/0.99  ------ 
% 3.18/0.99  Current options:
% 3.18/0.99  ------ 
% 3.18/0.99  
% 3.18/0.99  ------ Input Options
% 3.18/0.99  
% 3.18/0.99  --out_options                           all
% 3.18/0.99  --tptp_safe_out                         true
% 3.18/0.99  --problem_path                          ""
% 3.18/0.99  --include_path                          ""
% 3.18/0.99  --clausifier                            res/vclausify_rel
% 3.18/0.99  --clausifier_options                    --mode clausify
% 3.18/0.99  --stdin                                 false
% 3.18/0.99  --stats_out                             all
% 3.18/0.99  
% 3.18/0.99  ------ General Options
% 3.18/0.99  
% 3.18/0.99  --fof                                   false
% 3.18/0.99  --time_out_real                         305.
% 3.18/0.99  --time_out_virtual                      -1.
% 3.18/0.99  --symbol_type_check                     false
% 3.18/0.99  --clausify_out                          false
% 3.18/0.99  --sig_cnt_out                           false
% 3.18/0.99  --trig_cnt_out                          false
% 3.18/0.99  --trig_cnt_out_tolerance                1.
% 3.18/0.99  --trig_cnt_out_sk_spl                   false
% 3.18/0.99  --abstr_cl_out                          false
% 3.18/0.99  
% 3.18/0.99  ------ Global Options
% 3.18/0.99  
% 3.18/0.99  --schedule                              default
% 3.18/0.99  --add_important_lit                     false
% 3.18/0.99  --prop_solver_per_cl                    1000
% 3.18/0.99  --min_unsat_core                        false
% 3.18/0.99  --soft_assumptions                      false
% 3.18/0.99  --soft_lemma_size                       3
% 3.18/0.99  --prop_impl_unit_size                   0
% 3.18/0.99  --prop_impl_unit                        []
% 3.18/0.99  --share_sel_clauses                     true
% 3.18/0.99  --reset_solvers                         false
% 3.18/0.99  --bc_imp_inh                            [conj_cone]
% 3.18/0.99  --conj_cone_tolerance                   3.
% 3.18/0.99  --extra_neg_conj                        none
% 3.18/0.99  --large_theory_mode                     true
% 3.18/0.99  --prolific_symb_bound                   200
% 3.18/0.99  --lt_threshold                          2000
% 3.18/0.99  --clause_weak_htbl                      true
% 3.18/0.99  --gc_record_bc_elim                     false
% 3.18/0.99  
% 3.18/0.99  ------ Preprocessing Options
% 3.18/0.99  
% 3.18/0.99  --preprocessing_flag                    true
% 3.18/0.99  --time_out_prep_mult                    0.1
% 3.18/0.99  --splitting_mode                        input
% 3.18/0.99  --splitting_grd                         true
% 3.18/0.99  --splitting_cvd                         false
% 3.18/0.99  --splitting_cvd_svl                     false
% 3.18/0.99  --splitting_nvd                         32
% 3.18/0.99  --sub_typing                            true
% 3.18/0.99  --prep_gs_sim                           true
% 3.18/0.99  --prep_unflatten                        true
% 3.18/0.99  --prep_res_sim                          true
% 3.18/0.99  --prep_upred                            true
% 3.18/0.99  --prep_sem_filter                       exhaustive
% 3.18/0.99  --prep_sem_filter_out                   false
% 3.18/0.99  --pred_elim                             true
% 3.18/0.99  --res_sim_input                         true
% 3.18/0.99  --eq_ax_congr_red                       true
% 3.18/0.99  --pure_diseq_elim                       true
% 3.18/0.99  --brand_transform                       false
% 3.18/0.99  --non_eq_to_eq                          false
% 3.18/0.99  --prep_def_merge                        true
% 3.18/0.99  --prep_def_merge_prop_impl              false
% 3.18/0.99  --prep_def_merge_mbd                    true
% 3.18/0.99  --prep_def_merge_tr_red                 false
% 3.18/0.99  --prep_def_merge_tr_cl                  false
% 3.18/0.99  --smt_preprocessing                     true
% 3.18/0.99  --smt_ac_axioms                         fast
% 3.18/0.99  --preprocessed_out                      false
% 3.18/0.99  --preprocessed_stats                    false
% 3.18/0.99  
% 3.18/0.99  ------ Abstraction refinement Options
% 3.18/0.99  
% 3.18/0.99  --abstr_ref                             []
% 3.18/0.99  --abstr_ref_prep                        false
% 3.18/0.99  --abstr_ref_until_sat                   false
% 3.18/0.99  --abstr_ref_sig_restrict                funpre
% 3.18/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.18/0.99  --abstr_ref_under                       []
% 3.18/0.99  
% 3.18/0.99  ------ SAT Options
% 3.18/0.99  
% 3.18/0.99  --sat_mode                              false
% 3.18/0.99  --sat_fm_restart_options                ""
% 3.18/0.99  --sat_gr_def                            false
% 3.18/0.99  --sat_epr_types                         true
% 3.18/0.99  --sat_non_cyclic_types                  false
% 3.18/0.99  --sat_finite_models                     false
% 3.18/0.99  --sat_fm_lemmas                         false
% 3.18/0.99  --sat_fm_prep                           false
% 3.18/0.99  --sat_fm_uc_incr                        true
% 3.18/0.99  --sat_out_model                         small
% 3.18/0.99  --sat_out_clauses                       false
% 3.18/0.99  
% 3.18/0.99  ------ QBF Options
% 3.18/0.99  
% 3.18/0.99  --qbf_mode                              false
% 3.18/0.99  --qbf_elim_univ                         false
% 3.18/0.99  --qbf_dom_inst                          none
% 3.18/0.99  --qbf_dom_pre_inst                      false
% 3.18/0.99  --qbf_sk_in                             false
% 3.18/0.99  --qbf_pred_elim                         true
% 3.18/0.99  --qbf_split                             512
% 3.18/0.99  
% 3.18/0.99  ------ BMC1 Options
% 3.18/0.99  
% 3.18/0.99  --bmc1_incremental                      false
% 3.18/0.99  --bmc1_axioms                           reachable_all
% 3.18/0.99  --bmc1_min_bound                        0
% 3.18/0.99  --bmc1_max_bound                        -1
% 3.18/0.99  --bmc1_max_bound_default                -1
% 3.18/0.99  --bmc1_symbol_reachability              true
% 3.18/0.99  --bmc1_property_lemmas                  false
% 3.18/0.99  --bmc1_k_induction                      false
% 3.18/0.99  --bmc1_non_equiv_states                 false
% 3.18/0.99  --bmc1_deadlock                         false
% 3.18/0.99  --bmc1_ucm                              false
% 3.18/0.99  --bmc1_add_unsat_core                   none
% 3.18/0.99  --bmc1_unsat_core_children              false
% 3.18/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.18/0.99  --bmc1_out_stat                         full
% 3.18/0.99  --bmc1_ground_init                      false
% 3.18/0.99  --bmc1_pre_inst_next_state              false
% 3.18/0.99  --bmc1_pre_inst_state                   false
% 3.18/0.99  --bmc1_pre_inst_reach_state             false
% 3.18/0.99  --bmc1_out_unsat_core                   false
% 3.18/0.99  --bmc1_aig_witness_out                  false
% 3.18/0.99  --bmc1_verbose                          false
% 3.18/0.99  --bmc1_dump_clauses_tptp                false
% 3.18/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.18/0.99  --bmc1_dump_file                        -
% 3.18/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.18/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.18/0.99  --bmc1_ucm_extend_mode                  1
% 3.18/0.99  --bmc1_ucm_init_mode                    2
% 3.18/0.99  --bmc1_ucm_cone_mode                    none
% 3.18/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.18/0.99  --bmc1_ucm_relax_model                  4
% 3.18/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.18/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.18/0.99  --bmc1_ucm_layered_model                none
% 3.18/0.99  --bmc1_ucm_max_lemma_size               10
% 3.18/0.99  
% 3.18/0.99  ------ AIG Options
% 3.18/0.99  
% 3.18/0.99  --aig_mode                              false
% 3.18/0.99  
% 3.18/0.99  ------ Instantiation Options
% 3.18/0.99  
% 3.18/0.99  --instantiation_flag                    true
% 3.18/0.99  --inst_sos_flag                         false
% 3.18/0.99  --inst_sos_phase                        true
% 3.18/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.18/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.18/0.99  --inst_lit_sel_side                     none
% 3.18/0.99  --inst_solver_per_active                1400
% 3.18/0.99  --inst_solver_calls_frac                1.
% 3.18/0.99  --inst_passive_queue_type               priority_queues
% 3.18/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.18/0.99  --inst_passive_queues_freq              [25;2]
% 3.18/0.99  --inst_dismatching                      true
% 3.18/0.99  --inst_eager_unprocessed_to_passive     true
% 3.18/0.99  --inst_prop_sim_given                   true
% 3.18/0.99  --inst_prop_sim_new                     false
% 3.18/0.99  --inst_subs_new                         false
% 3.18/0.99  --inst_eq_res_simp                      false
% 3.18/0.99  --inst_subs_given                       false
% 3.18/0.99  --inst_orphan_elimination               true
% 3.18/0.99  --inst_learning_loop_flag               true
% 3.18/0.99  --inst_learning_start                   3000
% 3.18/0.99  --inst_learning_factor                  2
% 3.18/0.99  --inst_start_prop_sim_after_learn       3
% 3.18/0.99  --inst_sel_renew                        solver
% 3.18/0.99  --inst_lit_activity_flag                true
% 3.18/0.99  --inst_restr_to_given                   false
% 3.18/0.99  --inst_activity_threshold               500
% 3.18/0.99  --inst_out_proof                        true
% 3.18/0.99  
% 3.18/0.99  ------ Resolution Options
% 3.18/0.99  
% 3.18/0.99  --resolution_flag                       false
% 3.18/0.99  --res_lit_sel                           adaptive
% 3.18/0.99  --res_lit_sel_side                      none
% 3.18/0.99  --res_ordering                          kbo
% 3.18/0.99  --res_to_prop_solver                    active
% 3.18/0.99  --res_prop_simpl_new                    false
% 3.18/0.99  --res_prop_simpl_given                  true
% 3.18/0.99  --res_passive_queue_type                priority_queues
% 3.18/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.18/0.99  --res_passive_queues_freq               [15;5]
% 3.18/0.99  --res_forward_subs                      full
% 3.18/0.99  --res_backward_subs                     full
% 3.18/0.99  --res_forward_subs_resolution           true
% 3.18/0.99  --res_backward_subs_resolution          true
% 3.18/0.99  --res_orphan_elimination                true
% 3.18/0.99  --res_time_limit                        2.
% 3.18/0.99  --res_out_proof                         true
% 3.18/0.99  
% 3.18/0.99  ------ Superposition Options
% 3.18/0.99  
% 3.18/0.99  --superposition_flag                    true
% 3.18/0.99  --sup_passive_queue_type                priority_queues
% 3.18/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.18/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.18/0.99  --demod_completeness_check              fast
% 3.18/0.99  --demod_use_ground                      true
% 3.18/0.99  --sup_to_prop_solver                    passive
% 3.18/0.99  --sup_prop_simpl_new                    true
% 3.18/0.99  --sup_prop_simpl_given                  true
% 3.18/0.99  --sup_fun_splitting                     false
% 3.18/0.99  --sup_smt_interval                      50000
% 3.18/0.99  
% 3.18/0.99  ------ Superposition Simplification Setup
% 3.18/0.99  
% 3.18/0.99  --sup_indices_passive                   []
% 3.18/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.18/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.99  --sup_full_bw                           [BwDemod]
% 3.18/0.99  --sup_immed_triv                        [TrivRules]
% 3.18/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.18/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.99  --sup_immed_bw_main                     []
% 3.18/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.18/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/0.99  
% 3.18/0.99  ------ Combination Options
% 3.18/0.99  
% 3.18/0.99  --comb_res_mult                         3
% 3.18/0.99  --comb_sup_mult                         2
% 3.18/0.99  --comb_inst_mult                        10
% 3.18/0.99  
% 3.18/0.99  ------ Debug Options
% 3.18/0.99  
% 3.18/0.99  --dbg_backtrace                         false
% 3.18/0.99  --dbg_dump_prop_clauses                 false
% 3.18/0.99  --dbg_dump_prop_clauses_file            -
% 3.18/0.99  --dbg_out_stat                          false
% 3.18/0.99  
% 3.18/0.99  
% 3.18/0.99  
% 3.18/0.99  
% 3.18/0.99  ------ Proving...
% 3.18/0.99  
% 3.18/0.99  
% 3.18/0.99  % SZS status Theorem for theBenchmark.p
% 3.18/0.99  
% 3.18/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.18/0.99  
% 3.18/0.99  fof(f14,conjecture,(
% 3.18/0.99    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_2(X4,X2) & v2_funct_2(X3,X1)) => v2_funct_2(k1_partfun1(X0,X1,X1,X2,X3,X4),X2))))))),
% 3.18/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f15,negated_conjecture,(
% 3.18/0.99    ~! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_2(X4,X2) & v2_funct_2(X3,X1)) => v2_funct_2(k1_partfun1(X0,X1,X1,X2,X3,X4),X2))))))),
% 3.18/0.99    inference(negated_conjecture,[],[f14])).
% 3.18/0.99  
% 3.18/0.99  fof(f16,plain,(
% 3.18/0.99    ~! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4)) => ((v2_funct_2(X4,X2) & v2_funct_2(X3,X1)) => v2_funct_2(k1_partfun1(X0,X1,X1,X2,X3,X4),X2))))))),
% 3.18/0.99    inference(pure_predicate_removal,[],[f15])).
% 3.18/0.99  
% 3.18/0.99  fof(f17,plain,(
% 3.18/0.99    ~! [X1,X0,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4)) => ((v2_funct_2(X4,X2) & v2_funct_2(X3,X1)) => v2_funct_2(k1_partfun1(X0,X1,X1,X2,X3,X4),X2))))),
% 3.18/0.99    inference(pure_predicate_removal,[],[f16])).
% 3.18/0.99  
% 3.18/0.99  fof(f34,plain,(
% 3.18/0.99    ? [X1,X0,X2,X3] : (? [X4] : ((~v2_funct_2(k1_partfun1(X0,X1,X1,X2,X3,X4),X2) & (v2_funct_2(X4,X2) & v2_funct_2(X3,X1))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 3.18/0.99    inference(ennf_transformation,[],[f17])).
% 3.18/0.99  
% 3.18/0.99  fof(f35,plain,(
% 3.18/0.99    ? [X1,X0,X2,X3] : (? [X4] : (~v2_funct_2(k1_partfun1(X0,X1,X1,X2,X3,X4),X2) & v2_funct_2(X4,X2) & v2_funct_2(X3,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 3.18/0.99    inference(flattening,[],[f34])).
% 3.18/0.99  
% 3.18/0.99  fof(f37,plain,(
% 3.18/0.99    ? [X0,X1,X2,X3] : (? [X4] : (~v2_funct_2(k1_partfun1(X1,X0,X0,X2,X3,X4),X2) & v2_funct_2(X4,X2) & v2_funct_2(X3,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3))),
% 3.18/0.99    inference(rectify,[],[f35])).
% 3.18/0.99  
% 3.18/0.99  fof(f39,plain,(
% 3.18/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (~v2_funct_2(k1_partfun1(X1,X0,X0,X2,X3,X4),X2) & v2_funct_2(X4,X2) & v2_funct_2(X3,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => (~v2_funct_2(k1_partfun1(X1,X0,X0,X2,X3,sK4),X2) & v2_funct_2(sK4,X2) & v2_funct_2(X3,X0) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(sK4))) )),
% 3.18/0.99    introduced(choice_axiom,[])).
% 3.18/0.99  
% 3.18/0.99  fof(f38,plain,(
% 3.18/0.99    ? [X0,X1,X2,X3] : (? [X4] : (~v2_funct_2(k1_partfun1(X1,X0,X0,X2,X3,X4),X2) & v2_funct_2(X4,X2) & v2_funct_2(X3,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) => (? [X4] : (~v2_funct_2(k1_partfun1(sK1,sK0,sK0,sK2,sK3,X4),sK2) & v2_funct_2(X4,sK2) & v2_funct_2(sK3,sK0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(sK3))),
% 3.18/0.99    introduced(choice_axiom,[])).
% 3.18/0.99  
% 3.18/0.99  fof(f40,plain,(
% 3.18/0.99    (~v2_funct_2(k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4),sK2) & v2_funct_2(sK4,sK2) & v2_funct_2(sK3,sK0) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(sK3)),
% 3.18/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f37,f39,f38])).
% 3.18/0.99  
% 3.18/0.99  fof(f58,plain,(
% 3.18/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.18/0.99    inference(cnf_transformation,[],[f40])).
% 3.18/0.99  
% 3.18/0.99  fof(f60,plain,(
% 3.18/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 3.18/0.99    inference(cnf_transformation,[],[f40])).
% 3.18/0.99  
% 3.18/0.99  fof(f13,axiom,(
% 3.18/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.18/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f32,plain,(
% 3.18/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.18/0.99    inference(ennf_transformation,[],[f13])).
% 3.18/0.99  
% 3.18/0.99  fof(f33,plain,(
% 3.18/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.18/0.99    inference(flattening,[],[f32])).
% 3.18/0.99  
% 3.18/0.99  fof(f56,plain,(
% 3.18/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f33])).
% 3.18/0.99  
% 3.18/0.99  fof(f59,plain,(
% 3.18/0.99    v1_funct_1(sK4)),
% 3.18/0.99    inference(cnf_transformation,[],[f40])).
% 3.18/0.99  
% 3.18/0.99  fof(f57,plain,(
% 3.18/0.99    v1_funct_1(sK3)),
% 3.18/0.99    inference(cnf_transformation,[],[f40])).
% 3.18/0.99  
% 3.18/0.99  fof(f12,axiom,(
% 3.18/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.18/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f30,plain,(
% 3.18/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.18/0.99    inference(ennf_transformation,[],[f12])).
% 3.18/0.99  
% 3.18/0.99  fof(f31,plain,(
% 3.18/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.18/0.99    inference(flattening,[],[f30])).
% 3.18/0.99  
% 3.18/0.99  fof(f55,plain,(
% 3.18/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f31])).
% 3.18/0.99  
% 3.18/0.99  fof(f10,axiom,(
% 3.18/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.18/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f27,plain,(
% 3.18/0.99    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.18/0.99    inference(ennf_transformation,[],[f10])).
% 3.18/0.99  
% 3.18/0.99  fof(f51,plain,(
% 3.18/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.18/0.99    inference(cnf_transformation,[],[f27])).
% 3.18/0.99  
% 3.18/0.99  fof(f11,axiom,(
% 3.18/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.18/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f28,plain,(
% 3.18/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.18/0.99    inference(ennf_transformation,[],[f11])).
% 3.18/0.99  
% 3.18/0.99  fof(f29,plain,(
% 3.18/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.18/0.99    inference(flattening,[],[f28])).
% 3.18/0.99  
% 3.18/0.99  fof(f36,plain,(
% 3.18/0.99    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.18/0.99    inference(nnf_transformation,[],[f29])).
% 3.18/0.99  
% 3.18/0.99  fof(f53,plain,(
% 3.18/0.99    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f36])).
% 3.18/0.99  
% 3.18/0.99  fof(f64,plain,(
% 3.18/0.99    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.18/0.99    inference(equality_resolution,[],[f53])).
% 3.18/0.99  
% 3.18/0.99  fof(f63,plain,(
% 3.18/0.99    ~v2_funct_2(k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4),sK2)),
% 3.18/0.99    inference(cnf_transformation,[],[f40])).
% 3.18/0.99  
% 3.18/0.99  fof(f9,axiom,(
% 3.18/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.18/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f26,plain,(
% 3.18/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.18/0.99    inference(ennf_transformation,[],[f9])).
% 3.18/0.99  
% 3.18/0.99  fof(f49,plain,(
% 3.18/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.18/0.99    inference(cnf_transformation,[],[f26])).
% 3.18/0.99  
% 3.18/0.99  fof(f4,axiom,(
% 3.18/0.99    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 3.18/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f20,plain,(
% 3.18/0.99    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 3.18/0.99    inference(ennf_transformation,[],[f4])).
% 3.18/0.99  
% 3.18/0.99  fof(f21,plain,(
% 3.18/0.99    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 3.18/0.99    inference(flattening,[],[f20])).
% 3.18/0.99  
% 3.18/0.99  fof(f44,plain,(
% 3.18/0.99    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f21])).
% 3.18/0.99  
% 3.18/0.99  fof(f7,axiom,(
% 3.18/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 3.18/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f23,plain,(
% 3.18/0.99    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.18/0.99    inference(ennf_transformation,[],[f7])).
% 3.18/0.99  
% 3.18/0.99  fof(f47,plain,(
% 3.18/0.99    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f23])).
% 3.18/0.99  
% 3.18/0.99  fof(f52,plain,(
% 3.18/0.99    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f36])).
% 3.18/0.99  
% 3.18/0.99  fof(f61,plain,(
% 3.18/0.99    v2_funct_2(sK3,sK0)),
% 3.18/0.99    inference(cnf_transformation,[],[f40])).
% 3.18/0.99  
% 3.18/0.99  fof(f50,plain,(
% 3.18/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.18/0.99    inference(cnf_transformation,[],[f27])).
% 3.18/0.99  
% 3.18/0.99  fof(f8,axiom,(
% 3.18/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 3.18/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f24,plain,(
% 3.18/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.18/0.99    inference(ennf_transformation,[],[f8])).
% 3.18/0.99  
% 3.18/0.99  fof(f25,plain,(
% 3.18/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.18/0.99    inference(flattening,[],[f24])).
% 3.18/0.99  
% 3.18/0.99  fof(f48,plain,(
% 3.18/0.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f25])).
% 3.18/0.99  
% 3.18/0.99  fof(f6,axiom,(
% 3.18/0.99    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 3.18/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f22,plain,(
% 3.18/0.99    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.18/0.99    inference(ennf_transformation,[],[f6])).
% 3.18/0.99  
% 3.18/0.99  fof(f46,plain,(
% 3.18/0.99    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f22])).
% 3.18/0.99  
% 3.18/0.99  fof(f62,plain,(
% 3.18/0.99    v2_funct_2(sK4,sK2)),
% 3.18/0.99    inference(cnf_transformation,[],[f40])).
% 3.18/0.99  
% 3.18/0.99  cnf(c_21,negated_conjecture,
% 3.18/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.18/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_821,plain,
% 3.18/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_19,negated_conjecture,
% 3.18/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 3.18/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_823,plain,
% 3.18/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_15,plain,
% 3.18/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.18/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.18/0.99      | ~ v1_funct_1(X0)
% 3.18/0.99      | ~ v1_funct_1(X3)
% 3.18/0.99      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.18/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_824,plain,
% 3.18/0.99      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.18/0.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.18/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.18/0.99      | v1_funct_1(X5) != iProver_top
% 3.18/0.99      | v1_funct_1(X4) != iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2279,plain,
% 3.18/0.99      ( k1_partfun1(X0,X1,sK0,sK2,X2,sK4) = k5_relat_1(X2,sK4)
% 3.18/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.18/0.99      | v1_funct_1(X2) != iProver_top
% 3.18/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_823,c_824]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_20,negated_conjecture,
% 3.18/0.99      ( v1_funct_1(sK4) ),
% 3.18/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_25,plain,
% 3.18/0.99      ( v1_funct_1(sK4) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2908,plain,
% 3.18/0.99      ( v1_funct_1(X2) != iProver_top
% 3.18/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.18/0.99      | k1_partfun1(X0,X1,sK0,sK2,X2,sK4) = k5_relat_1(X2,sK4) ),
% 3.18/0.99      inference(global_propositional_subsumption,
% 3.18/0.99                [status(thm)],
% 3.18/0.99                [c_2279,c_25]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2909,plain,
% 3.18/0.99      ( k1_partfun1(X0,X1,sK0,sK2,X2,sK4) = k5_relat_1(X2,sK4)
% 3.18/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.18/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.18/0.99      inference(renaming,[status(thm)],[c_2908]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2918,plain,
% 3.18/0.99      ( k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
% 3.18/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_821,c_2909]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_22,negated_conjecture,
% 3.18/0.99      ( v1_funct_1(sK3) ),
% 3.18/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1072,plain,
% 3.18/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.18/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 3.18/0.99      | ~ v1_funct_1(X0)
% 3.18/0.99      | ~ v1_funct_1(sK4)
% 3.18/0.99      | k1_partfun1(X1,X2,X3,X4,X0,sK4) = k5_relat_1(X0,sK4) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1259,plain,
% 3.18/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.18/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.18/0.99      | ~ v1_funct_1(sK4)
% 3.18/0.99      | ~ v1_funct_1(sK3)
% 3.18/0.99      | k1_partfun1(X2,X3,X0,X1,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_1072]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1584,plain,
% 3.18/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 3.18/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.18/0.99      | ~ v1_funct_1(sK4)
% 3.18/0.99      | ~ v1_funct_1(sK3)
% 3.18/0.99      | k1_partfun1(X0,X1,sK0,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_1259]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2540,plain,
% 3.18/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 3.18/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.18/0.99      | ~ v1_funct_1(sK4)
% 3.18/0.99      | ~ v1_funct_1(sK3)
% 3.18/0.99      | k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_1584]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_3147,plain,
% 3.18/0.99      ( k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 3.18/0.99      inference(global_propositional_subsumption,
% 3.18/0.99                [status(thm)],
% 3.18/0.99                [c_2918,c_22,c_21,c_20,c_19,c_2540]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_13,plain,
% 3.18/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.18/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.18/0.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.18/0.99      | ~ v1_funct_1(X0)
% 3.18/0.99      | ~ v1_funct_1(X3) ),
% 3.18/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_826,plain,
% 3.18/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.18/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 3.18/0.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 3.18/0.99      | v1_funct_1(X0) != iProver_top
% 3.18/0.99      | v1_funct_1(X3) != iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_3433,plain,
% 3.18/0.99      ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top
% 3.18/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
% 3.18/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.18/0.99      | v1_funct_1(sK4) != iProver_top
% 3.18/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_3147,c_826]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_23,plain,
% 3.18/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_24,plain,
% 3.18/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_26,plain,
% 3.18/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_6427,plain,
% 3.18/0.99      ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.18/0.99      inference(global_propositional_subsumption,
% 3.18/0.99                [status(thm)],
% 3.18/0.99                [c_3433,c_23,c_24,c_25,c_26]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_9,plain,
% 3.18/0.99      ( v5_relat_1(X0,X1)
% 3.18/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.18/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_827,plain,
% 3.18/0.99      ( v5_relat_1(X0,X1) = iProver_top
% 3.18/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_6435,plain,
% 3.18/0.99      ( v5_relat_1(k5_relat_1(sK3,sK4),sK2) = iProver_top ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_6427,c_827]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_11,plain,
% 3.18/0.99      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.18/0.99      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 3.18/0.99      | ~ v1_relat_1(X0) ),
% 3.18/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_16,negated_conjecture,
% 3.18/0.99      ( ~ v2_funct_2(k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4),sK2) ),
% 3.18/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_267,plain,
% 3.18/0.99      ( ~ v5_relat_1(X0,k2_relat_1(X0))
% 3.18/0.99      | ~ v1_relat_1(X0)
% 3.18/0.99      | k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4) != X0
% 3.18/0.99      | k2_relat_1(X0) != sK2 ),
% 3.18/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_16]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_268,plain,
% 3.18/0.99      ( ~ v5_relat_1(k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4),k2_relat_1(k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4)))
% 3.18/0.99      | ~ v1_relat_1(k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4))
% 3.18/0.99      | k2_relat_1(k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4)) != sK2 ),
% 3.18/0.99      inference(unflattening,[status(thm)],[c_267]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_818,plain,
% 3.18/0.99      ( k2_relat_1(k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4)) != sK2
% 3.18/0.99      | v5_relat_1(k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4),k2_relat_1(k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4))) != iProver_top
% 3.18/0.99      | v1_relat_1(k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4)) != iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_268]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_3150,plain,
% 3.18/0.99      ( k2_relat_1(k5_relat_1(sK3,sK4)) != sK2
% 3.18/0.99      | v5_relat_1(k5_relat_1(sK3,sK4),k2_relat_1(k5_relat_1(sK3,sK4))) != iProver_top
% 3.18/0.99      | v1_relat_1(k5_relat_1(sK3,sK4)) != iProver_top ),
% 3.18/0.99      inference(demodulation,[status(thm)],[c_3147,c_818]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_8,plain,
% 3.18/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.18/0.99      | v1_relat_1(X0) ),
% 3.18/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_998,plain,
% 3.18/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 3.18/0.99      | v1_relat_1(sK4) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_999,plain,
% 3.18/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
% 3.18/0.99      | v1_relat_1(sK4) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_998]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1001,plain,
% 3.18/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.18/0.99      | v1_relat_1(sK3) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1002,plain,
% 3.18/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.18/0.99      | v1_relat_1(sK3) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_1001]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_3,plain,
% 3.18/0.99      ( ~ v1_relat_1(X0)
% 3.18/0.99      | ~ v1_relat_1(X1)
% 3.18/0.99      | v1_relat_1(k5_relat_1(X1,X0)) ),
% 3.18/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1111,plain,
% 3.18/0.99      ( ~ v1_relat_1(X0)
% 3.18/0.99      | v1_relat_1(k5_relat_1(X0,sK4))
% 3.18/0.99      | ~ v1_relat_1(sK4) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1344,plain,
% 3.18/0.99      ( v1_relat_1(k5_relat_1(sK3,sK4))
% 3.18/0.99      | ~ v1_relat_1(sK4)
% 3.18/0.99      | ~ v1_relat_1(sK3) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_1111]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1345,plain,
% 3.18/0.99      ( v1_relat_1(k5_relat_1(sK3,sK4)) = iProver_top
% 3.18/0.99      | v1_relat_1(sK4) != iProver_top
% 3.18/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_1344]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_828,plain,
% 3.18/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.18/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1554,plain,
% 3.18/0.99      ( v1_relat_1(sK3) = iProver_top ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_821,c_828]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1553,plain,
% 3.18/0.99      ( v1_relat_1(sK4) = iProver_top ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_823,c_828]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_6,plain,
% 3.18/0.99      ( ~ v1_relat_1(X0)
% 3.18/0.99      | ~ v1_relat_1(X1)
% 3.18/0.99      | k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0)) ),
% 3.18/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_829,plain,
% 3.18/0.99      ( k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0))
% 3.18/0.99      | v1_relat_1(X0) != iProver_top
% 3.18/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2681,plain,
% 3.18/0.99      ( k9_relat_1(sK4,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,sK4))
% 3.18/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_1553,c_829]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_4830,plain,
% 3.18/0.99      ( k9_relat_1(sK4,k2_relat_1(sK3)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_1554,c_2681]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_12,plain,
% 3.18/0.99      ( ~ v2_funct_2(X0,X1)
% 3.18/0.99      | ~ v5_relat_1(X0,X1)
% 3.18/0.99      | ~ v1_relat_1(X0)
% 3.18/0.99      | k2_relat_1(X0) = X1 ),
% 3.18/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_18,negated_conjecture,
% 3.18/0.99      ( v2_funct_2(sK3,sK0) ),
% 3.18/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_293,plain,
% 3.18/0.99      ( ~ v5_relat_1(X0,X1)
% 3.18/0.99      | ~ v1_relat_1(X0)
% 3.18/0.99      | k2_relat_1(X0) = X1
% 3.18/0.99      | sK3 != X0
% 3.18/0.99      | sK0 != X1 ),
% 3.18/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_18]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_294,plain,
% 3.18/0.99      ( ~ v5_relat_1(sK3,sK0)
% 3.18/0.99      | ~ v1_relat_1(sK3)
% 3.18/0.99      | k2_relat_1(sK3) = sK0 ),
% 3.18/0.99      inference(unflattening,[status(thm)],[c_293]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_816,plain,
% 3.18/0.99      ( k2_relat_1(sK3) = sK0
% 3.18/0.99      | v5_relat_1(sK3,sK0) != iProver_top
% 3.18/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_294]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1019,plain,
% 3.18/0.99      ( v5_relat_1(sK3,sK0)
% 3.18/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1179,plain,
% 3.18/0.99      ( k2_relat_1(sK3) = sK0 ),
% 3.18/0.99      inference(global_propositional_subsumption,
% 3.18/0.99                [status(thm)],
% 3.18/0.99                [c_816,c_21,c_294,c_1001,c_1019]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_10,plain,
% 3.18/0.99      ( v4_relat_1(X0,X1)
% 3.18/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.18/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_7,plain,
% 3.18/0.99      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 3.18/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_245,plain,
% 3.18/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.18/0.99      | ~ v1_relat_1(X0)
% 3.18/0.99      | k7_relat_1(X0,X1) = X0 ),
% 3.18/0.99      inference(resolution,[status(thm)],[c_10,c_7]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_249,plain,
% 3.18/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.18/0.99      | k7_relat_1(X0,X1) = X0 ),
% 3.18/0.99      inference(global_propositional_subsumption,
% 3.18/0.99                [status(thm)],
% 3.18/0.99                [c_245,c_10,c_8,c_7]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_819,plain,
% 3.18/0.99      ( k7_relat_1(X0,X1) = X0
% 3.18/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_249]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2119,plain,
% 3.18/0.99      ( k7_relat_1(sK4,sK0) = sK4 ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_823,c_819]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_5,plain,
% 3.18/0.99      ( ~ v1_relat_1(X0)
% 3.18/0.99      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 3.18/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_830,plain,
% 3.18/0.99      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 3.18/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1620,plain,
% 3.18/0.99      ( k2_relat_1(k7_relat_1(sK4,X0)) = k9_relat_1(sK4,X0) ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_1553,c_830]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2271,plain,
% 3.18/0.99      ( k9_relat_1(sK4,sK0) = k2_relat_1(sK4) ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_2119,c_1620]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_17,negated_conjecture,
% 3.18/0.99      ( v2_funct_2(sK4,sK2) ),
% 3.18/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_280,plain,
% 3.18/0.99      ( ~ v5_relat_1(X0,X1)
% 3.18/0.99      | ~ v1_relat_1(X0)
% 3.18/0.99      | k2_relat_1(X0) = X1
% 3.18/0.99      | sK4 != X0
% 3.18/0.99      | sK2 != X1 ),
% 3.18/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_17]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_281,plain,
% 3.18/0.99      ( ~ v5_relat_1(sK4,sK2)
% 3.18/0.99      | ~ v1_relat_1(sK4)
% 3.18/0.99      | k2_relat_1(sK4) = sK2 ),
% 3.18/0.99      inference(unflattening,[status(thm)],[c_280]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_817,plain,
% 3.18/0.99      ( k2_relat_1(sK4) = sK2
% 3.18/0.99      | v5_relat_1(sK4,sK2) != iProver_top
% 3.18/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_281]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1016,plain,
% 3.18/0.99      ( v5_relat_1(sK4,sK2)
% 3.18/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1183,plain,
% 3.18/0.99      ( k2_relat_1(sK4) = sK2 ),
% 3.18/0.99      inference(global_propositional_subsumption,
% 3.18/0.99                [status(thm)],
% 3.18/0.99                [c_817,c_19,c_281,c_998,c_1016]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2272,plain,
% 3.18/0.99      ( k9_relat_1(sK4,sK0) = sK2 ),
% 3.18/0.99      inference(light_normalisation,[status(thm)],[c_2271,c_1183]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_4832,plain,
% 3.18/0.99      ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2 ),
% 3.18/0.99      inference(light_normalisation,[status(thm)],[c_4830,c_1179,c_2272]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_6116,plain,
% 3.18/0.99      ( v5_relat_1(k5_relat_1(sK3,sK4),k2_relat_1(k5_relat_1(sK3,sK4))) != iProver_top ),
% 3.18/0.99      inference(global_propositional_subsumption,
% 3.18/0.99                [status(thm)],
% 3.18/0.99                [c_3150,c_24,c_26,c_999,c_1002,c_1345,c_4832]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_6120,plain,
% 3.18/0.99      ( v5_relat_1(k5_relat_1(sK3,sK4),sK2) != iProver_top ),
% 3.18/0.99      inference(light_normalisation,[status(thm)],[c_6116,c_4832]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(contradiction,plain,
% 3.18/0.99      ( $false ),
% 3.18/0.99      inference(minisat,[status(thm)],[c_6435,c_6120]) ).
% 3.18/0.99  
% 3.18/0.99  
% 3.18/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.18/0.99  
% 3.18/0.99  ------                               Statistics
% 3.18/0.99  
% 3.18/0.99  ------ General
% 3.18/0.99  
% 3.18/0.99  abstr_ref_over_cycles:                  0
% 3.18/0.99  abstr_ref_under_cycles:                 0
% 3.18/0.99  gc_basic_clause_elim:                   0
% 3.18/0.99  forced_gc_time:                         0
% 3.18/0.99  parsing_time:                           0.011
% 3.18/0.99  unif_index_cands_time:                  0.
% 3.18/0.99  unif_index_add_time:                    0.
% 3.18/0.99  orderings_time:                         0.
% 3.18/0.99  out_proof_time:                         0.009
% 3.18/0.99  total_time:                             0.213
% 3.18/0.99  num_of_symbols:                         50
% 3.18/0.99  num_of_terms:                           7952
% 3.18/0.99  
% 3.18/0.99  ------ Preprocessing
% 3.18/0.99  
% 3.18/0.99  num_of_splits:                          0
% 3.18/0.99  num_of_split_atoms:                     0
% 3.18/0.99  num_of_reused_defs:                     0
% 3.18/0.99  num_eq_ax_congr_red:                    21
% 3.18/0.99  num_of_sem_filtered_clauses:            1
% 3.18/0.99  num_of_subtypes:                        0
% 3.18/0.99  monotx_restored_types:                  0
% 3.18/0.99  sat_num_of_epr_types:                   0
% 3.18/0.99  sat_num_of_non_cyclic_types:            0
% 3.18/0.99  sat_guarded_non_collapsed_types:        0
% 3.18/0.99  num_pure_diseq_elim:                    0
% 3.18/0.99  simp_replaced_by:                       0
% 3.18/0.99  res_preprocessed:                       112
% 3.18/0.99  prep_upred:                             0
% 3.18/0.99  prep_unflattend:                        7
% 3.18/0.99  smt_new_axioms:                         0
% 3.18/0.99  pred_elim_cands:                        4
% 3.18/0.99  pred_elim:                              2
% 3.18/0.99  pred_elim_cl:                           1
% 3.18/0.99  pred_elim_cycles:                       4
% 3.18/0.99  merged_defs:                            0
% 3.18/0.99  merged_defs_ncl:                        0
% 3.18/0.99  bin_hyper_res:                          0
% 3.18/0.99  prep_cycles:                            4
% 3.18/0.99  pred_elim_time:                         0.002
% 3.18/0.99  splitting_time:                         0.
% 3.18/0.99  sem_filter_time:                        0.
% 3.18/0.99  monotx_time:                            0.
% 3.18/0.99  subtype_inf_time:                       0.
% 3.18/0.99  
% 3.18/0.99  ------ Problem properties
% 3.18/0.99  
% 3.18/0.99  clauses:                                22
% 3.18/0.99  conjectures:                            4
% 3.18/0.99  epr:                                    2
% 3.18/0.99  horn:                                   22
% 3.18/0.99  ground:                                 9
% 3.18/0.99  unary:                                  8
% 3.18/0.99  binary:                                 5
% 3.18/0.99  lits:                                   52
% 3.18/0.99  lits_eq:                                11
% 3.18/0.99  fd_pure:                                0
% 3.18/0.99  fd_pseudo:                              0
% 3.18/0.99  fd_cond:                                0
% 3.18/0.99  fd_pseudo_cond:                         0
% 3.18/0.99  ac_symbols:                             0
% 3.18/0.99  
% 3.18/0.99  ------ Propositional Solver
% 3.18/0.99  
% 3.18/0.99  prop_solver_calls:                      28
% 3.18/0.99  prop_fast_solver_calls:                 779
% 3.18/0.99  smt_solver_calls:                       0
% 3.18/0.99  smt_fast_solver_calls:                  0
% 3.18/0.99  prop_num_of_clauses:                    3250
% 3.18/0.99  prop_preprocess_simplified:             7376
% 3.18/0.99  prop_fo_subsumed:                       39
% 3.18/0.99  prop_solver_time:                       0.
% 3.18/0.99  smt_solver_time:                        0.
% 3.18/0.99  smt_fast_solver_time:                   0.
% 3.18/0.99  prop_fast_solver_time:                  0.
% 3.18/0.99  prop_unsat_core_time:                   0.
% 3.18/0.99  
% 3.18/0.99  ------ QBF
% 3.18/0.99  
% 3.18/0.99  qbf_q_res:                              0
% 3.18/0.99  qbf_num_tautologies:                    0
% 3.18/0.99  qbf_prep_cycles:                        0
% 3.18/0.99  
% 3.18/0.99  ------ BMC1
% 3.18/0.99  
% 3.18/0.99  bmc1_current_bound:                     -1
% 3.18/0.99  bmc1_last_solved_bound:                 -1
% 3.18/0.99  bmc1_unsat_core_size:                   -1
% 3.18/0.99  bmc1_unsat_core_parents_size:           -1
% 3.18/0.99  bmc1_merge_next_fun:                    0
% 3.18/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.18/0.99  
% 3.18/0.99  ------ Instantiation
% 3.18/0.99  
% 3.18/0.99  inst_num_of_clauses:                    898
% 3.18/0.99  inst_num_in_passive:                    184
% 3.18/0.99  inst_num_in_active:                     413
% 3.18/0.99  inst_num_in_unprocessed:                301
% 3.18/0.99  inst_num_of_loops:                      430
% 3.18/0.99  inst_num_of_learning_restarts:          0
% 3.18/0.99  inst_num_moves_active_passive:          16
% 3.18/0.99  inst_lit_activity:                      0
% 3.18/0.99  inst_lit_activity_moves:                1
% 3.18/0.99  inst_num_tautologies:                   0
% 3.18/0.99  inst_num_prop_implied:                  0
% 3.18/0.99  inst_num_existing_simplified:           0
% 3.18/0.99  inst_num_eq_res_simplified:             0
% 3.18/0.99  inst_num_child_elim:                    0
% 3.18/0.99  inst_num_of_dismatching_blockings:      51
% 3.18/0.99  inst_num_of_non_proper_insts:           374
% 3.18/0.99  inst_num_of_duplicates:                 0
% 3.18/0.99  inst_inst_num_from_inst_to_res:         0
% 3.18/0.99  inst_dismatching_checking_time:         0.
% 3.18/0.99  
% 3.18/0.99  ------ Resolution
% 3.18/0.99  
% 3.18/0.99  res_num_of_clauses:                     0
% 3.18/0.99  res_num_in_passive:                     0
% 3.18/0.99  res_num_in_active:                      0
% 3.18/0.99  res_num_of_loops:                       116
% 3.18/0.99  res_forward_subset_subsumed:            21
% 3.18/0.99  res_backward_subset_subsumed:           0
% 3.18/0.99  res_forward_subsumed:                   0
% 3.18/0.99  res_backward_subsumed:                  0
% 3.18/0.99  res_forward_subsumption_resolution:     0
% 3.18/0.99  res_backward_subsumption_resolution:    0
% 3.18/0.99  res_clause_to_clause_subsumption:       276
% 3.18/0.99  res_orphan_elimination:                 0
% 3.18/0.99  res_tautology_del:                      25
% 3.18/0.99  res_num_eq_res_simplified:              1
% 3.18/0.99  res_num_sel_changes:                    0
% 3.18/0.99  res_moves_from_active_to_pass:          0
% 3.18/0.99  
% 3.18/0.99  ------ Superposition
% 3.18/0.99  
% 3.18/0.99  sup_time_total:                         0.
% 3.18/0.99  sup_time_generating:                    0.
% 3.18/0.99  sup_time_sim_full:                      0.
% 3.18/0.99  sup_time_sim_immed:                     0.
% 3.18/0.99  
% 3.18/0.99  sup_num_of_clauses:                     130
% 3.18/0.99  sup_num_in_active:                      82
% 3.18/0.99  sup_num_in_passive:                     48
% 3.18/0.99  sup_num_of_loops:                       84
% 3.18/0.99  sup_fw_superposition:                   61
% 3.18/0.99  sup_bw_superposition:                   56
% 3.18/0.99  sup_immediate_simplified:               11
% 3.18/0.99  sup_given_eliminated:                   0
% 3.18/0.99  comparisons_done:                       0
% 3.18/0.99  comparisons_avoided:                    0
% 3.18/0.99  
% 3.18/0.99  ------ Simplifications
% 3.18/0.99  
% 3.18/0.99  
% 3.18/0.99  sim_fw_subset_subsumed:                 0
% 3.18/0.99  sim_bw_subset_subsumed:                 0
% 3.18/0.99  sim_fw_subsumed:                        0
% 3.18/0.99  sim_bw_subsumed:                        0
% 3.18/0.99  sim_fw_subsumption_res:                 2
% 3.18/0.99  sim_bw_subsumption_res:                 0
% 3.18/0.99  sim_tautology_del:                      1
% 3.18/0.99  sim_eq_tautology_del:                   0
% 3.18/0.99  sim_eq_res_simp:                        0
% 3.18/0.99  sim_fw_demodulated:                     0
% 3.18/0.99  sim_bw_demodulated:                     3
% 3.18/0.99  sim_light_normalised:                   13
% 3.18/0.99  sim_joinable_taut:                      0
% 3.18/0.99  sim_joinable_simp:                      0
% 3.18/0.99  sim_ac_normalised:                      0
% 3.18/0.99  sim_smt_subsumption:                    0
% 3.18/0.99  
%------------------------------------------------------------------------------
