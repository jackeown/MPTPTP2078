%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:10:19 EST 2020

% Result     : Theorem 2.82s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 488 expanded)
%              Number of clauses        :   95 ( 135 expanded)
%              Number of leaves         :   22 ( 176 expanded)
%              Depth                    :   16
%              Number of atoms          :  607 (3753 expanded)
%              Number of equality atoms :  189 ( 596 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2,X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                & v1_funct_2(X3,X1,X0)
                & v1_funct_1(X3) )
             => ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                    & v1_funct_1(X4) )
                 => ! [X5] :
                      ( m1_subset_1(X5,X1)
                     => ( v1_partfun1(X4,X0)
                       => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2,X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                  & v1_funct_2(X3,X1,X0)
                  & v1_funct_1(X3) )
               => ! [X4] :
                    ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                      & v1_funct_1(X4) )
                   => ! [X5] :
                        ( m1_subset_1(X5,X1)
                       => ( v1_partfun1(X4,X0)
                         => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
                      & v1_partfun1(X4,X0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
                      & v1_partfun1(X4,X0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
          & v1_partfun1(X4,X0)
          & m1_subset_1(X5,X1) )
     => ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),sK5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,sK5))
        & v1_partfun1(X4,X0)
        & m1_subset_1(sK5,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
              & v1_partfun1(X4,X0)
              & m1_subset_1(X5,X1) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,sK4),X5) != k1_funct_1(sK4,k3_funct_2(X1,X0,X3,X5))
            & v1_partfun1(sK4,X0)
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ? [X2,X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
                  & v1_partfun1(X4,X0)
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( k3_funct_2(X1,sK2,k8_funct_2(X1,X0,sK2,sK3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,sK3,X5))
                & v1_partfun1(X4,X0)
                & m1_subset_1(X5,X1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
            & v1_funct_1(X4) )
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK3,X1,X0)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
                      & v1_partfun1(X4,X0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
     => ( ? [X3,X2] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k3_funct_2(sK1,X2,k8_funct_2(sK1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(sK1,X0,X3,X5))
                    & v1_partfun1(X4,X0)
                    & m1_subset_1(X5,sK1) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
            & v1_funct_2(X3,sK1,X0)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2,X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
                        & v1_partfun1(X4,X0)
                        & m1_subset_1(X5,X1) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                    & v1_funct_1(X4) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                & v1_funct_2(X3,X1,X0)
                & v1_funct_1(X3) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X3,X2] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,sK0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,sK0,X3,X5))
                      & v1_partfun1(X4,sK0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
              & v1_funct_2(X3,X1,sK0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    & v1_partfun1(sK4,sK0)
    & m1_subset_1(sK5,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f29,f35,f34,f33,f32,f31])).

fof(f57,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f56,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f36])).

fof(f54,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X4)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f22])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f51,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f52,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f53,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f55,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f59,plain,(
    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f58,plain,(
    v1_partfun1(sK4,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f26])).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
      | ~ m1_subset_1(X5,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X3,X1,X2)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f50,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_814,plain,
    ( ~ v1_xboole_0(X0_52)
    | v1_xboole_0(X1_52)
    | X1_52 != X0_52 ),
    theory(equality)).

cnf(c_1310,plain,
    ( v1_xboole_0(X0_52)
    | ~ v1_xboole_0(k1_xboole_0)
    | X0_52 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_814])).

cnf(c_6822,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1310])).

cnf(c_813,plain,
    ( X0_52 != X1_52
    | X2_52 != X1_52
    | X2_52 = X0_52 ),
    theory(equality)).

cnf(c_1584,plain,
    ( X0_52 != X1_52
    | sK1 != X1_52
    | sK1 = X0_52 ),
    inference(instantiation,[status(thm)],[c_813])).

cnf(c_1902,plain,
    ( X0_52 != sK1
    | sK1 = X0_52
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1584])).

cnf(c_5253,plain,
    ( sK1 != sK1
    | sK1 = k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_1902])).

cnf(c_815,plain,
    ( X0_52 != X1_52
    | k1_zfmisc_1(X0_52) = k1_zfmisc_1(X1_52) ),
    theory(equality)).

cnf(c_1550,plain,
    ( X0_52 != sK0
    | k1_zfmisc_1(X0_52) = k1_zfmisc_1(sK0) ),
    inference(instantiation,[status(thm)],[c_815])).

cnf(c_4191,plain,
    ( k1_relset_1(sK0,sK2,sK4) != sK0
    | k1_zfmisc_1(k1_relset_1(sK0,sK2,sK4)) = k1_zfmisc_1(sK0) ),
    inference(instantiation,[status(thm)],[c_1550])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_800,negated_conjecture,
    ( m1_subset_1(sK5,sK1) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1156,plain,
    ( m1_subset_1(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_800])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_799,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1157,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_799])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_797,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1159,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_797])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k8_funct_2(X1,X2,X4,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_805,plain,
    ( ~ v1_funct_2(X0_51,X0_52,X1_52)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
    | m1_subset_1(k8_funct_2(X0_52,X1_52,X2_52,X0_51,X1_51),k1_zfmisc_1(k2_zfmisc_1(X0_52,X2_52)))
    | ~ v1_funct_1(X0_51)
    | ~ v1_funct_1(X1_51) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1152,plain,
    ( v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52))) != iProver_top
    | m1_subset_1(k8_funct_2(X0_52,X1_52,X2_52,X0_51,X1_51),k1_zfmisc_1(k2_zfmisc_1(X0_52,X2_52))) = iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_805])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_802,plain,
    ( ~ v1_funct_2(X0_51,X0_52,X1_52)
    | ~ m1_subset_1(X1_51,X0_52)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ v1_funct_1(X0_51)
    | v1_xboole_0(X0_52)
    | k3_funct_2(X0_52,X1_52,X0_51,X1_51) = k1_funct_1(X0_51,X1_51) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1155,plain,
    ( k3_funct_2(X0_52,X1_52,X0_51,X1_51) = k1_funct_1(X0_51,X1_51)
    | v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
    | m1_subset_1(X1_51,X0_52) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_xboole_0(X0_52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_802])).

cnf(c_1912,plain,
    ( k3_funct_2(X0_52,X1_52,k8_funct_2(X0_52,X2_52,X1_52,X0_51,X1_51),X2_51) = k1_funct_1(k8_funct_2(X0_52,X2_52,X1_52,X0_51,X1_51),X2_51)
    | v1_funct_2(X0_51,X0_52,X2_52) != iProver_top
    | v1_funct_2(k8_funct_2(X0_52,X2_52,X1_52,X0_51,X1_51),X0_52,X1_52) != iProver_top
    | m1_subset_1(X2_51,X0_52) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X2_52))) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X2_52,X1_52))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_funct_1(k8_funct_2(X0_52,X2_52,X1_52,X0_51,X1_51)) != iProver_top
    | v1_xboole_0(X0_52) = iProver_top ),
    inference(superposition,[status(thm)],[c_1152,c_1155])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k8_funct_2(X1,X2,X4,X0,X3)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_803,plain,
    ( ~ v1_funct_2(X0_51,X0_52,X1_52)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
    | ~ v1_funct_1(X0_51)
    | ~ v1_funct_1(X1_51)
    | v1_funct_1(k8_funct_2(X0_52,X1_52,X2_52,X0_51,X1_51)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1154,plain,
    ( v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_funct_1(k8_funct_2(X0_52,X1_52,X2_52,X0_51,X1_51)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_803])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k8_funct_2(X1,X2,X3,X0,X4),X1,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_804,plain,
    ( ~ v1_funct_2(X0_51,X0_52,X1_52)
    | v1_funct_2(k8_funct_2(X0_52,X1_52,X2_52,X0_51,X1_51),X0_52,X2_52)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
    | ~ v1_funct_1(X0_51)
    | ~ v1_funct_1(X1_51) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1153,plain,
    ( v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
    | v1_funct_2(k8_funct_2(X0_52,X1_52,X2_52,X0_51,X1_51),X0_52,X2_52) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_804])).

cnf(c_3653,plain,
    ( k3_funct_2(X0_52,X1_52,k8_funct_2(X0_52,X2_52,X1_52,X0_51,X1_51),X2_51) = k1_funct_1(k8_funct_2(X0_52,X2_52,X1_52,X0_51,X1_51),X2_51)
    | v1_funct_2(X0_51,X0_52,X2_52) != iProver_top
    | m1_subset_1(X2_51,X0_52) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X2_52))) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X2_52,X1_52))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_xboole_0(X0_52) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1912,c_1154,c_1153])).

cnf(c_3658,plain,
    ( k3_funct_2(sK1,X0_52,k8_funct_2(sK1,sK0,X0_52,sK3,X0_51),X1_51) = k1_funct_1(k8_funct_2(sK1,sK0,X0_52,sK3,X0_51),X1_51)
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_52))) != iProver_top
    | m1_subset_1(X1_51,sK1) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1159,c_3653])).

cnf(c_21,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_24,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_25,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_26,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3841,plain,
    ( k3_funct_2(sK1,X0_52,k8_funct_2(sK1,sK0,X0_52,sK3,X0_51),X1_51) = k1_funct_1(k8_funct_2(sK1,sK0,X0_52,sK3,X0_51),X1_51)
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_52))) != iProver_top
    | m1_subset_1(X1_51,sK1) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3658,c_24,c_25,c_26])).

cnf(c_3851,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0_51) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0_51)
    | m1_subset_1(X0_51,sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1157,c_3841])).

cnf(c_17,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_28,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3934,plain,
    ( m1_subset_1(X0_51,sK1) != iProver_top
    | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0_51) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0_51) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3851,c_28])).

cnf(c_3935,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0_51) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0_51)
    | m1_subset_1(X0_51,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3934])).

cnf(c_3942,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) ),
    inference(superposition,[status(thm)],[c_1156,c_3935])).

cnf(c_1597,plain,
    ( k3_funct_2(sK1,sK0,sK3,X0_51) = k1_funct_1(sK3,X0_51)
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(X0_51,sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1159,c_1155])).

cnf(c_1781,plain,
    ( k3_funct_2(sK1,sK0,sK3,X0_51) = k1_funct_1(sK3,X0_51)
    | m1_subset_1(X0_51,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1597,c_24,c_25,c_26])).

cnf(c_1789,plain,
    ( k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) ),
    inference(superposition,[status(thm)],[c_1156,c_1781])).

cnf(c_13,negated_conjecture,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_801,negated_conjecture,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1864,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_1789,c_801])).

cnf(c_3944,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_3942,c_1864])).

cnf(c_816,plain,
    ( ~ m1_subset_1(X0_51,X0_52)
    | m1_subset_1(X1_51,X1_52)
    | X1_52 != X0_52
    | X1_51 != X0_51 ),
    theory(equality)).

cnf(c_1427,plain,
    ( m1_subset_1(X0_51,X0_52)
    | ~ m1_subset_1(k2_relset_1(sK1,sK0,sK3),k1_zfmisc_1(sK0))
    | X0_52 != k1_zfmisc_1(sK0)
    | X0_51 != k2_relset_1(sK1,sK0,sK3) ),
    inference(instantiation,[status(thm)],[c_816])).

cnf(c_1549,plain,
    ( m1_subset_1(X0_51,k1_zfmisc_1(X0_52))
    | ~ m1_subset_1(k2_relset_1(sK1,sK0,sK3),k1_zfmisc_1(sK0))
    | k1_zfmisc_1(X0_52) != k1_zfmisc_1(sK0)
    | X0_51 != k2_relset_1(sK1,sK0,sK3) ),
    inference(instantiation,[status(thm)],[c_1427])).

cnf(c_1977,plain,
    ( m1_subset_1(k2_relset_1(sK1,sK0,sK3),k1_zfmisc_1(X0_52))
    | ~ m1_subset_1(k2_relset_1(sK1,sK0,sK3),k1_zfmisc_1(sK0))
    | k1_zfmisc_1(X0_52) != k1_zfmisc_1(sK0)
    | k2_relset_1(sK1,sK0,sK3) != k2_relset_1(sK1,sK0,sK3) ),
    inference(instantiation,[status(thm)],[c_1549])).

cnf(c_3226,plain,
    ( m1_subset_1(k2_relset_1(sK1,sK0,sK3),k1_zfmisc_1(k1_relset_1(sK0,sK2,sK4)))
    | ~ m1_subset_1(k2_relset_1(sK1,sK0,sK3),k1_zfmisc_1(sK0))
    | k1_zfmisc_1(k1_relset_1(sK0,sK2,sK4)) != k1_zfmisc_1(sK0)
    | k2_relset_1(sK1,sK0,sK3) != k2_relset_1(sK1,sK0,sK3) ),
    inference(instantiation,[status(thm)],[c_1977])).

cnf(c_810,plain,
    ( X0_51 = X0_51 ),
    theory(equality)).

cnf(c_1978,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relset_1(sK1,sK0,sK3) ),
    inference(instantiation,[status(thm)],[c_810])).

cnf(c_3,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_7,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_281,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_3,c_7])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_285,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_281,c_7,c_3,c_2])).

cnf(c_286,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_285])).

cnf(c_14,negated_conjecture,
    ( v1_partfun1(sK4,sK0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_327,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1
    | sK4 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_286,c_14])).

cnf(c_328,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | k1_relat_1(sK4) = sK0 ),
    inference(unflattening,[status(thm)],[c_327])).

cnf(c_792,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_52)))
    | k1_relat_1(sK4) = sK0 ),
    inference(subtyping,[status(esa)],[c_328])).

cnf(c_1164,plain,
    ( k1_relat_1(sK4) = sK0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_52))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_792])).

cnf(c_1304,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_relat_1(sK4) = sK0 ),
    inference(instantiation,[status(thm)],[c_792])).

cnf(c_1727,plain,
    ( k1_relat_1(sK4) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1164,c_16,c_1304])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_806,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | k1_relset_1(X0_52,X1_52,X0_51) = k1_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1151,plain,
    ( k1_relset_1(X0_52,X1_52,X0_51) = k1_relat_1(X0_51)
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_806])).

cnf(c_1562,plain,
    ( k1_relset_1(sK0,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1157,c_1151])).

cnf(c_1730,plain,
    ( k1_relset_1(sK0,sK2,sK4) = sK0 ),
    inference(demodulation,[status(thm)],[c_1727,c_1562])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X5,X4))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_funct_1(k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_342,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X2,X7)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X6)
    | v1_xboole_0(X2)
    | k1_relset_1(X2,X7,X6) != X5
    | k2_relset_1(X1,X2,X0) != X4
    | k1_funct_1(k8_funct_2(X1,X2,X7,X0,X6),X3) = k1_funct_1(X6,k1_funct_1(X0,X3))
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_12])).

cnf(c_343,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
    | ~ m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(k1_relset_1(X2,X5,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X4)
    | v1_xboole_0(X2)
    | k1_funct_1(k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_342])).

cnf(c_791,plain,
    ( ~ v1_funct_2(X0_51,X0_52,X1_52)
    | ~ m1_subset_1(X1_51,X0_52)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
    | ~ m1_subset_1(k2_relset_1(X0_52,X1_52,X0_51),k1_zfmisc_1(k1_relset_1(X1_52,X2_52,X2_51)))
    | ~ v1_funct_1(X0_51)
    | ~ v1_funct_1(X2_51)
    | v1_xboole_0(X1_52)
    | k1_xboole_0 = X0_52
    | k1_funct_1(k8_funct_2(X0_52,X1_52,X2_52,X0_51,X2_51),X1_51) = k1_funct_1(X2_51,k1_funct_1(X0_51,X1_51)) ),
    inference(subtyping,[status(esa)],[c_343])).

cnf(c_1387,plain,
    ( ~ v1_funct_2(X0_51,sK1,X0_52)
    | ~ m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK1,X0_52)))
    | ~ m1_subset_1(k2_relset_1(sK1,X0_52,X0_51),k1_zfmisc_1(k1_relset_1(X0_52,X1_52,X1_51)))
    | ~ m1_subset_1(sK5,sK1)
    | ~ v1_funct_1(X0_51)
    | ~ v1_funct_1(X1_51)
    | v1_xboole_0(X0_52)
    | k1_xboole_0 = sK1
    | k1_funct_1(k8_funct_2(sK1,X0_52,X1_52,X0_51,X1_51),sK5) = k1_funct_1(X1_51,k1_funct_1(X0_51,sK5)) ),
    inference(instantiation,[status(thm)],[c_791])).

cnf(c_1491,plain,
    ( ~ v1_funct_2(X0_51,sK1,sK0)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k2_relset_1(sK1,sK0,X0_51),k1_zfmisc_1(k1_relset_1(sK0,sK2,sK4)))
    | ~ m1_subset_1(sK5,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(X0_51)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK0)
    | k1_xboole_0 = sK1
    | k1_funct_1(k8_funct_2(sK1,sK0,sK2,X0_51,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(X0_51,sK5)) ),
    inference(instantiation,[status(thm)],[c_1387])).

cnf(c_1493,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(k2_relset_1(sK1,sK0,sK3),k1_zfmisc_1(k1_relset_1(sK0,sK2,sK4)))
    | ~ m1_subset_1(sK5,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK0)
    | k1_xboole_0 = sK1
    | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(instantiation,[status(thm)],[c_1491])).

cnf(c_811,plain,
    ( X0_52 = X0_52 ),
    theory(equality)).

cnf(c_1439,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_811])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_807,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | m1_subset_1(k2_relset_1(X0_52,X1_52,X0_51),k1_zfmisc_1(X1_52)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1330,plain,
    ( m1_subset_1(k2_relset_1(sK1,sK0,sK3),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(instantiation,[status(thm)],[c_807])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_22,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6822,c_5253,c_4191,c_3944,c_3226,c_1978,c_1730,c_1493,c_1439,c_1330,c_0,c_15,c_16,c_17,c_18,c_19,c_20,c_21,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : iproveropt_run.sh %d %s
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:44:55 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running in FOF mode
% 2.82/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.01  
% 2.82/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.82/1.01  
% 2.82/1.01  ------  iProver source info
% 2.82/1.01  
% 2.82/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.82/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.82/1.01  git: non_committed_changes: false
% 2.82/1.01  git: last_make_outside_of_git: false
% 2.82/1.01  
% 2.82/1.01  ------ 
% 2.82/1.01  
% 2.82/1.01  ------ Input Options
% 2.82/1.01  
% 2.82/1.01  --out_options                           all
% 2.82/1.01  --tptp_safe_out                         true
% 2.82/1.01  --problem_path                          ""
% 2.82/1.01  --include_path                          ""
% 2.82/1.01  --clausifier                            res/vclausify_rel
% 2.82/1.01  --clausifier_options                    --mode clausify
% 2.82/1.01  --stdin                                 false
% 2.82/1.01  --stats_out                             all
% 2.82/1.01  
% 2.82/1.01  ------ General Options
% 2.82/1.01  
% 2.82/1.01  --fof                                   false
% 2.82/1.01  --time_out_real                         305.
% 2.82/1.01  --time_out_virtual                      -1.
% 2.82/1.01  --symbol_type_check                     false
% 2.82/1.01  --clausify_out                          false
% 2.82/1.01  --sig_cnt_out                           false
% 2.82/1.01  --trig_cnt_out                          false
% 2.82/1.01  --trig_cnt_out_tolerance                1.
% 2.82/1.01  --trig_cnt_out_sk_spl                   false
% 2.82/1.01  --abstr_cl_out                          false
% 2.82/1.01  
% 2.82/1.01  ------ Global Options
% 2.82/1.01  
% 2.82/1.01  --schedule                              default
% 2.82/1.01  --add_important_lit                     false
% 2.82/1.01  --prop_solver_per_cl                    1000
% 2.82/1.01  --min_unsat_core                        false
% 2.82/1.01  --soft_assumptions                      false
% 2.82/1.01  --soft_lemma_size                       3
% 2.82/1.01  --prop_impl_unit_size                   0
% 2.82/1.01  --prop_impl_unit                        []
% 2.82/1.01  --share_sel_clauses                     true
% 2.82/1.01  --reset_solvers                         false
% 2.82/1.01  --bc_imp_inh                            [conj_cone]
% 2.82/1.01  --conj_cone_tolerance                   3.
% 2.82/1.01  --extra_neg_conj                        none
% 2.82/1.01  --large_theory_mode                     true
% 2.82/1.01  --prolific_symb_bound                   200
% 2.82/1.01  --lt_threshold                          2000
% 2.82/1.01  --clause_weak_htbl                      true
% 2.82/1.01  --gc_record_bc_elim                     false
% 2.82/1.01  
% 2.82/1.01  ------ Preprocessing Options
% 2.82/1.01  
% 2.82/1.01  --preprocessing_flag                    true
% 2.82/1.01  --time_out_prep_mult                    0.1
% 2.82/1.01  --splitting_mode                        input
% 2.82/1.01  --splitting_grd                         true
% 2.82/1.01  --splitting_cvd                         false
% 2.82/1.01  --splitting_cvd_svl                     false
% 2.82/1.01  --splitting_nvd                         32
% 2.82/1.01  --sub_typing                            true
% 2.82/1.01  --prep_gs_sim                           true
% 2.82/1.01  --prep_unflatten                        true
% 2.82/1.01  --prep_res_sim                          true
% 2.82/1.01  --prep_upred                            true
% 2.82/1.01  --prep_sem_filter                       exhaustive
% 2.82/1.01  --prep_sem_filter_out                   false
% 2.82/1.01  --pred_elim                             true
% 2.82/1.01  --res_sim_input                         true
% 2.82/1.01  --eq_ax_congr_red                       true
% 2.82/1.01  --pure_diseq_elim                       true
% 2.82/1.01  --brand_transform                       false
% 2.82/1.01  --non_eq_to_eq                          false
% 2.82/1.01  --prep_def_merge                        true
% 2.82/1.01  --prep_def_merge_prop_impl              false
% 2.82/1.01  --prep_def_merge_mbd                    true
% 2.82/1.01  --prep_def_merge_tr_red                 false
% 2.82/1.01  --prep_def_merge_tr_cl                  false
% 2.82/1.01  --smt_preprocessing                     true
% 2.82/1.01  --smt_ac_axioms                         fast
% 2.82/1.01  --preprocessed_out                      false
% 2.82/1.01  --preprocessed_stats                    false
% 2.82/1.01  
% 2.82/1.01  ------ Abstraction refinement Options
% 2.82/1.01  
% 2.82/1.01  --abstr_ref                             []
% 2.82/1.01  --abstr_ref_prep                        false
% 2.82/1.01  --abstr_ref_until_sat                   false
% 2.82/1.01  --abstr_ref_sig_restrict                funpre
% 2.82/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.82/1.01  --abstr_ref_under                       []
% 2.82/1.01  
% 2.82/1.01  ------ SAT Options
% 2.82/1.01  
% 2.82/1.01  --sat_mode                              false
% 2.82/1.01  --sat_fm_restart_options                ""
% 2.82/1.01  --sat_gr_def                            false
% 2.82/1.01  --sat_epr_types                         true
% 2.82/1.01  --sat_non_cyclic_types                  false
% 2.82/1.01  --sat_finite_models                     false
% 2.82/1.01  --sat_fm_lemmas                         false
% 2.82/1.01  --sat_fm_prep                           false
% 2.82/1.01  --sat_fm_uc_incr                        true
% 2.82/1.01  --sat_out_model                         small
% 2.82/1.01  --sat_out_clauses                       false
% 2.82/1.01  
% 2.82/1.01  ------ QBF Options
% 2.82/1.01  
% 2.82/1.01  --qbf_mode                              false
% 2.82/1.01  --qbf_elim_univ                         false
% 2.82/1.01  --qbf_dom_inst                          none
% 2.82/1.01  --qbf_dom_pre_inst                      false
% 2.82/1.01  --qbf_sk_in                             false
% 2.82/1.01  --qbf_pred_elim                         true
% 2.82/1.01  --qbf_split                             512
% 2.82/1.01  
% 2.82/1.01  ------ BMC1 Options
% 2.82/1.01  
% 2.82/1.01  --bmc1_incremental                      false
% 2.82/1.01  --bmc1_axioms                           reachable_all
% 2.82/1.01  --bmc1_min_bound                        0
% 2.82/1.01  --bmc1_max_bound                        -1
% 2.82/1.01  --bmc1_max_bound_default                -1
% 2.82/1.01  --bmc1_symbol_reachability              true
% 2.82/1.01  --bmc1_property_lemmas                  false
% 2.82/1.01  --bmc1_k_induction                      false
% 2.82/1.01  --bmc1_non_equiv_states                 false
% 2.82/1.01  --bmc1_deadlock                         false
% 2.82/1.01  --bmc1_ucm                              false
% 2.82/1.01  --bmc1_add_unsat_core                   none
% 2.82/1.01  --bmc1_unsat_core_children              false
% 2.82/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.82/1.01  --bmc1_out_stat                         full
% 2.82/1.01  --bmc1_ground_init                      false
% 2.82/1.01  --bmc1_pre_inst_next_state              false
% 2.82/1.01  --bmc1_pre_inst_state                   false
% 2.82/1.01  --bmc1_pre_inst_reach_state             false
% 2.82/1.01  --bmc1_out_unsat_core                   false
% 2.82/1.01  --bmc1_aig_witness_out                  false
% 2.82/1.01  --bmc1_verbose                          false
% 2.82/1.01  --bmc1_dump_clauses_tptp                false
% 2.82/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.82/1.01  --bmc1_dump_file                        -
% 2.82/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.82/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.82/1.01  --bmc1_ucm_extend_mode                  1
% 2.82/1.01  --bmc1_ucm_init_mode                    2
% 2.82/1.01  --bmc1_ucm_cone_mode                    none
% 2.82/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.82/1.01  --bmc1_ucm_relax_model                  4
% 2.82/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.82/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.82/1.01  --bmc1_ucm_layered_model                none
% 2.82/1.01  --bmc1_ucm_max_lemma_size               10
% 2.82/1.01  
% 2.82/1.01  ------ AIG Options
% 2.82/1.01  
% 2.82/1.01  --aig_mode                              false
% 2.82/1.01  
% 2.82/1.01  ------ Instantiation Options
% 2.82/1.01  
% 2.82/1.01  --instantiation_flag                    true
% 2.82/1.01  --inst_sos_flag                         false
% 2.82/1.01  --inst_sos_phase                        true
% 2.82/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.82/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.82/1.01  --inst_lit_sel_side                     num_symb
% 2.82/1.01  --inst_solver_per_active                1400
% 2.82/1.01  --inst_solver_calls_frac                1.
% 2.82/1.01  --inst_passive_queue_type               priority_queues
% 2.82/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.82/1.01  --inst_passive_queues_freq              [25;2]
% 2.82/1.01  --inst_dismatching                      true
% 2.82/1.01  --inst_eager_unprocessed_to_passive     true
% 2.82/1.01  --inst_prop_sim_given                   true
% 2.82/1.01  --inst_prop_sim_new                     false
% 2.82/1.01  --inst_subs_new                         false
% 2.82/1.01  --inst_eq_res_simp                      false
% 2.82/1.01  --inst_subs_given                       false
% 2.82/1.01  --inst_orphan_elimination               true
% 2.82/1.01  --inst_learning_loop_flag               true
% 2.82/1.01  --inst_learning_start                   3000
% 2.82/1.01  --inst_learning_factor                  2
% 2.82/1.01  --inst_start_prop_sim_after_learn       3
% 2.82/1.01  --inst_sel_renew                        solver
% 2.82/1.01  --inst_lit_activity_flag                true
% 2.82/1.01  --inst_restr_to_given                   false
% 2.82/1.01  --inst_activity_threshold               500
% 2.82/1.01  --inst_out_proof                        true
% 2.82/1.01  
% 2.82/1.01  ------ Resolution Options
% 2.82/1.01  
% 2.82/1.01  --resolution_flag                       true
% 2.82/1.01  --res_lit_sel                           adaptive
% 2.82/1.01  --res_lit_sel_side                      none
% 2.82/1.01  --res_ordering                          kbo
% 2.82/1.01  --res_to_prop_solver                    active
% 2.82/1.01  --res_prop_simpl_new                    false
% 2.82/1.01  --res_prop_simpl_given                  true
% 2.82/1.01  --res_passive_queue_type                priority_queues
% 2.82/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.82/1.01  --res_passive_queues_freq               [15;5]
% 2.82/1.01  --res_forward_subs                      full
% 2.82/1.01  --res_backward_subs                     full
% 2.82/1.01  --res_forward_subs_resolution           true
% 2.82/1.01  --res_backward_subs_resolution          true
% 2.82/1.01  --res_orphan_elimination                true
% 2.82/1.01  --res_time_limit                        2.
% 2.82/1.01  --res_out_proof                         true
% 2.82/1.01  
% 2.82/1.01  ------ Superposition Options
% 2.82/1.01  
% 2.82/1.01  --superposition_flag                    true
% 2.82/1.01  --sup_passive_queue_type                priority_queues
% 2.82/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.82/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.82/1.01  --demod_completeness_check              fast
% 2.82/1.01  --demod_use_ground                      true
% 2.82/1.01  --sup_to_prop_solver                    passive
% 2.82/1.01  --sup_prop_simpl_new                    true
% 2.82/1.01  --sup_prop_simpl_given                  true
% 2.82/1.01  --sup_fun_splitting                     false
% 2.82/1.01  --sup_smt_interval                      50000
% 2.82/1.01  
% 2.82/1.01  ------ Superposition Simplification Setup
% 2.82/1.01  
% 2.82/1.01  --sup_indices_passive                   []
% 2.82/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.82/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/1.01  --sup_full_bw                           [BwDemod]
% 2.82/1.01  --sup_immed_triv                        [TrivRules]
% 2.82/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.82/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/1.01  --sup_immed_bw_main                     []
% 2.82/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.82/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.82/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.82/1.01  
% 2.82/1.01  ------ Combination Options
% 2.82/1.01  
% 2.82/1.01  --comb_res_mult                         3
% 2.82/1.01  --comb_sup_mult                         2
% 2.82/1.01  --comb_inst_mult                        10
% 2.82/1.01  
% 2.82/1.01  ------ Debug Options
% 2.82/1.01  
% 2.82/1.01  --dbg_backtrace                         false
% 2.82/1.01  --dbg_dump_prop_clauses                 false
% 2.82/1.01  --dbg_dump_prop_clauses_file            -
% 2.82/1.01  --dbg_out_stat                          false
% 2.82/1.01  ------ Parsing...
% 2.82/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.82/1.01  
% 2.82/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.82/1.01  
% 2.82/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.82/1.01  
% 2.82/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.82/1.01  ------ Proving...
% 2.82/1.01  ------ Problem Properties 
% 2.82/1.01  
% 2.82/1.01  
% 2.82/1.01  clauses                                 18
% 2.82/1.01  conjectures                             9
% 2.82/1.01  EPR                                     7
% 2.82/1.01  Horn                                    16
% 2.82/1.01  unary                                   10
% 2.82/1.01  binary                                  3
% 2.82/1.01  lits                                    50
% 2.82/1.01  lits eq                                 6
% 2.82/1.01  fd_pure                                 0
% 2.82/1.01  fd_pseudo                               0
% 2.82/1.01  fd_cond                                 1
% 2.82/1.01  fd_pseudo_cond                          0
% 2.82/1.01  AC symbols                              0
% 2.82/1.01  
% 2.82/1.01  ------ Schedule dynamic 5 is on 
% 2.82/1.01  
% 2.82/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.82/1.01  
% 2.82/1.01  
% 2.82/1.01  ------ 
% 2.82/1.01  Current options:
% 2.82/1.01  ------ 
% 2.82/1.01  
% 2.82/1.01  ------ Input Options
% 2.82/1.01  
% 2.82/1.01  --out_options                           all
% 2.82/1.01  --tptp_safe_out                         true
% 2.82/1.01  --problem_path                          ""
% 2.82/1.01  --include_path                          ""
% 2.82/1.01  --clausifier                            res/vclausify_rel
% 2.82/1.01  --clausifier_options                    --mode clausify
% 2.82/1.01  --stdin                                 false
% 2.82/1.01  --stats_out                             all
% 2.82/1.01  
% 2.82/1.01  ------ General Options
% 2.82/1.01  
% 2.82/1.01  --fof                                   false
% 2.82/1.01  --time_out_real                         305.
% 2.82/1.01  --time_out_virtual                      -1.
% 2.82/1.01  --symbol_type_check                     false
% 2.82/1.01  --clausify_out                          false
% 2.82/1.01  --sig_cnt_out                           false
% 2.82/1.01  --trig_cnt_out                          false
% 2.82/1.01  --trig_cnt_out_tolerance                1.
% 2.82/1.01  --trig_cnt_out_sk_spl                   false
% 2.82/1.01  --abstr_cl_out                          false
% 2.82/1.01  
% 2.82/1.01  ------ Global Options
% 2.82/1.01  
% 2.82/1.01  --schedule                              default
% 2.82/1.01  --add_important_lit                     false
% 2.82/1.01  --prop_solver_per_cl                    1000
% 2.82/1.01  --min_unsat_core                        false
% 2.82/1.01  --soft_assumptions                      false
% 2.82/1.01  --soft_lemma_size                       3
% 2.82/1.01  --prop_impl_unit_size                   0
% 2.82/1.01  --prop_impl_unit                        []
% 2.82/1.01  --share_sel_clauses                     true
% 2.82/1.01  --reset_solvers                         false
% 2.82/1.01  --bc_imp_inh                            [conj_cone]
% 2.82/1.01  --conj_cone_tolerance                   3.
% 2.82/1.01  --extra_neg_conj                        none
% 2.82/1.01  --large_theory_mode                     true
% 2.82/1.01  --prolific_symb_bound                   200
% 2.82/1.01  --lt_threshold                          2000
% 2.82/1.01  --clause_weak_htbl                      true
% 2.82/1.01  --gc_record_bc_elim                     false
% 2.82/1.01  
% 2.82/1.01  ------ Preprocessing Options
% 2.82/1.01  
% 2.82/1.01  --preprocessing_flag                    true
% 2.82/1.01  --time_out_prep_mult                    0.1
% 2.82/1.01  --splitting_mode                        input
% 2.82/1.01  --splitting_grd                         true
% 2.82/1.01  --splitting_cvd                         false
% 2.82/1.01  --splitting_cvd_svl                     false
% 2.82/1.01  --splitting_nvd                         32
% 2.82/1.01  --sub_typing                            true
% 2.82/1.01  --prep_gs_sim                           true
% 2.82/1.01  --prep_unflatten                        true
% 2.82/1.01  --prep_res_sim                          true
% 2.82/1.01  --prep_upred                            true
% 2.82/1.01  --prep_sem_filter                       exhaustive
% 2.82/1.01  --prep_sem_filter_out                   false
% 2.82/1.01  --pred_elim                             true
% 2.82/1.01  --res_sim_input                         true
% 2.82/1.01  --eq_ax_congr_red                       true
% 2.82/1.01  --pure_diseq_elim                       true
% 2.82/1.01  --brand_transform                       false
% 2.82/1.01  --non_eq_to_eq                          false
% 2.82/1.01  --prep_def_merge                        true
% 2.82/1.01  --prep_def_merge_prop_impl              false
% 2.82/1.01  --prep_def_merge_mbd                    true
% 2.82/1.01  --prep_def_merge_tr_red                 false
% 2.82/1.01  --prep_def_merge_tr_cl                  false
% 2.82/1.01  --smt_preprocessing                     true
% 2.82/1.01  --smt_ac_axioms                         fast
% 2.82/1.01  --preprocessed_out                      false
% 2.82/1.01  --preprocessed_stats                    false
% 2.82/1.01  
% 2.82/1.01  ------ Abstraction refinement Options
% 2.82/1.01  
% 2.82/1.01  --abstr_ref                             []
% 2.82/1.01  --abstr_ref_prep                        false
% 2.82/1.01  --abstr_ref_until_sat                   false
% 2.82/1.01  --abstr_ref_sig_restrict                funpre
% 2.82/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.82/1.01  --abstr_ref_under                       []
% 2.82/1.01  
% 2.82/1.01  ------ SAT Options
% 2.82/1.01  
% 2.82/1.01  --sat_mode                              false
% 2.82/1.01  --sat_fm_restart_options                ""
% 2.82/1.01  --sat_gr_def                            false
% 2.82/1.01  --sat_epr_types                         true
% 2.82/1.01  --sat_non_cyclic_types                  false
% 2.82/1.01  --sat_finite_models                     false
% 2.82/1.01  --sat_fm_lemmas                         false
% 2.82/1.01  --sat_fm_prep                           false
% 2.82/1.01  --sat_fm_uc_incr                        true
% 2.82/1.01  --sat_out_model                         small
% 2.82/1.01  --sat_out_clauses                       false
% 2.82/1.01  
% 2.82/1.01  ------ QBF Options
% 2.82/1.01  
% 2.82/1.01  --qbf_mode                              false
% 2.82/1.01  --qbf_elim_univ                         false
% 2.82/1.01  --qbf_dom_inst                          none
% 2.82/1.01  --qbf_dom_pre_inst                      false
% 2.82/1.01  --qbf_sk_in                             false
% 2.82/1.01  --qbf_pred_elim                         true
% 2.82/1.01  --qbf_split                             512
% 2.82/1.01  
% 2.82/1.01  ------ BMC1 Options
% 2.82/1.01  
% 2.82/1.01  --bmc1_incremental                      false
% 2.82/1.01  --bmc1_axioms                           reachable_all
% 2.82/1.01  --bmc1_min_bound                        0
% 2.82/1.01  --bmc1_max_bound                        -1
% 2.82/1.01  --bmc1_max_bound_default                -1
% 2.82/1.01  --bmc1_symbol_reachability              true
% 2.82/1.01  --bmc1_property_lemmas                  false
% 2.82/1.01  --bmc1_k_induction                      false
% 2.82/1.01  --bmc1_non_equiv_states                 false
% 2.82/1.01  --bmc1_deadlock                         false
% 2.82/1.01  --bmc1_ucm                              false
% 2.82/1.01  --bmc1_add_unsat_core                   none
% 2.82/1.01  --bmc1_unsat_core_children              false
% 2.82/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.82/1.01  --bmc1_out_stat                         full
% 2.82/1.01  --bmc1_ground_init                      false
% 2.82/1.01  --bmc1_pre_inst_next_state              false
% 2.82/1.01  --bmc1_pre_inst_state                   false
% 2.82/1.01  --bmc1_pre_inst_reach_state             false
% 2.82/1.01  --bmc1_out_unsat_core                   false
% 2.82/1.01  --bmc1_aig_witness_out                  false
% 2.82/1.01  --bmc1_verbose                          false
% 2.82/1.01  --bmc1_dump_clauses_tptp                false
% 2.82/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.82/1.01  --bmc1_dump_file                        -
% 2.82/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.82/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.82/1.01  --bmc1_ucm_extend_mode                  1
% 2.82/1.01  --bmc1_ucm_init_mode                    2
% 2.82/1.01  --bmc1_ucm_cone_mode                    none
% 2.82/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.82/1.01  --bmc1_ucm_relax_model                  4
% 2.82/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.82/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.82/1.01  --bmc1_ucm_layered_model                none
% 2.82/1.01  --bmc1_ucm_max_lemma_size               10
% 2.82/1.01  
% 2.82/1.01  ------ AIG Options
% 2.82/1.01  
% 2.82/1.01  --aig_mode                              false
% 2.82/1.01  
% 2.82/1.01  ------ Instantiation Options
% 2.82/1.01  
% 2.82/1.01  --instantiation_flag                    true
% 2.82/1.01  --inst_sos_flag                         false
% 2.82/1.01  --inst_sos_phase                        true
% 2.82/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.82/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.82/1.01  --inst_lit_sel_side                     none
% 2.82/1.01  --inst_solver_per_active                1400
% 2.82/1.01  --inst_solver_calls_frac                1.
% 2.82/1.01  --inst_passive_queue_type               priority_queues
% 2.82/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.82/1.01  --inst_passive_queues_freq              [25;2]
% 2.82/1.01  --inst_dismatching                      true
% 2.82/1.01  --inst_eager_unprocessed_to_passive     true
% 2.82/1.01  --inst_prop_sim_given                   true
% 2.82/1.01  --inst_prop_sim_new                     false
% 2.82/1.01  --inst_subs_new                         false
% 2.82/1.01  --inst_eq_res_simp                      false
% 2.82/1.01  --inst_subs_given                       false
% 2.82/1.01  --inst_orphan_elimination               true
% 2.82/1.01  --inst_learning_loop_flag               true
% 2.82/1.01  --inst_learning_start                   3000
% 2.82/1.01  --inst_learning_factor                  2
% 2.82/1.01  --inst_start_prop_sim_after_learn       3
% 2.82/1.01  --inst_sel_renew                        solver
% 2.82/1.01  --inst_lit_activity_flag                true
% 2.82/1.01  --inst_restr_to_given                   false
% 2.82/1.01  --inst_activity_threshold               500
% 2.82/1.01  --inst_out_proof                        true
% 2.82/1.01  
% 2.82/1.01  ------ Resolution Options
% 2.82/1.01  
% 2.82/1.01  --resolution_flag                       false
% 2.82/1.01  --res_lit_sel                           adaptive
% 2.82/1.01  --res_lit_sel_side                      none
% 2.82/1.01  --res_ordering                          kbo
% 2.82/1.01  --res_to_prop_solver                    active
% 2.82/1.01  --res_prop_simpl_new                    false
% 2.82/1.01  --res_prop_simpl_given                  true
% 2.82/1.01  --res_passive_queue_type                priority_queues
% 2.82/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.82/1.01  --res_passive_queues_freq               [15;5]
% 2.82/1.01  --res_forward_subs                      full
% 2.82/1.01  --res_backward_subs                     full
% 2.82/1.01  --res_forward_subs_resolution           true
% 2.82/1.01  --res_backward_subs_resolution          true
% 2.82/1.01  --res_orphan_elimination                true
% 2.82/1.01  --res_time_limit                        2.
% 2.82/1.01  --res_out_proof                         true
% 2.82/1.01  
% 2.82/1.01  ------ Superposition Options
% 2.82/1.01  
% 2.82/1.01  --superposition_flag                    true
% 2.82/1.01  --sup_passive_queue_type                priority_queues
% 2.82/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.82/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.82/1.01  --demod_completeness_check              fast
% 2.82/1.01  --demod_use_ground                      true
% 2.82/1.01  --sup_to_prop_solver                    passive
% 2.82/1.01  --sup_prop_simpl_new                    true
% 2.82/1.01  --sup_prop_simpl_given                  true
% 2.82/1.01  --sup_fun_splitting                     false
% 2.82/1.01  --sup_smt_interval                      50000
% 2.82/1.01  
% 2.82/1.01  ------ Superposition Simplification Setup
% 2.82/1.01  
% 2.82/1.01  --sup_indices_passive                   []
% 2.82/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.82/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/1.01  --sup_full_bw                           [BwDemod]
% 2.82/1.01  --sup_immed_triv                        [TrivRules]
% 2.82/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.82/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/1.01  --sup_immed_bw_main                     []
% 2.82/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.82/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.82/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.82/1.01  
% 2.82/1.01  ------ Combination Options
% 2.82/1.01  
% 2.82/1.01  --comb_res_mult                         3
% 2.82/1.01  --comb_sup_mult                         2
% 2.82/1.01  --comb_inst_mult                        10
% 2.82/1.01  
% 2.82/1.01  ------ Debug Options
% 2.82/1.01  
% 2.82/1.01  --dbg_backtrace                         false
% 2.82/1.01  --dbg_dump_prop_clauses                 false
% 2.82/1.01  --dbg_dump_prop_clauses_file            -
% 2.82/1.01  --dbg_out_stat                          false
% 2.82/1.01  
% 2.82/1.01  
% 2.82/1.01  
% 2.82/1.01  
% 2.82/1.01  ------ Proving...
% 2.82/1.01  
% 2.82/1.01  
% 2.82/1.01  % SZS status Theorem for theBenchmark.p
% 2.82/1.01  
% 2.82/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.82/1.01  
% 2.82/1.01  fof(f11,conjecture,(
% 2.82/1.01    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 2.82/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/1.02  
% 2.82/1.02  fof(f12,negated_conjecture,(
% 2.82/1.02    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 2.82/1.02    inference(negated_conjecture,[],[f11])).
% 2.82/1.02  
% 2.82/1.02  fof(f28,plain,(
% 2.82/1.02    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : ((k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0)) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.82/1.02    inference(ennf_transformation,[],[f12])).
% 2.82/1.02  
% 2.82/1.02  fof(f29,plain,(
% 2.82/1.02    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.82/1.02    inference(flattening,[],[f28])).
% 2.82/1.02  
% 2.82/1.02  fof(f35,plain,(
% 2.82/1.02    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) => (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),sK5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,sK5)) & v1_partfun1(X4,X0) & m1_subset_1(sK5,X1))) )),
% 2.82/1.02    introduced(choice_axiom,[])).
% 2.82/1.02  
% 2.82/1.02  fof(f34,plain,(
% 2.82/1.02    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,sK4),X5) != k1_funct_1(sK4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(sK4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(sK4))) )),
% 2.82/1.02    introduced(choice_axiom,[])).
% 2.82/1.02  
% 2.82/1.02  fof(f33,plain,(
% 2.82/1.02    ( ! [X0,X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k3_funct_2(X1,sK2,k8_funct_2(X1,X0,sK2,sK3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,sK3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 2.82/1.02    introduced(choice_axiom,[])).
% 2.82/1.02  
% 2.82/1.02  fof(f32,plain,(
% 2.82/1.02    ( ! [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) => (? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(sK1,X2,k8_funct_2(sK1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(sK1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) & v1_funct_2(X3,sK1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(sK1))) )),
% 2.82/1.02    introduced(choice_axiom,[])).
% 2.82/1.02  
% 2.82/1.02  fof(f31,plain,(
% 2.82/1.02    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,sK0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,sK0,X3,X5)) & v1_partfun1(X4,sK0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) & v1_funct_2(X3,X1,sK0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 2.82/1.02    introduced(choice_axiom,[])).
% 2.82/1.02  
% 2.82/1.02  fof(f36,plain,(
% 2.82/1.02    ((((k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) & v1_partfun1(sK4,sK0) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 2.82/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f29,f35,f34,f33,f32,f31])).
% 2.82/1.02  
% 2.82/1.02  fof(f57,plain,(
% 2.82/1.02    m1_subset_1(sK5,sK1)),
% 2.82/1.02    inference(cnf_transformation,[],[f36])).
% 2.82/1.02  
% 2.82/1.02  fof(f56,plain,(
% 2.82/1.02    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 2.82/1.02    inference(cnf_transformation,[],[f36])).
% 2.82/1.02  
% 2.82/1.02  fof(f54,plain,(
% 2.82/1.02    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.82/1.02    inference(cnf_transformation,[],[f36])).
% 2.82/1.02  
% 2.82/1.02  fof(f8,axiom,(
% 2.82/1.02    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))))),
% 2.82/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/1.02  
% 2.82/1.02  fof(f22,plain,(
% 2.82/1.02    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.82/1.02    inference(ennf_transformation,[],[f8])).
% 2.82/1.02  
% 2.82/1.02  fof(f23,plain,(
% 2.82/1.02    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.82/1.02    inference(flattening,[],[f22])).
% 2.82/1.02  
% 2.82/1.02  fof(f47,plain,(
% 2.82/1.02    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.82/1.02    inference(cnf_transformation,[],[f23])).
% 2.82/1.02  
% 2.82/1.02  fof(f9,axiom,(
% 2.82/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 2.82/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/1.02  
% 2.82/1.02  fof(f24,plain,(
% 2.82/1.02    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 2.82/1.02    inference(ennf_transformation,[],[f9])).
% 2.82/1.02  
% 2.82/1.02  fof(f25,plain,(
% 2.82/1.02    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 2.82/1.02    inference(flattening,[],[f24])).
% 2.82/1.02  
% 2.82/1.02  fof(f48,plain,(
% 2.82/1.02    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 2.82/1.02    inference(cnf_transformation,[],[f25])).
% 2.82/1.02  
% 2.82/1.02  fof(f45,plain,(
% 2.82/1.02    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.82/1.02    inference(cnf_transformation,[],[f23])).
% 2.82/1.02  
% 2.82/1.02  fof(f46,plain,(
% 2.82/1.02    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.82/1.02    inference(cnf_transformation,[],[f23])).
% 2.82/1.02  
% 2.82/1.02  fof(f51,plain,(
% 2.82/1.02    ~v1_xboole_0(sK1)),
% 2.82/1.02    inference(cnf_transformation,[],[f36])).
% 2.82/1.02  
% 2.82/1.02  fof(f52,plain,(
% 2.82/1.02    v1_funct_1(sK3)),
% 2.82/1.02    inference(cnf_transformation,[],[f36])).
% 2.82/1.02  
% 2.82/1.02  fof(f53,plain,(
% 2.82/1.02    v1_funct_2(sK3,sK1,sK0)),
% 2.82/1.02    inference(cnf_transformation,[],[f36])).
% 2.82/1.02  
% 2.82/1.02  fof(f55,plain,(
% 2.82/1.02    v1_funct_1(sK4)),
% 2.82/1.02    inference(cnf_transformation,[],[f36])).
% 2.82/1.02  
% 2.82/1.02  fof(f59,plain,(
% 2.82/1.02    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 2.82/1.02    inference(cnf_transformation,[],[f36])).
% 2.82/1.02  
% 2.82/1.02  fof(f4,axiom,(
% 2.82/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.82/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/1.02  
% 2.82/1.02  fof(f14,plain,(
% 2.82/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.82/1.02    inference(pure_predicate_removal,[],[f4])).
% 2.82/1.02  
% 2.82/1.02  fof(f17,plain,(
% 2.82/1.02    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.82/1.02    inference(ennf_transformation,[],[f14])).
% 2.82/1.02  
% 2.82/1.02  fof(f40,plain,(
% 2.82/1.02    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.82/1.02    inference(cnf_transformation,[],[f17])).
% 2.82/1.02  
% 2.82/1.02  fof(f7,axiom,(
% 2.82/1.02    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.82/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/1.02  
% 2.82/1.02  fof(f20,plain,(
% 2.82/1.02    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.82/1.02    inference(ennf_transformation,[],[f7])).
% 2.82/1.02  
% 2.82/1.02  fof(f21,plain,(
% 2.82/1.02    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.82/1.02    inference(flattening,[],[f20])).
% 2.82/1.02  
% 2.82/1.02  fof(f30,plain,(
% 2.82/1.02    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.82/1.02    inference(nnf_transformation,[],[f21])).
% 2.82/1.02  
% 2.82/1.02  fof(f43,plain,(
% 2.82/1.02    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.82/1.02    inference(cnf_transformation,[],[f30])).
% 2.82/1.02  
% 2.82/1.02  fof(f3,axiom,(
% 2.82/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.82/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/1.02  
% 2.82/1.02  fof(f16,plain,(
% 2.82/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.82/1.02    inference(ennf_transformation,[],[f3])).
% 2.82/1.02  
% 2.82/1.02  fof(f39,plain,(
% 2.82/1.02    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.82/1.02    inference(cnf_transformation,[],[f16])).
% 2.82/1.02  
% 2.82/1.02  fof(f58,plain,(
% 2.82/1.02    v1_partfun1(sK4,sK0)),
% 2.82/1.02    inference(cnf_transformation,[],[f36])).
% 2.82/1.02  
% 2.82/1.02  fof(f6,axiom,(
% 2.82/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.82/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/1.02  
% 2.82/1.02  fof(f19,plain,(
% 2.82/1.02    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.82/1.02    inference(ennf_transformation,[],[f6])).
% 2.82/1.02  
% 2.82/1.02  fof(f42,plain,(
% 2.82/1.02    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.82/1.02    inference(cnf_transformation,[],[f19])).
% 2.82/1.02  
% 2.82/1.02  fof(f2,axiom,(
% 2.82/1.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.82/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/1.02  
% 2.82/1.02  fof(f13,plain,(
% 2.82/1.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 2.82/1.02    inference(unused_predicate_definition_removal,[],[f2])).
% 2.82/1.02  
% 2.82/1.02  fof(f15,plain,(
% 2.82/1.02    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 2.82/1.02    inference(ennf_transformation,[],[f13])).
% 2.82/1.02  
% 2.82/1.02  fof(f38,plain,(
% 2.82/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.82/1.02    inference(cnf_transformation,[],[f15])).
% 2.82/1.02  
% 2.82/1.02  fof(f10,axiom,(
% 2.82/1.02    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 2.82/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/1.02  
% 2.82/1.02  fof(f26,plain,(
% 2.82/1.02    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 2.82/1.02    inference(ennf_transformation,[],[f10])).
% 2.82/1.02  
% 2.82/1.02  fof(f27,plain,(
% 2.82/1.02    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 2.82/1.02    inference(flattening,[],[f26])).
% 2.82/1.02  
% 2.82/1.02  fof(f49,plain,(
% 2.82/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 2.82/1.02    inference(cnf_transformation,[],[f27])).
% 2.82/1.02  
% 2.82/1.02  fof(f5,axiom,(
% 2.82/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 2.82/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/1.02  
% 2.82/1.02  fof(f18,plain,(
% 2.82/1.02    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.82/1.02    inference(ennf_transformation,[],[f5])).
% 2.82/1.02  
% 2.82/1.02  fof(f41,plain,(
% 2.82/1.02    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.82/1.02    inference(cnf_transformation,[],[f18])).
% 2.82/1.02  
% 2.82/1.02  fof(f1,axiom,(
% 2.82/1.02    v1_xboole_0(k1_xboole_0)),
% 2.82/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/1.02  
% 2.82/1.02  fof(f37,plain,(
% 2.82/1.02    v1_xboole_0(k1_xboole_0)),
% 2.82/1.02    inference(cnf_transformation,[],[f1])).
% 2.82/1.02  
% 2.82/1.02  fof(f50,plain,(
% 2.82/1.02    ~v1_xboole_0(sK0)),
% 2.82/1.02    inference(cnf_transformation,[],[f36])).
% 2.82/1.02  
% 2.82/1.02  cnf(c_814,plain,
% 2.82/1.02      ( ~ v1_xboole_0(X0_52) | v1_xboole_0(X1_52) | X1_52 != X0_52 ),
% 2.82/1.02      theory(equality) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_1310,plain,
% 2.82/1.02      ( v1_xboole_0(X0_52)
% 2.82/1.02      | ~ v1_xboole_0(k1_xboole_0)
% 2.82/1.02      | X0_52 != k1_xboole_0 ),
% 2.82/1.02      inference(instantiation,[status(thm)],[c_814]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_6822,plain,
% 2.82/1.02      ( v1_xboole_0(sK1)
% 2.82/1.02      | ~ v1_xboole_0(k1_xboole_0)
% 2.82/1.02      | sK1 != k1_xboole_0 ),
% 2.82/1.02      inference(instantiation,[status(thm)],[c_1310]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_813,plain,
% 2.82/1.02      ( X0_52 != X1_52 | X2_52 != X1_52 | X2_52 = X0_52 ),
% 2.82/1.02      theory(equality) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_1584,plain,
% 2.82/1.02      ( X0_52 != X1_52 | sK1 != X1_52 | sK1 = X0_52 ),
% 2.82/1.02      inference(instantiation,[status(thm)],[c_813]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_1902,plain,
% 2.82/1.02      ( X0_52 != sK1 | sK1 = X0_52 | sK1 != sK1 ),
% 2.82/1.02      inference(instantiation,[status(thm)],[c_1584]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_5253,plain,
% 2.82/1.02      ( sK1 != sK1 | sK1 = k1_xboole_0 | k1_xboole_0 != sK1 ),
% 2.82/1.02      inference(instantiation,[status(thm)],[c_1902]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_815,plain,
% 2.82/1.02      ( X0_52 != X1_52 | k1_zfmisc_1(X0_52) = k1_zfmisc_1(X1_52) ),
% 2.82/1.02      theory(equality) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_1550,plain,
% 2.82/1.02      ( X0_52 != sK0 | k1_zfmisc_1(X0_52) = k1_zfmisc_1(sK0) ),
% 2.82/1.02      inference(instantiation,[status(thm)],[c_815]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_4191,plain,
% 2.82/1.02      ( k1_relset_1(sK0,sK2,sK4) != sK0
% 2.82/1.02      | k1_zfmisc_1(k1_relset_1(sK0,sK2,sK4)) = k1_zfmisc_1(sK0) ),
% 2.82/1.02      inference(instantiation,[status(thm)],[c_1550]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_15,negated_conjecture,
% 2.82/1.02      ( m1_subset_1(sK5,sK1) ),
% 2.82/1.02      inference(cnf_transformation,[],[f57]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_800,negated_conjecture,
% 2.82/1.02      ( m1_subset_1(sK5,sK1) ),
% 2.82/1.02      inference(subtyping,[status(esa)],[c_15]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_1156,plain,
% 2.82/1.02      ( m1_subset_1(sK5,sK1) = iProver_top ),
% 2.82/1.02      inference(predicate_to_equality,[status(thm)],[c_800]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_16,negated_conjecture,
% 2.82/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 2.82/1.02      inference(cnf_transformation,[],[f56]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_799,negated_conjecture,
% 2.82/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 2.82/1.02      inference(subtyping,[status(esa)],[c_16]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_1157,plain,
% 2.82/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
% 2.82/1.02      inference(predicate_to_equality,[status(thm)],[c_799]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_18,negated_conjecture,
% 2.82/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 2.82/1.02      inference(cnf_transformation,[],[f54]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_797,negated_conjecture,
% 2.82/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 2.82/1.02      inference(subtyping,[status(esa)],[c_18]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_1159,plain,
% 2.82/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.82/1.02      inference(predicate_to_equality,[status(thm)],[c_797]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_8,plain,
% 2.82/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.82/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 2.82/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.82/1.02      | m1_subset_1(k8_funct_2(X1,X2,X4,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
% 2.82/1.02      | ~ v1_funct_1(X3)
% 2.82/1.02      | ~ v1_funct_1(X0) ),
% 2.82/1.02      inference(cnf_transformation,[],[f47]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_805,plain,
% 2.82/1.02      ( ~ v1_funct_2(X0_51,X0_52,X1_52)
% 2.82/1.02      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 2.82/1.02      | ~ m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
% 2.82/1.02      | m1_subset_1(k8_funct_2(X0_52,X1_52,X2_52,X0_51,X1_51),k1_zfmisc_1(k2_zfmisc_1(X0_52,X2_52)))
% 2.82/1.02      | ~ v1_funct_1(X0_51)
% 2.82/1.02      | ~ v1_funct_1(X1_51) ),
% 2.82/1.02      inference(subtyping,[status(esa)],[c_8]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_1152,plain,
% 2.82/1.02      ( v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
% 2.82/1.02      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 2.82/1.02      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52))) != iProver_top
% 2.82/1.02      | m1_subset_1(k8_funct_2(X0_52,X1_52,X2_52,X0_51,X1_51),k1_zfmisc_1(k2_zfmisc_1(X0_52,X2_52))) = iProver_top
% 2.82/1.02      | v1_funct_1(X0_51) != iProver_top
% 2.82/1.02      | v1_funct_1(X1_51) != iProver_top ),
% 2.82/1.02      inference(predicate_to_equality,[status(thm)],[c_805]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_11,plain,
% 2.82/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.82/1.02      | ~ m1_subset_1(X3,X1)
% 2.82/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.82/1.02      | ~ v1_funct_1(X0)
% 2.82/1.02      | v1_xboole_0(X1)
% 2.82/1.02      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 2.82/1.02      inference(cnf_transformation,[],[f48]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_802,plain,
% 2.82/1.02      ( ~ v1_funct_2(X0_51,X0_52,X1_52)
% 2.82/1.02      | ~ m1_subset_1(X1_51,X0_52)
% 2.82/1.02      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 2.82/1.02      | ~ v1_funct_1(X0_51)
% 2.82/1.02      | v1_xboole_0(X0_52)
% 2.82/1.02      | k3_funct_2(X0_52,X1_52,X0_51,X1_51) = k1_funct_1(X0_51,X1_51) ),
% 2.82/1.02      inference(subtyping,[status(esa)],[c_11]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_1155,plain,
% 2.82/1.02      ( k3_funct_2(X0_52,X1_52,X0_51,X1_51) = k1_funct_1(X0_51,X1_51)
% 2.82/1.02      | v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
% 2.82/1.02      | m1_subset_1(X1_51,X0_52) != iProver_top
% 2.82/1.02      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 2.82/1.02      | v1_funct_1(X0_51) != iProver_top
% 2.82/1.02      | v1_xboole_0(X0_52) = iProver_top ),
% 2.82/1.02      inference(predicate_to_equality,[status(thm)],[c_802]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_1912,plain,
% 2.82/1.02      ( k3_funct_2(X0_52,X1_52,k8_funct_2(X0_52,X2_52,X1_52,X0_51,X1_51),X2_51) = k1_funct_1(k8_funct_2(X0_52,X2_52,X1_52,X0_51,X1_51),X2_51)
% 2.82/1.02      | v1_funct_2(X0_51,X0_52,X2_52) != iProver_top
% 2.82/1.02      | v1_funct_2(k8_funct_2(X0_52,X2_52,X1_52,X0_51,X1_51),X0_52,X1_52) != iProver_top
% 2.82/1.02      | m1_subset_1(X2_51,X0_52) != iProver_top
% 2.82/1.02      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X2_52))) != iProver_top
% 2.82/1.02      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X2_52,X1_52))) != iProver_top
% 2.82/1.02      | v1_funct_1(X0_51) != iProver_top
% 2.82/1.02      | v1_funct_1(X1_51) != iProver_top
% 2.82/1.02      | v1_funct_1(k8_funct_2(X0_52,X2_52,X1_52,X0_51,X1_51)) != iProver_top
% 2.82/1.02      | v1_xboole_0(X0_52) = iProver_top ),
% 2.82/1.02      inference(superposition,[status(thm)],[c_1152,c_1155]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_10,plain,
% 2.82/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.82/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 2.82/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.82/1.02      | ~ v1_funct_1(X3)
% 2.82/1.02      | ~ v1_funct_1(X0)
% 2.82/1.02      | v1_funct_1(k8_funct_2(X1,X2,X4,X0,X3)) ),
% 2.82/1.02      inference(cnf_transformation,[],[f45]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_803,plain,
% 2.82/1.02      ( ~ v1_funct_2(X0_51,X0_52,X1_52)
% 2.82/1.02      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 2.82/1.02      | ~ m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
% 2.82/1.02      | ~ v1_funct_1(X0_51)
% 2.82/1.02      | ~ v1_funct_1(X1_51)
% 2.82/1.02      | v1_funct_1(k8_funct_2(X0_52,X1_52,X2_52,X0_51,X1_51)) ),
% 2.82/1.02      inference(subtyping,[status(esa)],[c_10]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_1154,plain,
% 2.82/1.02      ( v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
% 2.82/1.02      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 2.82/1.02      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52))) != iProver_top
% 2.82/1.02      | v1_funct_1(X0_51) != iProver_top
% 2.82/1.02      | v1_funct_1(X1_51) != iProver_top
% 2.82/1.02      | v1_funct_1(k8_funct_2(X0_52,X1_52,X2_52,X0_51,X1_51)) = iProver_top ),
% 2.82/1.02      inference(predicate_to_equality,[status(thm)],[c_803]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_9,plain,
% 2.82/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.82/1.02      | v1_funct_2(k8_funct_2(X1,X2,X3,X0,X4),X1,X3)
% 2.82/1.02      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.82/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.82/1.02      | ~ v1_funct_1(X4)
% 2.82/1.02      | ~ v1_funct_1(X0) ),
% 2.82/1.02      inference(cnf_transformation,[],[f46]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_804,plain,
% 2.82/1.02      ( ~ v1_funct_2(X0_51,X0_52,X1_52)
% 2.82/1.02      | v1_funct_2(k8_funct_2(X0_52,X1_52,X2_52,X0_51,X1_51),X0_52,X2_52)
% 2.82/1.02      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 2.82/1.02      | ~ m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
% 2.82/1.02      | ~ v1_funct_1(X0_51)
% 2.82/1.02      | ~ v1_funct_1(X1_51) ),
% 2.82/1.02      inference(subtyping,[status(esa)],[c_9]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_1153,plain,
% 2.82/1.02      ( v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
% 2.82/1.02      | v1_funct_2(k8_funct_2(X0_52,X1_52,X2_52,X0_51,X1_51),X0_52,X2_52) = iProver_top
% 2.82/1.02      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 2.82/1.02      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52))) != iProver_top
% 2.82/1.02      | v1_funct_1(X0_51) != iProver_top
% 2.82/1.02      | v1_funct_1(X1_51) != iProver_top ),
% 2.82/1.02      inference(predicate_to_equality,[status(thm)],[c_804]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_3653,plain,
% 2.82/1.02      ( k3_funct_2(X0_52,X1_52,k8_funct_2(X0_52,X2_52,X1_52,X0_51,X1_51),X2_51) = k1_funct_1(k8_funct_2(X0_52,X2_52,X1_52,X0_51,X1_51),X2_51)
% 2.82/1.02      | v1_funct_2(X0_51,X0_52,X2_52) != iProver_top
% 2.82/1.02      | m1_subset_1(X2_51,X0_52) != iProver_top
% 2.82/1.02      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X2_52))) != iProver_top
% 2.82/1.02      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X2_52,X1_52))) != iProver_top
% 2.82/1.02      | v1_funct_1(X0_51) != iProver_top
% 2.82/1.02      | v1_funct_1(X1_51) != iProver_top
% 2.82/1.02      | v1_xboole_0(X0_52) = iProver_top ),
% 2.82/1.02      inference(forward_subsumption_resolution,
% 2.82/1.02                [status(thm)],
% 2.82/1.02                [c_1912,c_1154,c_1153]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_3658,plain,
% 2.82/1.02      ( k3_funct_2(sK1,X0_52,k8_funct_2(sK1,sK0,X0_52,sK3,X0_51),X1_51) = k1_funct_1(k8_funct_2(sK1,sK0,X0_52,sK3,X0_51),X1_51)
% 2.82/1.02      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 2.82/1.02      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_52))) != iProver_top
% 2.82/1.02      | m1_subset_1(X1_51,sK1) != iProver_top
% 2.82/1.02      | v1_funct_1(X0_51) != iProver_top
% 2.82/1.02      | v1_funct_1(sK3) != iProver_top
% 2.82/1.02      | v1_xboole_0(sK1) = iProver_top ),
% 2.82/1.02      inference(superposition,[status(thm)],[c_1159,c_3653]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_21,negated_conjecture,
% 2.82/1.02      ( ~ v1_xboole_0(sK1) ),
% 2.82/1.02      inference(cnf_transformation,[],[f51]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_24,plain,
% 2.82/1.02      ( v1_xboole_0(sK1) != iProver_top ),
% 2.82/1.02      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_20,negated_conjecture,
% 2.82/1.02      ( v1_funct_1(sK3) ),
% 2.82/1.02      inference(cnf_transformation,[],[f52]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_25,plain,
% 2.82/1.02      ( v1_funct_1(sK3) = iProver_top ),
% 2.82/1.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_19,negated_conjecture,
% 2.82/1.02      ( v1_funct_2(sK3,sK1,sK0) ),
% 2.82/1.02      inference(cnf_transformation,[],[f53]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_26,plain,
% 2.82/1.02      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 2.82/1.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_3841,plain,
% 2.82/1.02      ( k3_funct_2(sK1,X0_52,k8_funct_2(sK1,sK0,X0_52,sK3,X0_51),X1_51) = k1_funct_1(k8_funct_2(sK1,sK0,X0_52,sK3,X0_51),X1_51)
% 2.82/1.02      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_52))) != iProver_top
% 2.82/1.02      | m1_subset_1(X1_51,sK1) != iProver_top
% 2.82/1.02      | v1_funct_1(X0_51) != iProver_top ),
% 2.82/1.02      inference(global_propositional_subsumption,
% 2.82/1.02                [status(thm)],
% 2.82/1.02                [c_3658,c_24,c_25,c_26]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_3851,plain,
% 2.82/1.02      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0_51) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0_51)
% 2.82/1.02      | m1_subset_1(X0_51,sK1) != iProver_top
% 2.82/1.02      | v1_funct_1(sK4) != iProver_top ),
% 2.82/1.02      inference(superposition,[status(thm)],[c_1157,c_3841]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_17,negated_conjecture,
% 2.82/1.02      ( v1_funct_1(sK4) ),
% 2.82/1.02      inference(cnf_transformation,[],[f55]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_28,plain,
% 2.82/1.02      ( v1_funct_1(sK4) = iProver_top ),
% 2.82/1.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_3934,plain,
% 2.82/1.02      ( m1_subset_1(X0_51,sK1) != iProver_top
% 2.82/1.02      | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0_51) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0_51) ),
% 2.82/1.02      inference(global_propositional_subsumption,
% 2.82/1.02                [status(thm)],
% 2.82/1.02                [c_3851,c_28]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_3935,plain,
% 2.82/1.02      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0_51) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0_51)
% 2.82/1.02      | m1_subset_1(X0_51,sK1) != iProver_top ),
% 2.82/1.02      inference(renaming,[status(thm)],[c_3934]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_3942,plain,
% 2.82/1.02      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) ),
% 2.82/1.02      inference(superposition,[status(thm)],[c_1156,c_3935]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_1597,plain,
% 2.82/1.02      ( k3_funct_2(sK1,sK0,sK3,X0_51) = k1_funct_1(sK3,X0_51)
% 2.82/1.02      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 2.82/1.02      | m1_subset_1(X0_51,sK1) != iProver_top
% 2.82/1.02      | v1_funct_1(sK3) != iProver_top
% 2.82/1.02      | v1_xboole_0(sK1) = iProver_top ),
% 2.82/1.02      inference(superposition,[status(thm)],[c_1159,c_1155]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_1781,plain,
% 2.82/1.02      ( k3_funct_2(sK1,sK0,sK3,X0_51) = k1_funct_1(sK3,X0_51)
% 2.82/1.02      | m1_subset_1(X0_51,sK1) != iProver_top ),
% 2.82/1.02      inference(global_propositional_subsumption,
% 2.82/1.02                [status(thm)],
% 2.82/1.02                [c_1597,c_24,c_25,c_26]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_1789,plain,
% 2.82/1.02      ( k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) ),
% 2.82/1.02      inference(superposition,[status(thm)],[c_1156,c_1781]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_13,negated_conjecture,
% 2.82/1.02      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
% 2.82/1.02      inference(cnf_transformation,[],[f59]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_801,negated_conjecture,
% 2.82/1.02      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
% 2.82/1.02      inference(subtyping,[status(esa)],[c_13]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_1864,plain,
% 2.82/1.02      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 2.82/1.02      inference(demodulation,[status(thm)],[c_1789,c_801]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_3944,plain,
% 2.82/1.02      ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 2.82/1.02      inference(demodulation,[status(thm)],[c_3942,c_1864]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_816,plain,
% 2.82/1.02      ( ~ m1_subset_1(X0_51,X0_52)
% 2.82/1.02      | m1_subset_1(X1_51,X1_52)
% 2.82/1.02      | X1_52 != X0_52
% 2.82/1.02      | X1_51 != X0_51 ),
% 2.82/1.02      theory(equality) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_1427,plain,
% 2.82/1.02      ( m1_subset_1(X0_51,X0_52)
% 2.82/1.02      | ~ m1_subset_1(k2_relset_1(sK1,sK0,sK3),k1_zfmisc_1(sK0))
% 2.82/1.02      | X0_52 != k1_zfmisc_1(sK0)
% 2.82/1.02      | X0_51 != k2_relset_1(sK1,sK0,sK3) ),
% 2.82/1.02      inference(instantiation,[status(thm)],[c_816]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_1549,plain,
% 2.82/1.02      ( m1_subset_1(X0_51,k1_zfmisc_1(X0_52))
% 2.82/1.02      | ~ m1_subset_1(k2_relset_1(sK1,sK0,sK3),k1_zfmisc_1(sK0))
% 2.82/1.02      | k1_zfmisc_1(X0_52) != k1_zfmisc_1(sK0)
% 2.82/1.02      | X0_51 != k2_relset_1(sK1,sK0,sK3) ),
% 2.82/1.02      inference(instantiation,[status(thm)],[c_1427]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_1977,plain,
% 2.82/1.02      ( m1_subset_1(k2_relset_1(sK1,sK0,sK3),k1_zfmisc_1(X0_52))
% 2.82/1.02      | ~ m1_subset_1(k2_relset_1(sK1,sK0,sK3),k1_zfmisc_1(sK0))
% 2.82/1.02      | k1_zfmisc_1(X0_52) != k1_zfmisc_1(sK0)
% 2.82/1.02      | k2_relset_1(sK1,sK0,sK3) != k2_relset_1(sK1,sK0,sK3) ),
% 2.82/1.02      inference(instantiation,[status(thm)],[c_1549]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_3226,plain,
% 2.82/1.02      ( m1_subset_1(k2_relset_1(sK1,sK0,sK3),k1_zfmisc_1(k1_relset_1(sK0,sK2,sK4)))
% 2.82/1.02      | ~ m1_subset_1(k2_relset_1(sK1,sK0,sK3),k1_zfmisc_1(sK0))
% 2.82/1.02      | k1_zfmisc_1(k1_relset_1(sK0,sK2,sK4)) != k1_zfmisc_1(sK0)
% 2.82/1.02      | k2_relset_1(sK1,sK0,sK3) != k2_relset_1(sK1,sK0,sK3) ),
% 2.82/1.02      inference(instantiation,[status(thm)],[c_1977]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_810,plain,( X0_51 = X0_51 ),theory(equality) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_1978,plain,
% 2.82/1.02      ( k2_relset_1(sK1,sK0,sK3) = k2_relset_1(sK1,sK0,sK3) ),
% 2.82/1.02      inference(instantiation,[status(thm)],[c_810]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_3,plain,
% 2.82/1.02      ( v4_relat_1(X0,X1)
% 2.82/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.82/1.02      inference(cnf_transformation,[],[f40]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_7,plain,
% 2.82/1.02      ( ~ v1_partfun1(X0,X1)
% 2.82/1.02      | ~ v4_relat_1(X0,X1)
% 2.82/1.02      | ~ v1_relat_1(X0)
% 2.82/1.02      | k1_relat_1(X0) = X1 ),
% 2.82/1.02      inference(cnf_transformation,[],[f43]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_281,plain,
% 2.82/1.02      ( ~ v1_partfun1(X0,X1)
% 2.82/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.82/1.02      | ~ v1_relat_1(X0)
% 2.82/1.02      | k1_relat_1(X0) = X1 ),
% 2.82/1.02      inference(resolution,[status(thm)],[c_3,c_7]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_2,plain,
% 2.82/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.82/1.02      | v1_relat_1(X0) ),
% 2.82/1.02      inference(cnf_transformation,[],[f39]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_285,plain,
% 2.82/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.82/1.02      | ~ v1_partfun1(X0,X1)
% 2.82/1.02      | k1_relat_1(X0) = X1 ),
% 2.82/1.02      inference(global_propositional_subsumption,
% 2.82/1.02                [status(thm)],
% 2.82/1.02                [c_281,c_7,c_3,c_2]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_286,plain,
% 2.82/1.02      ( ~ v1_partfun1(X0,X1)
% 2.82/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.82/1.02      | k1_relat_1(X0) = X1 ),
% 2.82/1.02      inference(renaming,[status(thm)],[c_285]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_14,negated_conjecture,
% 2.82/1.02      ( v1_partfun1(sK4,sK0) ),
% 2.82/1.02      inference(cnf_transformation,[],[f58]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_327,plain,
% 2.82/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.82/1.02      | k1_relat_1(X0) = X1
% 2.82/1.02      | sK4 != X0
% 2.82/1.02      | sK0 != X1 ),
% 2.82/1.02      inference(resolution_lifted,[status(thm)],[c_286,c_14]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_328,plain,
% 2.82/1.02      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
% 2.82/1.02      | k1_relat_1(sK4) = sK0 ),
% 2.82/1.02      inference(unflattening,[status(thm)],[c_327]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_792,plain,
% 2.82/1.02      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_52)))
% 2.82/1.02      | k1_relat_1(sK4) = sK0 ),
% 2.82/1.02      inference(subtyping,[status(esa)],[c_328]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_1164,plain,
% 2.82/1.02      ( k1_relat_1(sK4) = sK0
% 2.82/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_52))) != iProver_top ),
% 2.82/1.02      inference(predicate_to_equality,[status(thm)],[c_792]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_1304,plain,
% 2.82/1.02      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.82/1.02      | k1_relat_1(sK4) = sK0 ),
% 2.82/1.02      inference(instantiation,[status(thm)],[c_792]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_1727,plain,
% 2.82/1.02      ( k1_relat_1(sK4) = sK0 ),
% 2.82/1.02      inference(global_propositional_subsumption,
% 2.82/1.02                [status(thm)],
% 2.82/1.02                [c_1164,c_16,c_1304]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_5,plain,
% 2.82/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.82/1.02      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.82/1.02      inference(cnf_transformation,[],[f42]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_806,plain,
% 2.82/1.02      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 2.82/1.02      | k1_relset_1(X0_52,X1_52,X0_51) = k1_relat_1(X0_51) ),
% 2.82/1.02      inference(subtyping,[status(esa)],[c_5]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_1151,plain,
% 2.82/1.02      ( k1_relset_1(X0_52,X1_52,X0_51) = k1_relat_1(X0_51)
% 2.82/1.02      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
% 2.82/1.02      inference(predicate_to_equality,[status(thm)],[c_806]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_1562,plain,
% 2.82/1.02      ( k1_relset_1(sK0,sK2,sK4) = k1_relat_1(sK4) ),
% 2.82/1.02      inference(superposition,[status(thm)],[c_1157,c_1151]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_1730,plain,
% 2.82/1.02      ( k1_relset_1(sK0,sK2,sK4) = sK0 ),
% 2.82/1.02      inference(demodulation,[status(thm)],[c_1727,c_1562]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_1,plain,
% 2.82/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.82/1.02      inference(cnf_transformation,[],[f38]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_12,plain,
% 2.82/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.82/1.02      | ~ m1_subset_1(X3,X1)
% 2.82/1.02      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
% 2.82/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.82/1.02      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X5,X4))
% 2.82/1.02      | ~ v1_funct_1(X4)
% 2.82/1.02      | ~ v1_funct_1(X0)
% 2.82/1.02      | v1_xboole_0(X2)
% 2.82/1.02      | k1_funct_1(k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
% 2.82/1.02      | k1_xboole_0 = X1 ),
% 2.82/1.02      inference(cnf_transformation,[],[f49]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_342,plain,
% 2.82/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.82/1.02      | ~ m1_subset_1(X3,X1)
% 2.82/1.02      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 2.82/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.82/1.02      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X2,X7)))
% 2.82/1.02      | ~ v1_funct_1(X0)
% 2.82/1.02      | ~ v1_funct_1(X6)
% 2.82/1.02      | v1_xboole_0(X2)
% 2.82/1.02      | k1_relset_1(X2,X7,X6) != X5
% 2.82/1.02      | k2_relset_1(X1,X2,X0) != X4
% 2.82/1.02      | k1_funct_1(k8_funct_2(X1,X2,X7,X0,X6),X3) = k1_funct_1(X6,k1_funct_1(X0,X3))
% 2.82/1.02      | k1_xboole_0 = X1 ),
% 2.82/1.02      inference(resolution_lifted,[status(thm)],[c_1,c_12]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_343,plain,
% 2.82/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.82/1.02      | ~ m1_subset_1(X3,X1)
% 2.82/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.82/1.02      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
% 2.82/1.02      | ~ m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(k1_relset_1(X2,X5,X4)))
% 2.82/1.02      | ~ v1_funct_1(X0)
% 2.82/1.02      | ~ v1_funct_1(X4)
% 2.82/1.02      | v1_xboole_0(X2)
% 2.82/1.02      | k1_funct_1(k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
% 2.82/1.02      | k1_xboole_0 = X1 ),
% 2.82/1.02      inference(unflattening,[status(thm)],[c_342]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_791,plain,
% 2.82/1.02      ( ~ v1_funct_2(X0_51,X0_52,X1_52)
% 2.82/1.02      | ~ m1_subset_1(X1_51,X0_52)
% 2.82/1.02      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 2.82/1.02      | ~ m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
% 2.82/1.02      | ~ m1_subset_1(k2_relset_1(X0_52,X1_52,X0_51),k1_zfmisc_1(k1_relset_1(X1_52,X2_52,X2_51)))
% 2.82/1.02      | ~ v1_funct_1(X0_51)
% 2.82/1.02      | ~ v1_funct_1(X2_51)
% 2.82/1.02      | v1_xboole_0(X1_52)
% 2.82/1.02      | k1_xboole_0 = X0_52
% 2.82/1.02      | k1_funct_1(k8_funct_2(X0_52,X1_52,X2_52,X0_51,X2_51),X1_51) = k1_funct_1(X2_51,k1_funct_1(X0_51,X1_51)) ),
% 2.82/1.02      inference(subtyping,[status(esa)],[c_343]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_1387,plain,
% 2.82/1.02      ( ~ v1_funct_2(X0_51,sK1,X0_52)
% 2.82/1.02      | ~ m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 2.82/1.02      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK1,X0_52)))
% 2.82/1.02      | ~ m1_subset_1(k2_relset_1(sK1,X0_52,X0_51),k1_zfmisc_1(k1_relset_1(X0_52,X1_52,X1_51)))
% 2.82/1.02      | ~ m1_subset_1(sK5,sK1)
% 2.82/1.02      | ~ v1_funct_1(X0_51)
% 2.82/1.02      | ~ v1_funct_1(X1_51)
% 2.82/1.02      | v1_xboole_0(X0_52)
% 2.82/1.02      | k1_xboole_0 = sK1
% 2.82/1.02      | k1_funct_1(k8_funct_2(sK1,X0_52,X1_52,X0_51,X1_51),sK5) = k1_funct_1(X1_51,k1_funct_1(X0_51,sK5)) ),
% 2.82/1.02      inference(instantiation,[status(thm)],[c_791]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_1491,plain,
% 2.82/1.02      ( ~ v1_funct_2(X0_51,sK1,sK0)
% 2.82/1.02      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.82/1.02      | ~ m1_subset_1(k2_relset_1(sK1,sK0,X0_51),k1_zfmisc_1(k1_relset_1(sK0,sK2,sK4)))
% 2.82/1.02      | ~ m1_subset_1(sK5,sK1)
% 2.82/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.82/1.02      | ~ v1_funct_1(X0_51)
% 2.82/1.02      | ~ v1_funct_1(sK4)
% 2.82/1.02      | v1_xboole_0(sK0)
% 2.82/1.02      | k1_xboole_0 = sK1
% 2.82/1.02      | k1_funct_1(k8_funct_2(sK1,sK0,sK2,X0_51,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(X0_51,sK5)) ),
% 2.82/1.02      inference(instantiation,[status(thm)],[c_1387]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_1493,plain,
% 2.82/1.02      ( ~ v1_funct_2(sK3,sK1,sK0)
% 2.82/1.02      | ~ m1_subset_1(k2_relset_1(sK1,sK0,sK3),k1_zfmisc_1(k1_relset_1(sK0,sK2,sK4)))
% 2.82/1.02      | ~ m1_subset_1(sK5,sK1)
% 2.82/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.82/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.82/1.02      | ~ v1_funct_1(sK4)
% 2.82/1.02      | ~ v1_funct_1(sK3)
% 2.82/1.02      | v1_xboole_0(sK0)
% 2.82/1.02      | k1_xboole_0 = sK1
% 2.82/1.02      | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 2.82/1.02      inference(instantiation,[status(thm)],[c_1491]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_811,plain,( X0_52 = X0_52 ),theory(equality) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_1439,plain,
% 2.82/1.02      ( sK1 = sK1 ),
% 2.82/1.02      inference(instantiation,[status(thm)],[c_811]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_4,plain,
% 2.82/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.82/1.02      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 2.82/1.02      inference(cnf_transformation,[],[f41]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_807,plain,
% 2.82/1.02      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 2.82/1.02      | m1_subset_1(k2_relset_1(X0_52,X1_52,X0_51),k1_zfmisc_1(X1_52)) ),
% 2.82/1.02      inference(subtyping,[status(esa)],[c_4]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_1330,plain,
% 2.82/1.02      ( m1_subset_1(k2_relset_1(sK1,sK0,sK3),k1_zfmisc_1(sK0))
% 2.82/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 2.82/1.02      inference(instantiation,[status(thm)],[c_807]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_0,plain,
% 2.82/1.02      ( v1_xboole_0(k1_xboole_0) ),
% 2.82/1.02      inference(cnf_transformation,[],[f37]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_22,negated_conjecture,
% 2.82/1.02      ( ~ v1_xboole_0(sK0) ),
% 2.82/1.02      inference(cnf_transformation,[],[f50]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(contradiction,plain,
% 2.82/1.02      ( $false ),
% 2.82/1.02      inference(minisat,
% 2.82/1.02                [status(thm)],
% 2.82/1.02                [c_6822,c_5253,c_4191,c_3944,c_3226,c_1978,c_1730,c_1493,
% 2.82/1.02                 c_1439,c_1330,c_0,c_15,c_16,c_17,c_18,c_19,c_20,c_21,
% 2.82/1.02                 c_22]) ).
% 2.82/1.02  
% 2.82/1.02  
% 2.82/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.82/1.02  
% 2.82/1.02  ------                               Statistics
% 2.82/1.02  
% 2.82/1.02  ------ General
% 2.82/1.02  
% 2.82/1.02  abstr_ref_over_cycles:                  0
% 2.82/1.02  abstr_ref_under_cycles:                 0
% 2.82/1.02  gc_basic_clause_elim:                   0
% 2.82/1.02  forced_gc_time:                         0
% 2.82/1.02  parsing_time:                           0.012
% 2.82/1.02  unif_index_cands_time:                  0.
% 2.82/1.02  unif_index_add_time:                    0.
% 2.82/1.02  orderings_time:                         0.
% 2.82/1.02  out_proof_time:                         0.011
% 2.82/1.02  total_time:                             0.253
% 2.82/1.02  num_of_symbols:                         59
% 2.82/1.02  num_of_terms:                           7135
% 2.82/1.02  
% 2.82/1.02  ------ Preprocessing
% 2.82/1.02  
% 2.82/1.02  num_of_splits:                          0
% 2.82/1.02  num_of_split_atoms:                     0
% 2.82/1.02  num_of_reused_defs:                     0
% 2.82/1.02  num_eq_ax_congr_red:                    21
% 2.82/1.02  num_of_sem_filtered_clauses:            1
% 2.82/1.02  num_of_subtypes:                        2
% 2.82/1.02  monotx_restored_types:                  0
% 2.82/1.02  sat_num_of_epr_types:                   0
% 2.82/1.02  sat_num_of_non_cyclic_types:            0
% 2.82/1.02  sat_guarded_non_collapsed_types:        1
% 2.82/1.02  num_pure_diseq_elim:                    0
% 2.82/1.02  simp_replaced_by:                       0
% 2.82/1.02  res_preprocessed:                       106
% 2.82/1.02  prep_upred:                             0
% 2.82/1.02  prep_unflattend:                        16
% 2.82/1.02  smt_new_axioms:                         0
% 2.82/1.02  pred_elim_cands:                        4
% 2.82/1.02  pred_elim:                              4
% 2.82/1.02  pred_elim_cl:                           5
% 2.82/1.02  pred_elim_cycles:                       7
% 2.82/1.02  merged_defs:                            0
% 2.82/1.02  merged_defs_ncl:                        0
% 2.82/1.02  bin_hyper_res:                          0
% 2.82/1.02  prep_cycles:                            4
% 2.82/1.02  pred_elim_time:                         0.009
% 2.82/1.02  splitting_time:                         0.
% 2.82/1.02  sem_filter_time:                        0.
% 2.82/1.02  monotx_time:                            0.
% 2.82/1.02  subtype_inf_time:                       0.
% 2.82/1.02  
% 2.82/1.02  ------ Problem properties
% 2.82/1.02  
% 2.82/1.02  clauses:                                18
% 2.82/1.02  conjectures:                            9
% 2.82/1.02  epr:                                    7
% 2.82/1.02  horn:                                   16
% 2.82/1.02  ground:                                 10
% 2.82/1.02  unary:                                  10
% 2.82/1.02  binary:                                 3
% 2.82/1.02  lits:                                   50
% 2.82/1.02  lits_eq:                                6
% 2.82/1.02  fd_pure:                                0
% 2.82/1.02  fd_pseudo:                              0
% 2.82/1.02  fd_cond:                                1
% 2.82/1.02  fd_pseudo_cond:                         0
% 2.82/1.02  ac_symbols:                             0
% 2.82/1.02  
% 2.82/1.02  ------ Propositional Solver
% 2.82/1.02  
% 2.82/1.02  prop_solver_calls:                      31
% 2.82/1.02  prop_fast_solver_calls:                 1242
% 2.82/1.02  smt_solver_calls:                       0
% 2.82/1.02  smt_fast_solver_calls:                  0
% 2.82/1.02  prop_num_of_clauses:                    1811
% 2.82/1.02  prop_preprocess_simplified:             5045
% 2.82/1.02  prop_fo_subsumed:                       34
% 2.82/1.02  prop_solver_time:                       0.
% 2.82/1.02  smt_solver_time:                        0.
% 2.82/1.02  smt_fast_solver_time:                   0.
% 2.82/1.02  prop_fast_solver_time:                  0.
% 2.82/1.02  prop_unsat_core_time:                   0.
% 2.82/1.02  
% 2.82/1.02  ------ QBF
% 2.82/1.02  
% 2.82/1.02  qbf_q_res:                              0
% 2.82/1.02  qbf_num_tautologies:                    0
% 2.82/1.02  qbf_prep_cycles:                        0
% 2.82/1.02  
% 2.82/1.02  ------ BMC1
% 2.82/1.02  
% 2.82/1.02  bmc1_current_bound:                     -1
% 2.82/1.02  bmc1_last_solved_bound:                 -1
% 2.82/1.02  bmc1_unsat_core_size:                   -1
% 2.82/1.02  bmc1_unsat_core_parents_size:           -1
% 2.82/1.02  bmc1_merge_next_fun:                    0
% 2.82/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.82/1.02  
% 2.82/1.02  ------ Instantiation
% 2.82/1.02  
% 2.82/1.02  inst_num_of_clauses:                    560
% 2.82/1.02  inst_num_in_passive:                    117
% 2.82/1.02  inst_num_in_active:                     438
% 2.82/1.02  inst_num_in_unprocessed:                4
% 2.82/1.02  inst_num_of_loops:                      454
% 2.82/1.02  inst_num_of_learning_restarts:          0
% 2.82/1.02  inst_num_moves_active_passive:          10
% 2.82/1.02  inst_lit_activity:                      0
% 2.82/1.02  inst_lit_activity_moves:                0
% 2.82/1.02  inst_num_tautologies:                   0
% 2.82/1.02  inst_num_prop_implied:                  0
% 2.82/1.02  inst_num_existing_simplified:           0
% 2.82/1.02  inst_num_eq_res_simplified:             0
% 2.82/1.02  inst_num_child_elim:                    0
% 2.82/1.02  inst_num_of_dismatching_blockings:      270
% 2.82/1.02  inst_num_of_non_proper_insts:           755
% 2.82/1.02  inst_num_of_duplicates:                 0
% 2.82/1.02  inst_inst_num_from_inst_to_res:         0
% 2.82/1.02  inst_dismatching_checking_time:         0.
% 2.82/1.02  
% 2.82/1.02  ------ Resolution
% 2.82/1.02  
% 2.82/1.02  res_num_of_clauses:                     0
% 2.82/1.02  res_num_in_passive:                     0
% 2.82/1.02  res_num_in_active:                      0
% 2.82/1.02  res_num_of_loops:                       110
% 2.82/1.02  res_forward_subset_subsumed:            166
% 2.82/1.02  res_backward_subset_subsumed:           0
% 2.82/1.02  res_forward_subsumed:                   0
% 2.82/1.02  res_backward_subsumed:                  0
% 2.82/1.02  res_forward_subsumption_resolution:     1
% 2.82/1.02  res_backward_subsumption_resolution:    0
% 2.82/1.02  res_clause_to_clause_subsumption:       1202
% 2.82/1.02  res_orphan_elimination:                 0
% 2.82/1.02  res_tautology_del:                      151
% 2.82/1.02  res_num_eq_res_simplified:              0
% 2.82/1.02  res_num_sel_changes:                    0
% 2.82/1.02  res_moves_from_active_to_pass:          0
% 2.82/1.02  
% 2.82/1.02  ------ Superposition
% 2.82/1.02  
% 2.82/1.02  sup_time_total:                         0.
% 2.82/1.02  sup_time_generating:                    0.
% 2.82/1.02  sup_time_sim_full:                      0.
% 2.82/1.02  sup_time_sim_immed:                     0.
% 2.82/1.02  
% 2.82/1.02  sup_num_of_clauses:                     143
% 2.82/1.02  sup_num_in_active:                      87
% 2.82/1.02  sup_num_in_passive:                     56
% 2.82/1.02  sup_num_of_loops:                       90
% 2.82/1.02  sup_fw_superposition:                   122
% 2.82/1.02  sup_bw_superposition:                   3
% 2.82/1.02  sup_immediate_simplified:               0
% 2.82/1.02  sup_given_eliminated:                   0
% 2.82/1.02  comparisons_done:                       0
% 2.82/1.02  comparisons_avoided:                    1
% 2.82/1.02  
% 2.82/1.02  ------ Simplifications
% 2.82/1.02  
% 2.82/1.02  
% 2.82/1.02  sim_fw_subset_subsumed:                 0
% 2.82/1.02  sim_bw_subset_subsumed:                 0
% 2.82/1.02  sim_fw_subsumed:                        0
% 2.82/1.02  sim_bw_subsumed:                        0
% 2.82/1.02  sim_fw_subsumption_res:                 12
% 2.82/1.02  sim_bw_subsumption_res:                 0
% 2.82/1.02  sim_tautology_del:                      0
% 2.82/1.02  sim_eq_tautology_del:                   0
% 2.82/1.02  sim_eq_res_simp:                        0
% 2.82/1.02  sim_fw_demodulated:                     0
% 2.82/1.02  sim_bw_demodulated:                     3
% 2.82/1.02  sim_light_normalised:                   0
% 2.82/1.02  sim_joinable_taut:                      0
% 2.82/1.02  sim_joinable_simp:                      0
% 2.82/1.02  sim_ac_normalised:                      0
% 2.82/1.02  sim_smt_subsumption:                    0
% 2.82/1.02  
%------------------------------------------------------------------------------
