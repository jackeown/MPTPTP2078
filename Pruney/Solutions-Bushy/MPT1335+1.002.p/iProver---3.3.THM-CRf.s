%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1335+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:30 EST 2020

% Result     : Theorem 43.21s
% Output     : CNFRefutation 43.21s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 898 expanded)
%              Number of clauses        :  115 ( 210 expanded)
%              Number of leaves         :   21 ( 351 expanded)
%              Depth                    :   19
%              Number of atoms          :  803 (10056 expanded)
%              Number of equality atoms :  175 ( 309 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( ( v5_pre_topc(X4,X2,X1)
                          & v5_pre_topc(X3,X0,X2) )
                       => v5_pre_topc(k1_partfun1(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),X3,X4),X0,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( ( l1_pre_topc(X2)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                      & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                      & v1_funct_1(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( ( v5_pre_topc(X4,X2,X1)
                            & v5_pre_topc(X3,X0,X2) )
                         => v5_pre_topc(k1_partfun1(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),X3,X4),X0,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ v5_pre_topc(k1_partfun1(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),X3,X4),X0,X1)
                      & v5_pre_topc(X4,X2,X1)
                      & v5_pre_topc(X3,X0,X2)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                  & v1_funct_1(X3) )
              & l1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ v5_pre_topc(k1_partfun1(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),X3,X4),X0,X1)
                      & v5_pre_topc(X4,X2,X1)
                      & v5_pre_topc(X3,X0,X2)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                  & v1_funct_1(X3) )
              & l1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ~ v5_pre_topc(k1_partfun1(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),X3,X4),X0,X1)
          & v5_pre_topc(X4,X2,X1)
          & v5_pre_topc(X3,X0,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
          & v1_funct_1(X4) )
     => ( ~ v5_pre_topc(k1_partfun1(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),X3,sK6),X0,X1)
        & v5_pre_topc(sK6,X2,X1)
        & v5_pre_topc(X3,X0,X2)
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(sK6,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ~ v5_pre_topc(k1_partfun1(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),X3,X4),X0,X1)
              & v5_pre_topc(X4,X2,X1)
              & v5_pre_topc(X3,X0,X2)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
              & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
          & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
          & v1_funct_1(X3) )
     => ( ? [X4] :
            ( ~ v5_pre_topc(k1_partfun1(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),sK5,X4),X0,X1)
            & v5_pre_topc(X4,X2,X1)
            & v5_pre_topc(sK5,X0,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
        & v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(X2))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ v5_pre_topc(k1_partfun1(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),X3,X4),X0,X1)
                  & v5_pre_topc(X4,X2,X1)
                  & v5_pre_topc(X3,X0,X2)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
              & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
              & v1_funct_1(X3) )
          & l1_pre_topc(X2)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ~ v5_pre_topc(k1_partfun1(u1_struct_0(X0),u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(X1),X3,X4),X0,X1)
                & v5_pre_topc(X4,sK4,X1)
                & v5_pre_topc(X3,X0,sK4)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4))))
            & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(sK4))
            & v1_funct_1(X3) )
        & l1_pre_topc(sK4)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ v5_pre_topc(k1_partfun1(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),X3,X4),X0,X1)
                      & v5_pre_topc(X4,X2,X1)
                      & v5_pre_topc(X3,X0,X2)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                  & v1_funct_1(X3) )
              & l1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ~ v5_pre_topc(k1_partfun1(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(sK3),X3,X4),X0,sK3)
                    & v5_pre_topc(X4,X2,sK3)
                    & v5_pre_topc(X3,X0,X2)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3))))
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK3))
                    & v1_funct_1(X4) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                & v1_funct_1(X3) )
            & l1_pre_topc(X2)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ~ v5_pre_topc(k1_partfun1(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),X3,X4),X0,X1)
                        & v5_pre_topc(X4,X2,X1)
                        & v5_pre_topc(X3,X0,X2)
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                    & v1_funct_1(X3) )
                & l1_pre_topc(X2)
                & ~ v2_struct_0(X2) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ v5_pre_topc(k1_partfun1(u1_struct_0(sK2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),X3,X4),sK2,X1)
                      & v5_pre_topc(X4,X2,X1)
                      & v5_pre_topc(X3,sK2,X2)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X2))))
                  & v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(X2))
                  & v1_funct_1(X3) )
              & l1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ~ v5_pre_topc(k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK6),sK2,sK3)
    & v5_pre_topc(sK6,sK4,sK3)
    & v5_pre_topc(sK5,sK2,sK4)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    & v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK4))))
    & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK4))
    & v1_funct_1(sK5)
    & l1_pre_topc(sK4)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f39,f50,f49,f48,f47,f46])).

fof(f78,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f51])).

fof(f81,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f51])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f29])).

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f79,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f51])).

fof(f76,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f21])).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( v4_pre_topc(X3,X1)
                     => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v4_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      | ~ v4_pre_topc(X3,X1)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v4_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v4_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v4_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
        & v4_pre_topc(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
                    & v4_pre_topc(sK0(X0,X1,X2),X1)
                    & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v4_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f42])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
      | ~ v4_pre_topc(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X4,X1,X2)
        & v1_funct_1(X4)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & ~ v1_xboole_0(X1) )
     => ( v1_funct_2(k5_relat_1(X3,X4),X0,X2)
        & v1_funct_1(k5_relat_1(X3,X4)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( v1_funct_2(k5_relat_1(X3,X4),X0,X2)
        & v1_funct_1(k5_relat_1(X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( v1_funct_2(k5_relat_1(X3,X4),X0,X2)
        & v1_funct_1(k5_relat_1(X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f27])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k5_relat_1(X3,X4),X0,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f74,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f75,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f80,plain,(
    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f51])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f60,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f84,plain,(
    ~ v5_pre_topc(k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK6),sK2,sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | v4_pre_topc(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f83,plain,(
    v5_pre_topc(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f82,plain,(
    v5_pre_topc(sK5,sK2,sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f77,plain,(
    v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f51])).

fof(f73,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f72,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1125,plain,
    ( ~ v4_pre_topc(X0,X1)
    | v4_pre_topc(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_41555,plain,
    ( ~ v4_pre_topc(X0,sK2)
    | v4_pre_topc(X1,sK2)
    | X1 != X0 ),
    inference(instantiation,[status(thm)],[c_1125])).

cnf(c_89789,plain,
    ( v4_pre_topc(X0,sK2)
    | ~ v4_pre_topc(k10_relat_1(sK5,k8_relset_1(u1_struct_0(X1),u1_struct_0(sK3),sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6)))),sK2)
    | X0 != k10_relat_1(sK5,k8_relset_1(u1_struct_0(X1),u1_struct_0(sK3),sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6)))) ),
    inference(instantiation,[status(thm)],[c_41555])).

cnf(c_103733,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK5,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6)))),sK2)
    | v4_pre_topc(k10_relat_1(sK5,k10_relat_1(sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6)))),sK2)
    | k10_relat_1(sK5,k10_relat_1(sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6)))) != k10_relat_1(sK5,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6)))) ),
    inference(instantiation,[status(thm)],[c_89789])).

cnf(c_1131,plain,
    ( X0 != X1
    | X2 != X3
    | k10_relat_1(X0,X2) = k10_relat_1(X1,X3) ),
    theory(equality)).

cnf(c_66862,plain,
    ( X0 != k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6)))
    | X1 != sK5
    | k10_relat_1(X1,X0) = k10_relat_1(sK5,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6)))) ),
    inference(instantiation,[status(thm)],[c_1131])).

cnf(c_74249,plain,
    ( X0 != k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6)))
    | k10_relat_1(sK5,X0) = k10_relat_1(sK5,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6))))
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_66862])).

cnf(c_79882,plain,
    ( k10_relat_1(sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6))) != k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6)))
    | k10_relat_1(sK5,k10_relat_1(sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6)))) = k10_relat_1(sK5,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6))))
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_74249])).

cnf(c_41623,plain,
    ( v4_pre_topc(X0,sK2)
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2,X3),sK2)
    | X0 != k8_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2,X3) ),
    inference(instantiation,[status(thm)],[c_41555])).

cnf(c_45380,plain,
    ( v4_pre_topc(X0,sK2)
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK4),sK5,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6)))),sK2)
    | X0 != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK4),sK5,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6)))) ),
    inference(instantiation,[status(thm)],[c_41623])).

cnf(c_66548,plain,
    ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK4),sK5,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6)))),sK2)
    | v4_pre_topc(k10_relat_1(X0,X1),sK2)
    | k10_relat_1(X0,X1) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK4),sK5,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6)))) ),
    inference(instantiation,[status(thm)],[c_45380])).

cnf(c_73560,plain,
    ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK4),sK5,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6)))),sK2)
    | v4_pre_topc(k10_relat_1(sK5,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6)))),sK2)
    | k10_relat_1(sK5,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6)))) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK4),sK5,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6)))) ),
    inference(instantiation,[status(thm)],[c_66548])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1649,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1652,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1660,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3233,plain,
    ( k1_partfun1(X0,X1,u1_struct_0(sK4),u1_struct_0(sK3),X2,sK6) = k5_relat_1(X2,sK6)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1652,c_1660])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_40,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3363,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,u1_struct_0(sK4),u1_struct_0(sK3),X2,sK6) = k5_relat_1(X2,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3233,c_40])).

cnf(c_3364,plain,
    ( k1_partfun1(X0,X1,u1_struct_0(sK4),u1_struct_0(sK3),X2,sK6) = k5_relat_1(X2,sK6)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3363])).

cnf(c_3373,plain,
    ( k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK6) = k5_relat_1(sK5,sK6)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1649,c_3364])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_3319,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK4))))
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_1(sK5)
    | k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK6) = k5_relat_1(sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_3421,plain,
    ( k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK6) = k5_relat_1(sK5,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3373,c_28,c_26,c_25,c_23,c_3319])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1666,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3425,plain,
    ( m1_subset_1(k5_relat_1(sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK4)))) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3421,c_1666])).

cnf(c_37,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_39,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_42,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_7386,plain,
    ( m1_subset_1(k5_relat_1(sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3425,c_37,c_39,c_40,c_42])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1659,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_7399,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k5_relat_1(sK5,sK6),X0) = k10_relat_1(k5_relat_1(sK5,sK6),X0) ),
    inference(superposition,[status(thm)],[c_7386,c_1659])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1671,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2197,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1652,c_1671])).

cnf(c_2198,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1649,c_1671])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(k5_relat_1(X1,X0),X2) = k10_relat_1(X1,k10_relat_1(X0,X2)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1658,plain,
    ( k10_relat_1(k5_relat_1(X0,X1),X2) = k10_relat_1(X0,k10_relat_1(X1,X2))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2452,plain,
    ( k10_relat_1(sK5,k10_relat_1(X0,X1)) = k10_relat_1(k5_relat_1(sK5,X0),X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2198,c_1658])).

cnf(c_3170,plain,
    ( k10_relat_1(k5_relat_1(sK5,sK6),X0) = k10_relat_1(sK5,k10_relat_1(sK6,X0)) ),
    inference(superposition,[status(thm)],[c_2197,c_2452])).

cnf(c_7401,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k5_relat_1(sK5,sK6),X0) = k10_relat_1(sK5,k10_relat_1(sK6,X0)) ),
    inference(light_normalisation,[status(thm)],[c_7399,c_3170])).

cnf(c_1,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1670,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v5_pre_topc(X0,X1,X2) = iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0)),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_66816,plain,
    ( v1_funct_2(k5_relat_1(sK5,sK6),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(k5_relat_1(sK5,sK6),sK2,sK3) = iProver_top
    | v4_pre_topc(k10_relat_1(sK5,k10_relat_1(sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6)))),sK2) != iProver_top
    | m1_subset_1(k5_relat_1(sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(k5_relat_1(sK5,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7401,c_1670])).

cnf(c_66819,plain,
    ( ~ v1_funct_2(k5_relat_1(sK5,sK6),u1_struct_0(sK2),u1_struct_0(sK3))
    | v5_pre_topc(k5_relat_1(sK5,sK6),sK2,sK3)
    | ~ v4_pre_topc(k10_relat_1(sK5,k10_relat_1(sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6)))),sK2)
    | ~ m1_subset_1(k5_relat_1(sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(k5_relat_1(sK5,sK6)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_66816])).

cnf(c_1117,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_66805,plain,
    ( k10_relat_1(sK5,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6)))) = k10_relat_1(sK5,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6)))) ),
    inference(instantiation,[status(thm)],[c_1117])).

cnf(c_1118,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_47535,plain,
    ( X0 != X1
    | X0 = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK4),sK5,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6))))
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK4),sK5,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6)))) != X1 ),
    inference(instantiation,[status(thm)],[c_1118])).

cnf(c_51229,plain,
    ( X0 = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK4),sK5,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6))))
    | X0 != k10_relat_1(sK5,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6))))
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK4),sK5,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6)))) != k10_relat_1(sK5,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6)))) ),
    inference(instantiation,[status(thm)],[c_47535])).

cnf(c_61493,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK4),sK5,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6)))) != k10_relat_1(sK5,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6))))
    | k10_relat_1(sK5,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6)))) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK4),sK5,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6))))
    | k10_relat_1(sK5,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6)))) != k10_relat_1(sK5,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6)))) ),
    inference(instantiation,[status(thm)],[c_51229])).

cnf(c_61123,plain,
    ( k10_relat_1(sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6))) = k10_relat_1(sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6))) ),
    inference(instantiation,[status(thm)],[c_1117])).

cnf(c_45434,plain,
    ( X0 != X1
    | X0 = k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6)))
    | k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6))) != X1 ),
    inference(instantiation,[status(thm)],[c_1118])).

cnf(c_47566,plain,
    ( X0 = k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6)))
    | X0 != k10_relat_1(sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6)))
    | k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6))) != k10_relat_1(sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6))) ),
    inference(instantiation,[status(thm)],[c_45434])).

cnf(c_56705,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6))) != k10_relat_1(sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6)))
    | k10_relat_1(sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6))) = k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6)))
    | k10_relat_1(sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6))) != k10_relat_1(sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6))) ),
    inference(instantiation,[status(thm)],[c_47566])).

cnf(c_56686,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK4))))
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK4),sK5,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6)))) = k10_relat_1(sK5,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6)))) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_51208,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6))) = k10_relat_1(sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6))) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_45512,plain,
    ( m1_subset_1(k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6))),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ v4_pre_topc(X3,X2)
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_41633,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
    | ~ v5_pre_topc(X0,sK2,X1)
    | ~ v4_pre_topc(X2,X1)
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X0,X2),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_41708,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
    | ~ v5_pre_topc(X0,sK2,X1)
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X1)
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X0,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4)),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ m1_subset_1(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_41633])).

cnf(c_42503,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(X0))
    | ~ v5_pre_topc(sK5,sK2,X0)
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(X0),sK5,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),sK2)
    | ~ m1_subset_1(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_41708])).

cnf(c_43988,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK4))
    | ~ v5_pre_topc(sK5,sK2,sK4)
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6))),sK4)
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK4),sK5,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6)))),sK2)
    | ~ m1_subset_1(k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6))),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK4))))
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_42503])).

cnf(c_41845,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1))
    | ~ v5_pre_topc(X0,sK4,X1)
    | ~ v4_pre_topc(X2,X1)
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0,X2),sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK4)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_42474,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v5_pre_topc(X0,sK4,sK3)
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),X0,sK0(sK2,sK3,k5_relat_1(sK5,sK6))),sK4)
    | ~ v4_pre_topc(sK0(sK2,sK3,k5_relat_1(sK5,sK6)),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK0(sK2,sK3,k5_relat_1(sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK4)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_41845])).

cnf(c_43407,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v5_pre_topc(sK6,sK4,sK3)
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK0(sK2,sK3,k5_relat_1(sK5,sK6))),sK4)
    | ~ v4_pre_topc(sK0(sK2,sK3,k5_relat_1(sK5,sK6)),sK3)
    | ~ m1_subset_1(sK0(sK2,sK3,k5_relat_1(sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK4)
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_42474])).

cnf(c_4609,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1117])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | v1_funct_2(k5_relat_1(X3,X0),X4,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1662,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | v1_funct_2(X3,X4,X1) != iProver_top
    | v1_funct_2(k5_relat_1(X3,X0),X4,X2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3638,plain,
    ( v1_funct_2(X0,X1,u1_struct_0(sK4)) != iProver_top
    | v1_funct_2(k5_relat_1(X0,sK6),X1,u1_struct_0(sK3)) = iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK4)))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1652,c_1662])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_35,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_36,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_41,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_10,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_73,plain,
    ( v2_struct_0(X0) = iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_75,plain,
    ( v2_struct_0(sK4) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) != iProver_top
    | l1_struct_0(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_73])).

cnf(c_8,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_79,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_81,plain,
    ( l1_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_79])).

cnf(c_3945,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_2(k5_relat_1(X0,sK6),X1,u1_struct_0(sK3)) = iProver_top
    | v1_funct_2(X0,X1,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK4)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3638,c_35,c_36,c_40,c_41,c_75,c_81])).

cnf(c_3946,plain,
    ( v1_funct_2(X0,X1,u1_struct_0(sK4)) != iProver_top
    | v1_funct_2(k5_relat_1(X0,sK6),X1,u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK4)))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3945])).

cnf(c_3954,plain,
    ( v1_funct_2(k5_relat_1(sK5,sK6),u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK4)) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1649,c_3946])).

cnf(c_3964,plain,
    ( v1_funct_2(k5_relat_1(sK5,sK6),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK4))
    | ~ v1_funct_1(sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3954])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_funct_1(k1_partfun1(X4,X5,X1,X2,X3,X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1665,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(k1_partfun1(X4,X5,X1,X2,X3,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3426,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK4)))) != iProver_top
    | v1_funct_1(k5_relat_1(sK5,sK6)) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3421,c_1665])).

cnf(c_3428,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK4))))
    | v1_funct_1(k5_relat_1(sK5,sK6))
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_1(sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3426])).

cnf(c_3427,plain,
    ( m1_subset_1(k5_relat_1(sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK4))))
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_1(sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3425])).

cnf(c_20,negated_conjecture,
    ( ~ v5_pre_topc(k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK6),sK2,sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1655,plain,
    ( v5_pre_topc(k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK6),sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3423,plain,
    ( v5_pre_topc(k5_relat_1(sK5,sK6),sK2,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3421,c_1655])).

cnf(c_3424,plain,
    ( ~ v5_pre_topc(k5_relat_1(sK5,sK6),sK2,sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3423])).

cnf(c_2,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | v4_pre_topc(sK0(X1,X2,X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1872,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3))
    | v5_pre_topc(X0,sK2,sK3)
    | v4_pre_topc(sK0(sK2,sK3,X0),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2016,plain,
    ( ~ v1_funct_2(k5_relat_1(X0,X1),u1_struct_0(sK2),u1_struct_0(sK3))
    | v5_pre_topc(k5_relat_1(X0,X1),sK2,sK3)
    | v4_pre_topc(sK0(sK2,sK3,k5_relat_1(X0,X1)),sK3)
    | ~ m1_subset_1(k5_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(k5_relat_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_1872])).

cnf(c_3022,plain,
    ( ~ v1_funct_2(k5_relat_1(sK5,sK6),u1_struct_0(sK2),u1_struct_0(sK3))
    | v5_pre_topc(k5_relat_1(sK5,sK6),sK2,sK3)
    | v4_pre_topc(sK0(sK2,sK3,k5_relat_1(sK5,sK6)),sK3)
    | ~ m1_subset_1(k5_relat_1(sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(k5_relat_1(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_2016])).

cnf(c_3,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1871,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3))
    | v5_pre_topc(X0,sK2,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | m1_subset_1(sK0(sK2,sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1997,plain,
    ( ~ v1_funct_2(k5_relat_1(X0,X1),u1_struct_0(sK2),u1_struct_0(sK3))
    | v5_pre_topc(k5_relat_1(X0,X1),sK2,sK3)
    | m1_subset_1(sK0(sK2,sK3,k5_relat_1(X0,X1)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k5_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(k5_relat_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_1871])).

cnf(c_3023,plain,
    ( ~ v1_funct_2(k5_relat_1(sK5,sK6),u1_struct_0(sK2),u1_struct_0(sK3))
    | v5_pre_topc(k5_relat_1(sK5,sK6),sK2,sK3)
    | m1_subset_1(sK0(sK2,sK3,k5_relat_1(sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k5_relat_1(sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(k5_relat_1(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_1997])).

cnf(c_21,negated_conjecture,
    ( v5_pre_topc(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_22,negated_conjecture,
    ( v5_pre_topc(sK5,sK2,sK4) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_31,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_103733,c_79882,c_73560,c_66819,c_66805,c_61493,c_61123,c_56705,c_56686,c_51208,c_45512,c_43988,c_43407,c_4609,c_3964,c_3428,c_3427,c_3424,c_3022,c_3023,c_21,c_22,c_23,c_24,c_25,c_26,c_27,c_28,c_29,c_31,c_32])).


%------------------------------------------------------------------------------
