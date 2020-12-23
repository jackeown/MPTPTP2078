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
% DateTime   : Thu Dec  3 12:23:58 EST 2020

% Result     : Theorem 6.57s
% Output     : CNFRefutation 6.57s
% Verified   : 
% Statistics : Number of formulae       :  208 (2035 expanded)
%              Number of clauses        :  111 ( 474 expanded)
%              Number of leaves         :   25 ( 693 expanded)
%              Depth                    :   26
%              Number of atoms          :  917 (14859 expanded)
%              Number of equality atoms :  190 ( 728 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ~ r2_hidden(X2,X1)
               => r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( ( r1_tmap_1(X1,X0,X2,X4)
                              & X4 = X5 )
                           => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,X0,X2,X4)
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,X0,X2,X4)
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f98,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ r1_tmap_1(X1,X0,X2,X4)
      | X4 != X5
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f113,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ r1_tmap_1(X1,X0,X2,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f98])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( r1_xboole_0(u1_struct_0(X2),X1)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X2))
                   => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( r1_xboole_0(u1_struct_0(X2),X1)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X2))
                     => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
              & r1_xboole_0(u1_struct_0(X2),X1)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
              & r1_xboole_0(u1_struct_0(X2),X1)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
          & m1_subset_1(X3,u1_struct_0(X2)) )
     => ( ~ r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),sK7)
        & m1_subset_1(sK7,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
              & m1_subset_1(X3,u1_struct_0(X2)) )
          & r1_xboole_0(u1_struct_0(X2),X1)
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ~ r1_tmap_1(sK6,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),sK6),X3)
            & m1_subset_1(X3,u1_struct_0(sK6)) )
        & r1_xboole_0(u1_struct_0(sK6),X1)
        & m1_pre_topc(sK6,X0)
        & ~ v2_struct_0(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
              & r1_xboole_0(u1_struct_0(X2),X1)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_tmap_1(X2,k6_tmap_1(X0,sK5),k2_tmap_1(X0,k6_tmap_1(X0,sK5),k7_tmap_1(X0,sK5),X2),X3)
                & m1_subset_1(X3,u1_struct_0(X2)) )
            & r1_xboole_0(u1_struct_0(X2),sK5)
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                    & m1_subset_1(X3,u1_struct_0(X2)) )
                & r1_xboole_0(u1_struct_0(X2),X1)
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tmap_1(X2,k6_tmap_1(sK4,X1),k2_tmap_1(sK4,k6_tmap_1(sK4,X1),k7_tmap_1(sK4,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
              & r1_xboole_0(u1_struct_0(X2),X1)
              & m1_pre_topc(X2,sK4)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,
    ( ~ r1_tmap_1(sK6,k6_tmap_1(sK4,sK5),k2_tmap_1(sK4,k6_tmap_1(sK4,sK5),k7_tmap_1(sK4,sK5),sK6),sK7)
    & m1_subset_1(sK7,u1_struct_0(sK6))
    & r1_xboole_0(u1_struct_0(sK6),sK5)
    & m1_pre_topc(sK6,sK4)
    & ~ v2_struct_0(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f43,f65,f64,f63,f62])).

fof(f104,plain,(
    m1_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f66])).

fof(f99,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f66])).

fof(f100,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f66])).

fof(f101,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f66])).

fof(f103,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f66])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f107,plain,(
    ~ r1_tmap_1(sK6,k6_tmap_1(sK4,sK5),k2_tmap_1(sK4,k6_tmap_1(sK4,sK5),k7_tmap_1(sK4,sK5),sK6),sK7) ),
    inference(cnf_transformation,[],[f66])).

fof(f102,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f66])).

fof(f106,plain,(
    m1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f66])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f91,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f96,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f94,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f93,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(X0,X1) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f105,plain,(
    r1_xboole_0(u1_struct_0(sK6),sK5) ),
    inference(cnf_transformation,[],[f66])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f52])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f53])).

fof(f55,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f54,f55])).

fof(f73,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f109,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f73])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f44])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f45,f46])).

fof(f67,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f85,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f60,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_xboole_0(sK3(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0] :
      ( ( ~ v1_xboole_0(sK3(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f60])).

fof(f87,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f48])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f49,f50])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f88,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK3(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f72,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f110,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f72])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f86,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_30,plain,
    ( r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(X2,X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_2275,plain,
    ( r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r2_hidden(X2,X1) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_31,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_35,negated_conjecture,
    ( m1_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_780,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | sK4 != X0
    | sK6 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_35])).

cnf(c_781,plain,
    ( ~ r1_tmap_1(sK4,X0,X1,X2)
    | r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,X1,sK6),X2)
    | ~ v1_funct_2(X1,u1_struct_0(sK4),u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | ~ v1_funct_1(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(X0)
    | v2_struct_0(sK4)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_780])).

cnf(c_40,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_39,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_38,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_785,plain,
    ( ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ r1_tmap_1(sK4,X0,X1,X2)
    | r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,X1,sK6),X2)
    | ~ v1_funct_2(X1,u1_struct_0(sK4),u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | ~ v1_funct_1(X1)
    | ~ v2_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_781,c_40,c_39,c_38,c_36])).

cnf(c_786,plain,
    ( ~ r1_tmap_1(sK4,X0,X1,X2)
    | r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,X1,sK6),X2)
    | ~ v1_funct_2(X1,u1_struct_0(sK4),u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | ~ v1_funct_1(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(renaming,[status(thm)],[c_785])).

cnf(c_22,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_751,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(X0,u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X2)
    | sK4 != X2
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_35])).

cnf(c_752,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | v2_struct_0(sK4)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_751])).

cnf(c_756,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_752,c_40,c_38,c_36])).

cnf(c_757,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_756])).

cnf(c_801,plain,
    ( ~ r1_tmap_1(sK4,X0,X1,X2)
    | r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,X1,sK6),X2)
    | ~ v1_funct_2(X1,u1_struct_0(sK4),u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | ~ v1_funct_1(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_786,c_757])).

cnf(c_2263,plain,
    ( r1_tmap_1(sK4,X0,X1,X2) != iProver_top
    | r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,X1,sK6),X2) = iProver_top
    | v1_funct_2(X1,u1_struct_0(sK4),u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_801])).

cnf(c_32,negated_conjecture,
    ( ~ r1_tmap_1(sK6,k6_tmap_1(sK4,sK5),k2_tmap_1(sK4,k6_tmap_1(sK4,sK5),k7_tmap_1(sK4,sK5),sK6),sK7) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_2274,plain,
    ( r1_tmap_1(sK6,k6_tmap_1(sK4,sK5),k2_tmap_1(sK4,k6_tmap_1(sK4,sK5),k7_tmap_1(sK4,sK5),sK6),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_2690,plain,
    ( r1_tmap_1(sK4,k6_tmap_1(sK4,sK5),k7_tmap_1(sK4,sK5),sK7) != iProver_top
    | v1_funct_2(k7_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5))))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK6)) != iProver_top
    | v1_funct_1(k7_tmap_1(sK4,sK5)) != iProver_top
    | v2_pre_topc(k6_tmap_1(sK4,sK5)) != iProver_top
    | v2_struct_0(k6_tmap_1(sK4,sK5)) = iProver_top
    | l1_pre_topc(k6_tmap_1(sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2263,c_2274])).

cnf(c_41,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_42,plain,
    ( v2_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_43,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_44,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_48,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k6_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2607,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | l1_pre_topc(k6_tmap_1(sK4,sK5))
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_2608,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(k6_tmap_1(sK4,sK5)) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2607])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_funct_1(k7_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2616,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_funct_1(k7_tmap_1(sK4,sK5))
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_2617,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK4,sK5)) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2616])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k6_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2625,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_pre_topc(k6_tmap_1(sK4,sK5))
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_2626,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v2_pre_topc(k6_tmap_1(sK4,sK5)) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2625])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2649,plain,
    ( m1_subset_1(k7_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5)))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_2650,plain,
    ( m1_subset_1(k7_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5))))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2649])).

cnf(c_26,plain,
    ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2658,plain,
    ( v1_funct_2(k7_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_2659,plain,
    ( v1_funct_2(k7_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2658])).

cnf(c_3136,plain,
    ( v2_struct_0(k6_tmap_1(sK4,sK5)) = iProver_top
    | r1_tmap_1(sK4,k6_tmap_1(sK4,sK5),k7_tmap_1(sK4,sK5),sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2690,c_41,c_42,c_43,c_44,c_48,c_2608,c_2617,c_2626,c_2650,c_2659])).

cnf(c_3137,plain,
    ( r1_tmap_1(sK4,k6_tmap_1(sK4,sK5),k7_tmap_1(sK4,sK5),sK7) != iProver_top
    | v2_struct_0(k6_tmap_1(sK4,sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3136])).

cnf(c_5342,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(sK7,sK5) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_struct_0(k6_tmap_1(sK4,sK5)) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2275,c_3137])).

cnf(c_2581,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_757])).

cnf(c_2582,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2581])).

cnf(c_5921,plain,
    ( r2_hidden(sK7,sK5) = iProver_top
    | v2_struct_0(k6_tmap_1(sK4,sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5342,c_41,c_42,c_43,c_44,c_48,c_2582])).

cnf(c_2271,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(k6_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2276,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(k6_tmap_1(X1,X0)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_6161,plain,
    ( v2_pre_topc(sK4) != iProver_top
    | v2_struct_0(k6_tmap_1(sK4,sK5)) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2271,c_2276])).

cnf(c_6427,plain,
    ( v2_struct_0(k6_tmap_1(sK4,sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6161,c_41,c_42,c_43])).

cnf(c_6432,plain,
    ( r2_hidden(sK7,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_5921,c_6427])).

cnf(c_2273,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2284,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4140,plain,
    ( r2_hidden(sK7,u1_struct_0(sK6)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2273,c_2284])).

cnf(c_14,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_34,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(sK6),sK5) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_513,plain,
    ( k4_xboole_0(X0,X1) = X0
    | u1_struct_0(sK6) != X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_34])).

cnf(c_514,plain,
    ( k4_xboole_0(u1_struct_0(sK6),sK5) = u1_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_513])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_2288,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3408,plain,
    ( r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_514,c_2288])).

cnf(c_4522,plain,
    ( r2_hidden(sK7,sK5) != iProver_top
    | v1_xboole_0(u1_struct_0(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4140,c_3408])).

cnf(c_6490,plain,
    ( v1_xboole_0(u1_struct_0(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6432,c_4522])).

cnf(c_7,plain,
    ( r2_hidden(sK2(X0,X1,X2),X0)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2290,plain,
    ( k4_xboole_0(X0,X1) = X2
    | r2_hidden(sK2(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6,plain,
    ( ~ r2_hidden(sK2(X0,X1,X2),X1)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2291,plain,
    ( k4_xboole_0(X0,X1) = X2
    | r2_hidden(sK2(X0,X1,X2),X1) != iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5348,plain,
    ( k4_xboole_0(X0,X0) = X1
    | r2_hidden(sK2(X0,X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2290,c_2291])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2296,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6844,plain,
    ( k4_xboole_0(X0,X0) = X1
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5348,c_2296])).

cnf(c_6963,plain,
    ( k4_xboole_0(X0,X0) = u1_struct_0(sK6) ),
    inference(superposition,[status(thm)],[c_6490,c_6844])).

cnf(c_7587,plain,
    ( u1_struct_0(sK6) = X0
    | r2_hidden(sK2(X1,X1,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6963,c_5348])).

cnf(c_18,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_21,plain,
    ( m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_519,plain,
    ( m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_18,c_21])).

cnf(c_2267,plain,
    ( m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_519])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2282,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4130,plain,
    ( r1_tarski(sK3(X0),u1_struct_0(X0)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2267,c_2282])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2293,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6817,plain,
    ( r2_hidden(X0,u1_struct_0(X1)) = iProver_top
    | r2_hidden(X0,sK3(X1)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4130,c_2293])).

cnf(c_22031,plain,
    ( sK3(X0) = u1_struct_0(sK6)
    | r2_hidden(sK2(X1,X1,sK3(X0)),u1_struct_0(X0)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7587,c_6817])).

cnf(c_20,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(sK3(X0)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_533,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(sK3(X0)) ),
    inference(resolution,[status(thm)],[c_18,c_20])).

cnf(c_534,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(sK3(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_533])).

cnf(c_1391,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2671,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK3(X1))
    | sK3(X1) != X0 ),
    inference(instantiation,[status(thm)],[c_1391])).

cnf(c_10321,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK6))
    | v1_xboole_0(sK3(X0))
    | sK3(X0) != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_2671])).

cnf(c_10326,plain,
    ( sK3(X0) != u1_struct_0(sK6)
    | v1_xboole_0(u1_struct_0(sK6)) != iProver_top
    | v1_xboole_0(sK3(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10321])).

cnf(c_28600,plain,
    ( r2_hidden(sK2(X1,X1,sK3(X0)),u1_struct_0(X0)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22031,c_41,c_42,c_43,c_44,c_48,c_534,c_2582,c_4522,c_5342,c_6161,c_10326])).

cnf(c_28601,plain,
    ( r2_hidden(sK2(X0,X0,sK3(X1)),u1_struct_0(X1)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_28600])).

cnf(c_10,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_2287,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_7606,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6963,c_2287])).

cnf(c_7607,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6963,c_2288])).

cnf(c_7622,plain,
    ( r2_hidden(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7606,c_7607])).

cnf(c_28612,plain,
    ( v2_struct_0(sK6) = iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_28601,c_7622])).

cnf(c_19,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_769,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK4 != X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_35])).

cnf(c_770,plain,
    ( ~ l1_pre_topc(sK4)
    | l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_769])).

cnf(c_771,plain,
    ( l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_770])).

cnf(c_45,plain,
    ( v2_struct_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_28612,c_771,c_45,c_43])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:47:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 6.57/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.57/1.48  
% 6.57/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.57/1.48  
% 6.57/1.48  ------  iProver source info
% 6.57/1.48  
% 6.57/1.48  git: date: 2020-06-30 10:37:57 +0100
% 6.57/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.57/1.48  git: non_committed_changes: false
% 6.57/1.48  git: last_make_outside_of_git: false
% 6.57/1.48  
% 6.57/1.48  ------ 
% 6.57/1.48  
% 6.57/1.48  ------ Input Options
% 6.57/1.48  
% 6.57/1.48  --out_options                           all
% 6.57/1.48  --tptp_safe_out                         true
% 6.57/1.48  --problem_path                          ""
% 6.57/1.48  --include_path                          ""
% 6.57/1.48  --clausifier                            res/vclausify_rel
% 6.57/1.48  --clausifier_options                    --mode clausify
% 6.57/1.48  --stdin                                 false
% 6.57/1.48  --stats_out                             all
% 6.57/1.48  
% 6.57/1.48  ------ General Options
% 6.57/1.48  
% 6.57/1.48  --fof                                   false
% 6.57/1.48  --time_out_real                         305.
% 6.57/1.48  --time_out_virtual                      -1.
% 6.57/1.48  --symbol_type_check                     false
% 6.57/1.48  --clausify_out                          false
% 6.57/1.48  --sig_cnt_out                           false
% 6.57/1.48  --trig_cnt_out                          false
% 6.57/1.48  --trig_cnt_out_tolerance                1.
% 6.57/1.48  --trig_cnt_out_sk_spl                   false
% 6.57/1.48  --abstr_cl_out                          false
% 6.57/1.48  
% 6.57/1.48  ------ Global Options
% 6.57/1.48  
% 6.57/1.48  --schedule                              default
% 6.57/1.48  --add_important_lit                     false
% 6.57/1.48  --prop_solver_per_cl                    1000
% 6.57/1.48  --min_unsat_core                        false
% 6.57/1.48  --soft_assumptions                      false
% 6.57/1.48  --soft_lemma_size                       3
% 6.57/1.48  --prop_impl_unit_size                   0
% 6.57/1.48  --prop_impl_unit                        []
% 6.57/1.48  --share_sel_clauses                     true
% 6.57/1.48  --reset_solvers                         false
% 6.57/1.48  --bc_imp_inh                            [conj_cone]
% 6.57/1.48  --conj_cone_tolerance                   3.
% 6.57/1.48  --extra_neg_conj                        none
% 6.57/1.48  --large_theory_mode                     true
% 6.57/1.48  --prolific_symb_bound                   200
% 6.57/1.48  --lt_threshold                          2000
% 6.57/1.48  --clause_weak_htbl                      true
% 6.57/1.48  --gc_record_bc_elim                     false
% 6.57/1.48  
% 6.57/1.48  ------ Preprocessing Options
% 6.57/1.48  
% 6.57/1.48  --preprocessing_flag                    true
% 6.57/1.48  --time_out_prep_mult                    0.1
% 6.57/1.48  --splitting_mode                        input
% 6.57/1.48  --splitting_grd                         true
% 6.57/1.48  --splitting_cvd                         false
% 6.57/1.48  --splitting_cvd_svl                     false
% 6.57/1.48  --splitting_nvd                         32
% 6.57/1.48  --sub_typing                            true
% 6.57/1.48  --prep_gs_sim                           true
% 6.57/1.48  --prep_unflatten                        true
% 6.57/1.48  --prep_res_sim                          true
% 6.57/1.48  --prep_upred                            true
% 6.57/1.48  --prep_sem_filter                       exhaustive
% 6.57/1.48  --prep_sem_filter_out                   false
% 6.57/1.48  --pred_elim                             true
% 6.57/1.48  --res_sim_input                         true
% 6.57/1.48  --eq_ax_congr_red                       true
% 6.57/1.48  --pure_diseq_elim                       true
% 6.57/1.48  --brand_transform                       false
% 6.57/1.48  --non_eq_to_eq                          false
% 6.57/1.48  --prep_def_merge                        true
% 6.57/1.48  --prep_def_merge_prop_impl              false
% 6.57/1.48  --prep_def_merge_mbd                    true
% 6.57/1.48  --prep_def_merge_tr_red                 false
% 6.57/1.48  --prep_def_merge_tr_cl                  false
% 6.57/1.48  --smt_preprocessing                     true
% 6.57/1.48  --smt_ac_axioms                         fast
% 6.57/1.48  --preprocessed_out                      false
% 6.57/1.48  --preprocessed_stats                    false
% 6.57/1.48  
% 6.57/1.48  ------ Abstraction refinement Options
% 6.57/1.48  
% 6.57/1.48  --abstr_ref                             []
% 6.57/1.48  --abstr_ref_prep                        false
% 6.57/1.48  --abstr_ref_until_sat                   false
% 6.57/1.48  --abstr_ref_sig_restrict                funpre
% 6.57/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 6.57/1.48  --abstr_ref_under                       []
% 6.57/1.48  
% 6.57/1.48  ------ SAT Options
% 6.57/1.48  
% 6.57/1.48  --sat_mode                              false
% 6.57/1.48  --sat_fm_restart_options                ""
% 6.57/1.48  --sat_gr_def                            false
% 6.57/1.48  --sat_epr_types                         true
% 6.57/1.48  --sat_non_cyclic_types                  false
% 6.57/1.48  --sat_finite_models                     false
% 6.57/1.48  --sat_fm_lemmas                         false
% 6.57/1.48  --sat_fm_prep                           false
% 6.57/1.48  --sat_fm_uc_incr                        true
% 6.57/1.48  --sat_out_model                         small
% 6.57/1.48  --sat_out_clauses                       false
% 6.57/1.48  
% 6.57/1.48  ------ QBF Options
% 6.57/1.48  
% 6.57/1.48  --qbf_mode                              false
% 6.57/1.48  --qbf_elim_univ                         false
% 6.57/1.48  --qbf_dom_inst                          none
% 6.57/1.48  --qbf_dom_pre_inst                      false
% 6.57/1.48  --qbf_sk_in                             false
% 6.57/1.48  --qbf_pred_elim                         true
% 6.57/1.48  --qbf_split                             512
% 6.57/1.48  
% 6.57/1.48  ------ BMC1 Options
% 6.57/1.48  
% 6.57/1.48  --bmc1_incremental                      false
% 6.57/1.48  --bmc1_axioms                           reachable_all
% 6.57/1.48  --bmc1_min_bound                        0
% 6.57/1.48  --bmc1_max_bound                        -1
% 6.57/1.48  --bmc1_max_bound_default                -1
% 6.57/1.48  --bmc1_symbol_reachability              true
% 6.57/1.48  --bmc1_property_lemmas                  false
% 6.57/1.48  --bmc1_k_induction                      false
% 6.57/1.48  --bmc1_non_equiv_states                 false
% 6.57/1.48  --bmc1_deadlock                         false
% 6.57/1.48  --bmc1_ucm                              false
% 6.57/1.48  --bmc1_add_unsat_core                   none
% 6.57/1.48  --bmc1_unsat_core_children              false
% 6.57/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 6.57/1.48  --bmc1_out_stat                         full
% 6.57/1.48  --bmc1_ground_init                      false
% 6.57/1.48  --bmc1_pre_inst_next_state              false
% 6.57/1.48  --bmc1_pre_inst_state                   false
% 6.57/1.48  --bmc1_pre_inst_reach_state             false
% 6.57/1.48  --bmc1_out_unsat_core                   false
% 6.57/1.48  --bmc1_aig_witness_out                  false
% 6.57/1.48  --bmc1_verbose                          false
% 6.57/1.48  --bmc1_dump_clauses_tptp                false
% 6.57/1.48  --bmc1_dump_unsat_core_tptp             false
% 6.57/1.48  --bmc1_dump_file                        -
% 6.57/1.48  --bmc1_ucm_expand_uc_limit              128
% 6.57/1.48  --bmc1_ucm_n_expand_iterations          6
% 6.57/1.48  --bmc1_ucm_extend_mode                  1
% 6.57/1.48  --bmc1_ucm_init_mode                    2
% 6.57/1.48  --bmc1_ucm_cone_mode                    none
% 6.57/1.48  --bmc1_ucm_reduced_relation_type        0
% 6.57/1.48  --bmc1_ucm_relax_model                  4
% 6.57/1.48  --bmc1_ucm_full_tr_after_sat            true
% 6.57/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 6.57/1.48  --bmc1_ucm_layered_model                none
% 6.57/1.48  --bmc1_ucm_max_lemma_size               10
% 6.57/1.48  
% 6.57/1.48  ------ AIG Options
% 6.57/1.48  
% 6.57/1.48  --aig_mode                              false
% 6.57/1.48  
% 6.57/1.48  ------ Instantiation Options
% 6.57/1.48  
% 6.57/1.48  --instantiation_flag                    true
% 6.57/1.48  --inst_sos_flag                         false
% 6.57/1.48  --inst_sos_phase                        true
% 6.57/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.57/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.57/1.48  --inst_lit_sel_side                     num_symb
% 6.57/1.48  --inst_solver_per_active                1400
% 6.57/1.48  --inst_solver_calls_frac                1.
% 6.57/1.48  --inst_passive_queue_type               priority_queues
% 6.57/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.57/1.48  --inst_passive_queues_freq              [25;2]
% 6.57/1.48  --inst_dismatching                      true
% 6.57/1.48  --inst_eager_unprocessed_to_passive     true
% 6.57/1.48  --inst_prop_sim_given                   true
% 6.57/1.48  --inst_prop_sim_new                     false
% 6.57/1.48  --inst_subs_new                         false
% 6.57/1.48  --inst_eq_res_simp                      false
% 6.57/1.48  --inst_subs_given                       false
% 6.57/1.48  --inst_orphan_elimination               true
% 6.57/1.48  --inst_learning_loop_flag               true
% 6.57/1.48  --inst_learning_start                   3000
% 6.57/1.48  --inst_learning_factor                  2
% 6.57/1.48  --inst_start_prop_sim_after_learn       3
% 6.57/1.48  --inst_sel_renew                        solver
% 6.57/1.48  --inst_lit_activity_flag                true
% 6.57/1.48  --inst_restr_to_given                   false
% 6.57/1.48  --inst_activity_threshold               500
% 6.57/1.48  --inst_out_proof                        true
% 6.57/1.48  
% 6.57/1.48  ------ Resolution Options
% 6.57/1.48  
% 6.57/1.48  --resolution_flag                       true
% 6.57/1.48  --res_lit_sel                           adaptive
% 6.57/1.48  --res_lit_sel_side                      none
% 6.57/1.48  --res_ordering                          kbo
% 6.57/1.48  --res_to_prop_solver                    active
% 6.57/1.48  --res_prop_simpl_new                    false
% 6.57/1.48  --res_prop_simpl_given                  true
% 6.57/1.48  --res_passive_queue_type                priority_queues
% 6.57/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.57/1.48  --res_passive_queues_freq               [15;5]
% 6.57/1.48  --res_forward_subs                      full
% 6.57/1.48  --res_backward_subs                     full
% 6.57/1.48  --res_forward_subs_resolution           true
% 6.57/1.48  --res_backward_subs_resolution          true
% 6.57/1.48  --res_orphan_elimination                true
% 6.57/1.48  --res_time_limit                        2.
% 6.57/1.48  --res_out_proof                         true
% 6.57/1.48  
% 6.57/1.48  ------ Superposition Options
% 6.57/1.48  
% 6.57/1.48  --superposition_flag                    true
% 6.57/1.48  --sup_passive_queue_type                priority_queues
% 6.57/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.57/1.48  --sup_passive_queues_freq               [8;1;4]
% 6.57/1.48  --demod_completeness_check              fast
% 6.57/1.48  --demod_use_ground                      true
% 6.57/1.48  --sup_to_prop_solver                    passive
% 6.57/1.48  --sup_prop_simpl_new                    true
% 6.57/1.48  --sup_prop_simpl_given                  true
% 6.57/1.48  --sup_fun_splitting                     false
% 6.57/1.48  --sup_smt_interval                      50000
% 6.57/1.48  
% 6.57/1.48  ------ Superposition Simplification Setup
% 6.57/1.48  
% 6.57/1.48  --sup_indices_passive                   []
% 6.57/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.57/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.57/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.57/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 6.57/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.57/1.48  --sup_full_bw                           [BwDemod]
% 6.57/1.48  --sup_immed_triv                        [TrivRules]
% 6.57/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.57/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.57/1.48  --sup_immed_bw_main                     []
% 6.57/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.57/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 6.57/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.57/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.57/1.48  
% 6.57/1.48  ------ Combination Options
% 6.57/1.48  
% 6.57/1.48  --comb_res_mult                         3
% 6.57/1.48  --comb_sup_mult                         2
% 6.57/1.48  --comb_inst_mult                        10
% 6.57/1.48  
% 6.57/1.48  ------ Debug Options
% 6.57/1.48  
% 6.57/1.48  --dbg_backtrace                         false
% 6.57/1.48  --dbg_dump_prop_clauses                 false
% 6.57/1.48  --dbg_dump_prop_clauses_file            -
% 6.57/1.48  --dbg_out_stat                          false
% 6.57/1.48  ------ Parsing...
% 6.57/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.57/1.48  
% 6.57/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 6.57/1.48  
% 6.57/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.57/1.48  
% 6.57/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.57/1.48  ------ Proving...
% 6.57/1.48  ------ Problem Properties 
% 6.57/1.48  
% 6.57/1.48  
% 6.57/1.48  clauses                                 36
% 6.57/1.48  conjectures                             7
% 6.57/1.48  EPR                                     10
% 6.57/1.48  Horn                                    21
% 6.57/1.48  unary                                   10
% 6.57/1.48  binary                                  9
% 6.57/1.48  lits                                    102
% 6.57/1.48  lits eq                                 5
% 6.57/1.48  fd_pure                                 0
% 6.57/1.48  fd_pseudo                               0
% 6.57/1.48  fd_cond                                 0
% 6.57/1.48  fd_pseudo_cond                          4
% 6.57/1.48  AC symbols                              0
% 6.57/1.48  
% 6.57/1.48  ------ Schedule dynamic 5 is on 
% 6.57/1.48  
% 6.57/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.57/1.48  
% 6.57/1.48  
% 6.57/1.48  ------ 
% 6.57/1.48  Current options:
% 6.57/1.48  ------ 
% 6.57/1.48  
% 6.57/1.48  ------ Input Options
% 6.57/1.48  
% 6.57/1.48  --out_options                           all
% 6.57/1.48  --tptp_safe_out                         true
% 6.57/1.48  --problem_path                          ""
% 6.57/1.48  --include_path                          ""
% 6.57/1.48  --clausifier                            res/vclausify_rel
% 6.57/1.48  --clausifier_options                    --mode clausify
% 6.57/1.48  --stdin                                 false
% 6.57/1.48  --stats_out                             all
% 6.57/1.48  
% 6.57/1.48  ------ General Options
% 6.57/1.48  
% 6.57/1.48  --fof                                   false
% 6.57/1.48  --time_out_real                         305.
% 6.57/1.48  --time_out_virtual                      -1.
% 6.57/1.48  --symbol_type_check                     false
% 6.57/1.48  --clausify_out                          false
% 6.57/1.48  --sig_cnt_out                           false
% 6.57/1.48  --trig_cnt_out                          false
% 6.57/1.48  --trig_cnt_out_tolerance                1.
% 6.57/1.48  --trig_cnt_out_sk_spl                   false
% 6.57/1.48  --abstr_cl_out                          false
% 6.57/1.48  
% 6.57/1.48  ------ Global Options
% 6.57/1.48  
% 6.57/1.48  --schedule                              default
% 6.57/1.48  --add_important_lit                     false
% 6.57/1.48  --prop_solver_per_cl                    1000
% 6.57/1.48  --min_unsat_core                        false
% 6.57/1.48  --soft_assumptions                      false
% 6.57/1.48  --soft_lemma_size                       3
% 6.57/1.48  --prop_impl_unit_size                   0
% 6.57/1.48  --prop_impl_unit                        []
% 6.57/1.48  --share_sel_clauses                     true
% 6.57/1.48  --reset_solvers                         false
% 6.57/1.48  --bc_imp_inh                            [conj_cone]
% 6.57/1.48  --conj_cone_tolerance                   3.
% 6.57/1.48  --extra_neg_conj                        none
% 6.57/1.48  --large_theory_mode                     true
% 6.57/1.48  --prolific_symb_bound                   200
% 6.57/1.48  --lt_threshold                          2000
% 6.57/1.48  --clause_weak_htbl                      true
% 6.57/1.48  --gc_record_bc_elim                     false
% 6.57/1.48  
% 6.57/1.48  ------ Preprocessing Options
% 6.57/1.48  
% 6.57/1.48  --preprocessing_flag                    true
% 6.57/1.48  --time_out_prep_mult                    0.1
% 6.57/1.48  --splitting_mode                        input
% 6.57/1.48  --splitting_grd                         true
% 6.57/1.48  --splitting_cvd                         false
% 6.57/1.48  --splitting_cvd_svl                     false
% 6.57/1.48  --splitting_nvd                         32
% 6.57/1.48  --sub_typing                            true
% 6.57/1.48  --prep_gs_sim                           true
% 6.57/1.48  --prep_unflatten                        true
% 6.57/1.48  --prep_res_sim                          true
% 6.57/1.48  --prep_upred                            true
% 6.57/1.48  --prep_sem_filter                       exhaustive
% 6.57/1.48  --prep_sem_filter_out                   false
% 6.57/1.48  --pred_elim                             true
% 6.57/1.48  --res_sim_input                         true
% 6.57/1.48  --eq_ax_congr_red                       true
% 6.57/1.48  --pure_diseq_elim                       true
% 6.57/1.48  --brand_transform                       false
% 6.57/1.48  --non_eq_to_eq                          false
% 6.57/1.48  --prep_def_merge                        true
% 6.57/1.48  --prep_def_merge_prop_impl              false
% 6.57/1.48  --prep_def_merge_mbd                    true
% 6.57/1.48  --prep_def_merge_tr_red                 false
% 6.57/1.48  --prep_def_merge_tr_cl                  false
% 6.57/1.48  --smt_preprocessing                     true
% 6.57/1.48  --smt_ac_axioms                         fast
% 6.57/1.48  --preprocessed_out                      false
% 6.57/1.48  --preprocessed_stats                    false
% 6.57/1.48  
% 6.57/1.48  ------ Abstraction refinement Options
% 6.57/1.48  
% 6.57/1.48  --abstr_ref                             []
% 6.57/1.48  --abstr_ref_prep                        false
% 6.57/1.48  --abstr_ref_until_sat                   false
% 6.57/1.48  --abstr_ref_sig_restrict                funpre
% 6.57/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 6.57/1.48  --abstr_ref_under                       []
% 6.57/1.48  
% 6.57/1.48  ------ SAT Options
% 6.57/1.48  
% 6.57/1.48  --sat_mode                              false
% 6.57/1.48  --sat_fm_restart_options                ""
% 6.57/1.48  --sat_gr_def                            false
% 6.57/1.48  --sat_epr_types                         true
% 6.57/1.48  --sat_non_cyclic_types                  false
% 6.57/1.48  --sat_finite_models                     false
% 6.57/1.48  --sat_fm_lemmas                         false
% 6.57/1.48  --sat_fm_prep                           false
% 6.57/1.48  --sat_fm_uc_incr                        true
% 6.57/1.48  --sat_out_model                         small
% 6.57/1.48  --sat_out_clauses                       false
% 6.57/1.48  
% 6.57/1.48  ------ QBF Options
% 6.57/1.48  
% 6.57/1.48  --qbf_mode                              false
% 6.57/1.48  --qbf_elim_univ                         false
% 6.57/1.48  --qbf_dom_inst                          none
% 6.57/1.48  --qbf_dom_pre_inst                      false
% 6.57/1.48  --qbf_sk_in                             false
% 6.57/1.48  --qbf_pred_elim                         true
% 6.57/1.48  --qbf_split                             512
% 6.57/1.48  
% 6.57/1.48  ------ BMC1 Options
% 6.57/1.48  
% 6.57/1.48  --bmc1_incremental                      false
% 6.57/1.48  --bmc1_axioms                           reachable_all
% 6.57/1.48  --bmc1_min_bound                        0
% 6.57/1.48  --bmc1_max_bound                        -1
% 6.57/1.48  --bmc1_max_bound_default                -1
% 6.57/1.48  --bmc1_symbol_reachability              true
% 6.57/1.48  --bmc1_property_lemmas                  false
% 6.57/1.48  --bmc1_k_induction                      false
% 6.57/1.48  --bmc1_non_equiv_states                 false
% 6.57/1.48  --bmc1_deadlock                         false
% 6.57/1.48  --bmc1_ucm                              false
% 6.57/1.48  --bmc1_add_unsat_core                   none
% 6.57/1.48  --bmc1_unsat_core_children              false
% 6.57/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 6.57/1.48  --bmc1_out_stat                         full
% 6.57/1.48  --bmc1_ground_init                      false
% 6.57/1.48  --bmc1_pre_inst_next_state              false
% 6.57/1.48  --bmc1_pre_inst_state                   false
% 6.57/1.48  --bmc1_pre_inst_reach_state             false
% 6.57/1.48  --bmc1_out_unsat_core                   false
% 6.57/1.48  --bmc1_aig_witness_out                  false
% 6.57/1.48  --bmc1_verbose                          false
% 6.57/1.48  --bmc1_dump_clauses_tptp                false
% 6.57/1.48  --bmc1_dump_unsat_core_tptp             false
% 6.57/1.48  --bmc1_dump_file                        -
% 6.57/1.48  --bmc1_ucm_expand_uc_limit              128
% 6.57/1.48  --bmc1_ucm_n_expand_iterations          6
% 6.57/1.48  --bmc1_ucm_extend_mode                  1
% 6.57/1.48  --bmc1_ucm_init_mode                    2
% 6.57/1.48  --bmc1_ucm_cone_mode                    none
% 6.57/1.48  --bmc1_ucm_reduced_relation_type        0
% 6.57/1.48  --bmc1_ucm_relax_model                  4
% 6.57/1.48  --bmc1_ucm_full_tr_after_sat            true
% 6.57/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 6.57/1.48  --bmc1_ucm_layered_model                none
% 6.57/1.48  --bmc1_ucm_max_lemma_size               10
% 6.57/1.48  
% 6.57/1.48  ------ AIG Options
% 6.57/1.48  
% 6.57/1.48  --aig_mode                              false
% 6.57/1.48  
% 6.57/1.48  ------ Instantiation Options
% 6.57/1.48  
% 6.57/1.48  --instantiation_flag                    true
% 6.57/1.48  --inst_sos_flag                         false
% 6.57/1.48  --inst_sos_phase                        true
% 6.57/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.57/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.57/1.48  --inst_lit_sel_side                     none
% 6.57/1.48  --inst_solver_per_active                1400
% 6.57/1.48  --inst_solver_calls_frac                1.
% 6.57/1.48  --inst_passive_queue_type               priority_queues
% 6.57/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.57/1.48  --inst_passive_queues_freq              [25;2]
% 6.57/1.48  --inst_dismatching                      true
% 6.57/1.48  --inst_eager_unprocessed_to_passive     true
% 6.57/1.48  --inst_prop_sim_given                   true
% 6.57/1.48  --inst_prop_sim_new                     false
% 6.57/1.48  --inst_subs_new                         false
% 6.57/1.48  --inst_eq_res_simp                      false
% 6.57/1.48  --inst_subs_given                       false
% 6.57/1.48  --inst_orphan_elimination               true
% 6.57/1.48  --inst_learning_loop_flag               true
% 6.57/1.48  --inst_learning_start                   3000
% 6.57/1.48  --inst_learning_factor                  2
% 6.57/1.48  --inst_start_prop_sim_after_learn       3
% 6.57/1.48  --inst_sel_renew                        solver
% 6.57/1.48  --inst_lit_activity_flag                true
% 6.57/1.48  --inst_restr_to_given                   false
% 6.57/1.48  --inst_activity_threshold               500
% 6.57/1.48  --inst_out_proof                        true
% 6.57/1.48  
% 6.57/1.48  ------ Resolution Options
% 6.57/1.48  
% 6.57/1.48  --resolution_flag                       false
% 6.57/1.48  --res_lit_sel                           adaptive
% 6.57/1.48  --res_lit_sel_side                      none
% 6.57/1.48  --res_ordering                          kbo
% 6.57/1.48  --res_to_prop_solver                    active
% 6.57/1.48  --res_prop_simpl_new                    false
% 6.57/1.48  --res_prop_simpl_given                  true
% 6.57/1.48  --res_passive_queue_type                priority_queues
% 6.57/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.57/1.48  --res_passive_queues_freq               [15;5]
% 6.57/1.48  --res_forward_subs                      full
% 6.57/1.48  --res_backward_subs                     full
% 6.57/1.48  --res_forward_subs_resolution           true
% 6.57/1.48  --res_backward_subs_resolution          true
% 6.57/1.48  --res_orphan_elimination                true
% 6.57/1.48  --res_time_limit                        2.
% 6.57/1.48  --res_out_proof                         true
% 6.57/1.48  
% 6.57/1.48  ------ Superposition Options
% 6.57/1.48  
% 6.57/1.48  --superposition_flag                    true
% 6.57/1.48  --sup_passive_queue_type                priority_queues
% 6.57/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.57/1.48  --sup_passive_queues_freq               [8;1;4]
% 6.57/1.48  --demod_completeness_check              fast
% 6.57/1.48  --demod_use_ground                      true
% 6.57/1.48  --sup_to_prop_solver                    passive
% 6.57/1.48  --sup_prop_simpl_new                    true
% 6.57/1.48  --sup_prop_simpl_given                  true
% 6.57/1.48  --sup_fun_splitting                     false
% 6.57/1.48  --sup_smt_interval                      50000
% 6.57/1.48  
% 6.57/1.48  ------ Superposition Simplification Setup
% 6.57/1.48  
% 6.57/1.48  --sup_indices_passive                   []
% 6.57/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.57/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.57/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.57/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 6.57/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.57/1.48  --sup_full_bw                           [BwDemod]
% 6.57/1.48  --sup_immed_triv                        [TrivRules]
% 6.57/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.57/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.57/1.48  --sup_immed_bw_main                     []
% 6.57/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.57/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 6.57/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.57/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.57/1.48  
% 6.57/1.48  ------ Combination Options
% 6.57/1.48  
% 6.57/1.48  --comb_res_mult                         3
% 6.57/1.48  --comb_sup_mult                         2
% 6.57/1.48  --comb_inst_mult                        10
% 6.57/1.48  
% 6.57/1.48  ------ Debug Options
% 6.57/1.48  
% 6.57/1.48  --dbg_backtrace                         false
% 6.57/1.48  --dbg_dump_prop_clauses                 false
% 6.57/1.48  --dbg_dump_prop_clauses_file            -
% 6.57/1.48  --dbg_out_stat                          false
% 6.57/1.48  
% 6.57/1.48  
% 6.57/1.48  
% 6.57/1.48  
% 6.57/1.48  ------ Proving...
% 6.57/1.48  
% 6.57/1.48  
% 6.57/1.48  % SZS status Theorem for theBenchmark.p
% 6.57/1.48  
% 6.57/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 6.57/1.48  
% 6.57/1.48  fof(f15,axiom,(
% 6.57/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (~r2_hidden(X2,X1) => r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)))))),
% 6.57/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.57/1.48  
% 6.57/1.48  fof(f38,plain,(
% 6.57/1.48    ! [X0] : (! [X1] : (! [X2] : ((r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2) | r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 6.57/1.48    inference(ennf_transformation,[],[f15])).
% 6.57/1.48  
% 6.57/1.48  fof(f39,plain,(
% 6.57/1.48    ! [X0] : (! [X1] : (! [X2] : (r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2) | r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 6.57/1.48    inference(flattening,[],[f38])).
% 6.57/1.48  
% 6.57/1.48  fof(f97,plain,(
% 6.57/1.48    ( ! [X2,X0,X1] : (r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2) | r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 6.57/1.48    inference(cnf_transformation,[],[f39])).
% 6.57/1.48  
% 6.57/1.48  fof(f16,axiom,(
% 6.57/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 6.57/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.57/1.48  
% 6.57/1.48  fof(f40,plain,(
% 6.57/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 6.57/1.48    inference(ennf_transformation,[],[f16])).
% 6.57/1.48  
% 6.57/1.48  fof(f41,plain,(
% 6.57/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 6.57/1.48    inference(flattening,[],[f40])).
% 6.57/1.48  
% 6.57/1.48  fof(f98,plain,(
% 6.57/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 6.57/1.48    inference(cnf_transformation,[],[f41])).
% 6.57/1.48  
% 6.57/1.48  fof(f113,plain,(
% 6.57/1.48    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 6.57/1.48    inference(equality_resolution,[],[f98])).
% 6.57/1.48  
% 6.57/1.48  fof(f17,conjecture,(
% 6.57/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_xboole_0(u1_struct_0(X2),X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3))))))),
% 6.57/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.57/1.48  
% 6.57/1.48  fof(f18,negated_conjecture,(
% 6.57/1.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_xboole_0(u1_struct_0(X2),X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3))))))),
% 6.57/1.48    inference(negated_conjecture,[],[f17])).
% 6.57/1.48  
% 6.57/1.48  fof(f42,plain,(
% 6.57/1.48    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (~r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),X1)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 6.57/1.48    inference(ennf_transformation,[],[f18])).
% 6.57/1.48  
% 6.57/1.48  fof(f43,plain,(
% 6.57/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),X1) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 6.57/1.48    inference(flattening,[],[f42])).
% 6.57/1.48  
% 6.57/1.48  fof(f65,plain,(
% 6.57/1.48    ( ! [X2,X0,X1] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) => (~r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),sK7) & m1_subset_1(sK7,u1_struct_0(X2)))) )),
% 6.57/1.48    introduced(choice_axiom,[])).
% 6.57/1.48  
% 6.57/1.48  fof(f64,plain,(
% 6.57/1.48    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),X1) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (~r1_tmap_1(sK6,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),sK6),X3) & m1_subset_1(X3,u1_struct_0(sK6))) & r1_xboole_0(u1_struct_0(sK6),X1) & m1_pre_topc(sK6,X0) & ~v2_struct_0(sK6))) )),
% 6.57/1.48    introduced(choice_axiom,[])).
% 6.57/1.48  
% 6.57/1.48  fof(f63,plain,(
% 6.57/1.48    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),X1) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(X0,sK5),k2_tmap_1(X0,k6_tmap_1(X0,sK5),k7_tmap_1(X0,sK5),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),sK5) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 6.57/1.48    introduced(choice_axiom,[])).
% 6.57/1.48  
% 6.57/1.48  fof(f62,plain,(
% 6.57/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),X1) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(sK4,X1),k2_tmap_1(sK4,k6_tmap_1(sK4,X1),k7_tmap_1(sK4,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),X1) & m1_pre_topc(X2,sK4) & ~v2_struct_0(X2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 6.57/1.48    introduced(choice_axiom,[])).
% 6.57/1.48  
% 6.57/1.48  fof(f66,plain,(
% 6.57/1.48    (((~r1_tmap_1(sK6,k6_tmap_1(sK4,sK5),k2_tmap_1(sK4,k6_tmap_1(sK4,sK5),k7_tmap_1(sK4,sK5),sK6),sK7) & m1_subset_1(sK7,u1_struct_0(sK6))) & r1_xboole_0(u1_struct_0(sK6),sK5) & m1_pre_topc(sK6,sK4) & ~v2_struct_0(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)),
% 6.57/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f43,f65,f64,f63,f62])).
% 6.57/1.48  
% 6.57/1.48  fof(f104,plain,(
% 6.57/1.48    m1_pre_topc(sK6,sK4)),
% 6.57/1.48    inference(cnf_transformation,[],[f66])).
% 6.57/1.48  
% 6.57/1.48  fof(f99,plain,(
% 6.57/1.48    ~v2_struct_0(sK4)),
% 6.57/1.48    inference(cnf_transformation,[],[f66])).
% 6.57/1.48  
% 6.57/1.48  fof(f100,plain,(
% 6.57/1.48    v2_pre_topc(sK4)),
% 6.57/1.48    inference(cnf_transformation,[],[f66])).
% 6.57/1.48  
% 6.57/1.48  fof(f101,plain,(
% 6.57/1.48    l1_pre_topc(sK4)),
% 6.57/1.48    inference(cnf_transformation,[],[f66])).
% 6.57/1.48  
% 6.57/1.48  fof(f103,plain,(
% 6.57/1.48    ~v2_struct_0(sK6)),
% 6.57/1.48    inference(cnf_transformation,[],[f66])).
% 6.57/1.48  
% 6.57/1.48  fof(f11,axiom,(
% 6.57/1.48    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 6.57/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.57/1.48  
% 6.57/1.48  fof(f30,plain,(
% 6.57/1.48    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 6.57/1.48    inference(ennf_transformation,[],[f11])).
% 6.57/1.48  
% 6.57/1.48  fof(f31,plain,(
% 6.57/1.48    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 6.57/1.48    inference(flattening,[],[f30])).
% 6.57/1.48  
% 6.57/1.48  fof(f89,plain,(
% 6.57/1.48    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 6.57/1.48    inference(cnf_transformation,[],[f31])).
% 6.57/1.48  
% 6.57/1.48  fof(f107,plain,(
% 6.57/1.48    ~r1_tmap_1(sK6,k6_tmap_1(sK4,sK5),k2_tmap_1(sK4,k6_tmap_1(sK4,sK5),k7_tmap_1(sK4,sK5),sK6),sK7)),
% 6.57/1.48    inference(cnf_transformation,[],[f66])).
% 6.57/1.48  
% 6.57/1.48  fof(f102,plain,(
% 6.57/1.48    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))),
% 6.57/1.48    inference(cnf_transformation,[],[f66])).
% 6.57/1.48  
% 6.57/1.48  fof(f106,plain,(
% 6.57/1.48    m1_subset_1(sK7,u1_struct_0(sK6))),
% 6.57/1.48    inference(cnf_transformation,[],[f66])).
% 6.57/1.48  
% 6.57/1.48  fof(f12,axiom,(
% 6.57/1.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))))),
% 6.57/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.57/1.48  
% 6.57/1.48  fof(f21,plain,(
% 6.57/1.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))))),
% 6.57/1.48    inference(pure_predicate_removal,[],[f12])).
% 6.57/1.48  
% 6.57/1.48  fof(f32,plain,(
% 6.57/1.48    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 6.57/1.48    inference(ennf_transformation,[],[f21])).
% 6.57/1.48  
% 6.57/1.48  fof(f33,plain,(
% 6.57/1.48    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 6.57/1.48    inference(flattening,[],[f32])).
% 6.57/1.48  
% 6.57/1.48  fof(f91,plain,(
% 6.57/1.48    ( ! [X0,X1] : (l1_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 6.57/1.48    inference(cnf_transformation,[],[f33])).
% 6.57/1.48  
% 6.57/1.48  fof(f13,axiom,(
% 6.57/1.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 6.57/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.57/1.48  
% 6.57/1.48  fof(f34,plain,(
% 6.57/1.48    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 6.57/1.48    inference(ennf_transformation,[],[f13])).
% 6.57/1.48  
% 6.57/1.48  fof(f35,plain,(
% 6.57/1.48    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 6.57/1.48    inference(flattening,[],[f34])).
% 6.57/1.48  
% 6.57/1.48  fof(f92,plain,(
% 6.57/1.48    ( ! [X0,X1] : (v1_funct_1(k7_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 6.57/1.48    inference(cnf_transformation,[],[f35])).
% 6.57/1.48  
% 6.57/1.48  fof(f14,axiom,(
% 6.57/1.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))))),
% 6.57/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.57/1.48  
% 6.57/1.48  fof(f20,plain,(
% 6.57/1.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))))),
% 6.57/1.48    inference(pure_predicate_removal,[],[f14])).
% 6.57/1.48  
% 6.57/1.48  fof(f36,plain,(
% 6.57/1.48    ! [X0,X1] : ((v2_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 6.57/1.48    inference(ennf_transformation,[],[f20])).
% 6.57/1.48  
% 6.57/1.48  fof(f37,plain,(
% 6.57/1.48    ! [X0,X1] : ((v2_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 6.57/1.48    inference(flattening,[],[f36])).
% 6.57/1.48  
% 6.57/1.48  fof(f96,plain,(
% 6.57/1.48    ( ! [X0,X1] : (v2_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 6.57/1.48    inference(cnf_transformation,[],[f37])).
% 6.57/1.48  
% 6.57/1.48  fof(f94,plain,(
% 6.57/1.48    ( ! [X0,X1] : (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 6.57/1.48    inference(cnf_transformation,[],[f35])).
% 6.57/1.48  
% 6.57/1.48  fof(f93,plain,(
% 6.57/1.48    ( ! [X0,X1] : (v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 6.57/1.48    inference(cnf_transformation,[],[f35])).
% 6.57/1.48  
% 6.57/1.48  fof(f95,plain,(
% 6.57/1.48    ( ! [X0,X1] : (~v2_struct_0(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 6.57/1.48    inference(cnf_transformation,[],[f37])).
% 6.57/1.48  
% 6.57/1.48  fof(f6,axiom,(
% 6.57/1.48    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 6.57/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.57/1.48  
% 6.57/1.48  fof(f24,plain,(
% 6.57/1.48    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 6.57/1.48    inference(ennf_transformation,[],[f6])).
% 6.57/1.48  
% 6.57/1.48  fof(f25,plain,(
% 6.57/1.48    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 6.57/1.48    inference(flattening,[],[f24])).
% 6.57/1.48  
% 6.57/1.48  fof(f82,plain,(
% 6.57/1.48    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 6.57/1.48    inference(cnf_transformation,[],[f25])).
% 6.57/1.48  
% 6.57/1.48  fof(f5,axiom,(
% 6.57/1.48    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 6.57/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.57/1.48  
% 6.57/1.48  fof(f19,plain,(
% 6.57/1.48    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(X0,X1) = X0)),
% 6.57/1.48    inference(unused_predicate_definition_removal,[],[f5])).
% 6.57/1.48  
% 6.57/1.48  fof(f23,plain,(
% 6.57/1.48    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 6.57/1.48    inference(ennf_transformation,[],[f19])).
% 6.57/1.48  
% 6.57/1.48  fof(f81,plain,(
% 6.57/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 6.57/1.48    inference(cnf_transformation,[],[f23])).
% 6.57/1.48  
% 6.57/1.48  fof(f105,plain,(
% 6.57/1.48    r1_xboole_0(u1_struct_0(sK6),sK5)),
% 6.57/1.48    inference(cnf_transformation,[],[f66])).
% 6.57/1.48  
% 6.57/1.48  fof(f3,axiom,(
% 6.57/1.48    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 6.57/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.57/1.48  
% 6.57/1.48  fof(f52,plain,(
% 6.57/1.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 6.57/1.48    inference(nnf_transformation,[],[f3])).
% 6.57/1.48  
% 6.57/1.48  fof(f53,plain,(
% 6.57/1.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 6.57/1.48    inference(flattening,[],[f52])).
% 6.57/1.48  
% 6.57/1.48  fof(f54,plain,(
% 6.57/1.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 6.57/1.48    inference(rectify,[],[f53])).
% 6.57/1.48  
% 6.57/1.48  fof(f55,plain,(
% 6.57/1.48    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 6.57/1.48    introduced(choice_axiom,[])).
% 6.57/1.48  
% 6.57/1.48  fof(f56,plain,(
% 6.57/1.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 6.57/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f54,f55])).
% 6.57/1.48  
% 6.57/1.48  fof(f73,plain,(
% 6.57/1.48    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 6.57/1.48    inference(cnf_transformation,[],[f56])).
% 6.57/1.48  
% 6.57/1.48  fof(f109,plain,(
% 6.57/1.48    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 6.57/1.48    inference(equality_resolution,[],[f73])).
% 6.57/1.48  
% 6.57/1.48  fof(f75,plain,(
% 6.57/1.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 6.57/1.48    inference(cnf_transformation,[],[f56])).
% 6.57/1.48  
% 6.57/1.48  fof(f76,plain,(
% 6.57/1.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 6.57/1.48    inference(cnf_transformation,[],[f56])).
% 6.57/1.48  
% 6.57/1.48  fof(f1,axiom,(
% 6.57/1.48    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 6.57/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.57/1.48  
% 6.57/1.48  fof(f44,plain,(
% 6.57/1.48    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 6.57/1.48    inference(nnf_transformation,[],[f1])).
% 6.57/1.48  
% 6.57/1.48  fof(f45,plain,(
% 6.57/1.48    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 6.57/1.48    inference(rectify,[],[f44])).
% 6.57/1.48  
% 6.57/1.48  fof(f46,plain,(
% 6.57/1.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 6.57/1.48    introduced(choice_axiom,[])).
% 6.57/1.48  
% 6.57/1.48  fof(f47,plain,(
% 6.57/1.48    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 6.57/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f45,f46])).
% 6.57/1.48  
% 6.57/1.48  fof(f67,plain,(
% 6.57/1.48    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 6.57/1.48    inference(cnf_transformation,[],[f47])).
% 6.57/1.48  
% 6.57/1.48  fof(f8,axiom,(
% 6.57/1.48    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 6.57/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.57/1.48  
% 6.57/1.48  fof(f26,plain,(
% 6.57/1.48    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 6.57/1.48    inference(ennf_transformation,[],[f8])).
% 6.57/1.48  
% 6.57/1.48  fof(f85,plain,(
% 6.57/1.48    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 6.57/1.48    inference(cnf_transformation,[],[f26])).
% 6.57/1.48  
% 6.57/1.48  fof(f10,axiom,(
% 6.57/1.48    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 6.57/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.57/1.48  
% 6.57/1.48  fof(f28,plain,(
% 6.57/1.48    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 6.57/1.48    inference(ennf_transformation,[],[f10])).
% 6.57/1.48  
% 6.57/1.48  fof(f29,plain,(
% 6.57/1.48    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 6.57/1.48    inference(flattening,[],[f28])).
% 6.57/1.48  
% 6.57/1.48  fof(f60,plain,(
% 6.57/1.48    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_xboole_0(sK3(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 6.57/1.48    introduced(choice_axiom,[])).
% 6.57/1.48  
% 6.57/1.48  fof(f61,plain,(
% 6.57/1.48    ! [X0] : ((~v1_xboole_0(sK3(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 6.57/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f60])).
% 6.57/1.48  
% 6.57/1.48  fof(f87,plain,(
% 6.57/1.48    ( ! [X0] : (m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 6.57/1.48    inference(cnf_transformation,[],[f61])).
% 6.57/1.48  
% 6.57/1.48  fof(f7,axiom,(
% 6.57/1.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 6.57/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.57/1.48  
% 6.57/1.48  fof(f59,plain,(
% 6.57/1.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 6.57/1.48    inference(nnf_transformation,[],[f7])).
% 6.57/1.48  
% 6.57/1.48  fof(f83,plain,(
% 6.57/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 6.57/1.48    inference(cnf_transformation,[],[f59])).
% 6.57/1.48  
% 6.57/1.48  fof(f2,axiom,(
% 6.57/1.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 6.57/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.57/1.48  
% 6.57/1.48  fof(f22,plain,(
% 6.57/1.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 6.57/1.48    inference(ennf_transformation,[],[f2])).
% 6.57/1.48  
% 6.57/1.48  fof(f48,plain,(
% 6.57/1.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 6.57/1.48    inference(nnf_transformation,[],[f22])).
% 6.57/1.48  
% 6.57/1.48  fof(f49,plain,(
% 6.57/1.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 6.57/1.48    inference(rectify,[],[f48])).
% 6.57/1.48  
% 6.57/1.48  fof(f50,plain,(
% 6.57/1.48    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 6.57/1.48    introduced(choice_axiom,[])).
% 6.57/1.48  
% 6.57/1.48  fof(f51,plain,(
% 6.57/1.48    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 6.57/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f49,f50])).
% 6.57/1.48  
% 6.57/1.48  fof(f69,plain,(
% 6.57/1.48    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 6.57/1.48    inference(cnf_transformation,[],[f51])).
% 6.57/1.48  
% 6.57/1.48  fof(f88,plain,(
% 6.57/1.48    ( ! [X0] : (~v1_xboole_0(sK3(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 6.57/1.48    inference(cnf_transformation,[],[f61])).
% 6.57/1.48  
% 6.57/1.48  fof(f72,plain,(
% 6.57/1.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 6.57/1.48    inference(cnf_transformation,[],[f56])).
% 6.57/1.48  
% 6.57/1.48  fof(f110,plain,(
% 6.57/1.48    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 6.57/1.48    inference(equality_resolution,[],[f72])).
% 6.57/1.48  
% 6.57/1.48  fof(f9,axiom,(
% 6.57/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 6.57/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.57/1.48  
% 6.57/1.48  fof(f27,plain,(
% 6.57/1.48    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 6.57/1.48    inference(ennf_transformation,[],[f9])).
% 6.57/1.48  
% 6.57/1.48  fof(f86,plain,(
% 6.57/1.48    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 6.57/1.48    inference(cnf_transformation,[],[f27])).
% 6.57/1.48  
% 6.57/1.48  cnf(c_30,plain,
% 6.57/1.48      ( r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)
% 6.57/1.48      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 6.57/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 6.57/1.48      | r2_hidden(X2,X1)
% 6.57/1.48      | ~ v2_pre_topc(X0)
% 6.57/1.48      | v2_struct_0(X0)
% 6.57/1.48      | ~ l1_pre_topc(X0) ),
% 6.57/1.48      inference(cnf_transformation,[],[f97]) ).
% 6.57/1.48  
% 6.57/1.48  cnf(c_2275,plain,
% 6.57/1.48      ( r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2) = iProver_top
% 6.57/1.48      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 6.57/1.48      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 6.57/1.48      | r2_hidden(X2,X1) = iProver_top
% 6.57/1.48      | v2_pre_topc(X0) != iProver_top
% 6.57/1.48      | v2_struct_0(X0) = iProver_top
% 6.57/1.48      | l1_pre_topc(X0) != iProver_top ),
% 6.57/1.48      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 6.57/1.48  
% 6.57/1.48  cnf(c_31,plain,
% 6.57/1.48      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 6.57/1.48      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 6.57/1.48      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 6.57/1.48      | ~ m1_pre_topc(X4,X0)
% 6.57/1.48      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 6.57/1.48      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 6.57/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 6.57/1.48      | ~ v1_funct_1(X2)
% 6.57/1.48      | ~ v2_pre_topc(X1)
% 6.57/1.48      | ~ v2_pre_topc(X0)
% 6.57/1.48      | v2_struct_0(X1)
% 6.57/1.48      | v2_struct_0(X0)
% 6.57/1.48      | v2_struct_0(X4)
% 6.57/1.48      | ~ l1_pre_topc(X1)
% 6.57/1.48      | ~ l1_pre_topc(X0) ),
% 6.57/1.48      inference(cnf_transformation,[],[f113]) ).
% 6.57/1.48  
% 6.57/1.48  cnf(c_35,negated_conjecture,
% 6.57/1.48      ( m1_pre_topc(sK6,sK4) ),
% 6.57/1.48      inference(cnf_transformation,[],[f104]) ).
% 6.57/1.48  
% 6.57/1.48  cnf(c_780,plain,
% 6.57/1.48      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 6.57/1.48      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 6.57/1.48      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 6.57/1.48      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 6.57/1.48      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 6.57/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 6.57/1.48      | ~ v1_funct_1(X2)
% 6.57/1.48      | ~ v2_pre_topc(X0)
% 6.57/1.48      | ~ v2_pre_topc(X1)
% 6.57/1.48      | v2_struct_0(X0)
% 6.57/1.48      | v2_struct_0(X1)
% 6.57/1.48      | v2_struct_0(X4)
% 6.57/1.48      | ~ l1_pre_topc(X0)
% 6.57/1.48      | ~ l1_pre_topc(X1)
% 6.57/1.48      | sK4 != X0
% 6.57/1.48      | sK6 != X4 ),
% 6.57/1.48      inference(resolution_lifted,[status(thm)],[c_31,c_35]) ).
% 6.57/1.48  
% 6.57/1.48  cnf(c_781,plain,
% 6.57/1.48      ( ~ r1_tmap_1(sK4,X0,X1,X2)
% 6.57/1.48      | r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,X1,sK6),X2)
% 6.57/1.48      | ~ v1_funct_2(X1,u1_struct_0(sK4),u1_struct_0(X0))
% 6.57/1.48      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 6.57/1.48      | ~ m1_subset_1(X2,u1_struct_0(sK6))
% 6.57/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
% 6.57/1.48      | ~ v1_funct_1(X1)
% 6.57/1.48      | ~ v2_pre_topc(X0)
% 6.57/1.48      | ~ v2_pre_topc(sK4)
% 6.57/1.48      | v2_struct_0(X0)
% 6.57/1.48      | v2_struct_0(sK4)
% 6.57/1.48      | v2_struct_0(sK6)
% 6.57/1.48      | ~ l1_pre_topc(X0)
% 6.57/1.48      | ~ l1_pre_topc(sK4) ),
% 6.57/1.48      inference(unflattening,[status(thm)],[c_780]) ).
% 6.57/1.48  
% 6.57/1.48  cnf(c_40,negated_conjecture,
% 6.57/1.48      ( ~ v2_struct_0(sK4) ),
% 6.57/1.48      inference(cnf_transformation,[],[f99]) ).
% 6.57/1.48  
% 6.57/1.48  cnf(c_39,negated_conjecture,
% 6.57/1.48      ( v2_pre_topc(sK4) ),
% 6.57/1.48      inference(cnf_transformation,[],[f100]) ).
% 6.57/1.48  
% 6.57/1.48  cnf(c_38,negated_conjecture,
% 6.57/1.48      ( l1_pre_topc(sK4) ),
% 6.57/1.48      inference(cnf_transformation,[],[f101]) ).
% 6.57/1.48  
% 6.57/1.48  cnf(c_36,negated_conjecture,
% 6.57/1.48      ( ~ v2_struct_0(sK6) ),
% 6.57/1.48      inference(cnf_transformation,[],[f103]) ).
% 6.57/1.48  
% 6.57/1.48  cnf(c_785,plain,
% 6.57/1.48      ( ~ l1_pre_topc(X0)
% 6.57/1.48      | v2_struct_0(X0)
% 6.57/1.48      | ~ r1_tmap_1(sK4,X0,X1,X2)
% 6.57/1.48      | r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,X1,sK6),X2)
% 6.57/1.48      | ~ v1_funct_2(X1,u1_struct_0(sK4),u1_struct_0(X0))
% 6.57/1.48      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 6.57/1.48      | ~ m1_subset_1(X2,u1_struct_0(sK6))
% 6.57/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
% 6.57/1.48      | ~ v1_funct_1(X1)
% 6.57/1.48      | ~ v2_pre_topc(X0) ),
% 6.57/1.48      inference(global_propositional_subsumption,
% 6.57/1.48                [status(thm)],
% 6.57/1.48                [c_781,c_40,c_39,c_38,c_36]) ).
% 6.57/1.48  
% 6.57/1.48  cnf(c_786,plain,
% 6.57/1.48      ( ~ r1_tmap_1(sK4,X0,X1,X2)
% 6.57/1.48      | r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,X1,sK6),X2)
% 6.57/1.48      | ~ v1_funct_2(X1,u1_struct_0(sK4),u1_struct_0(X0))
% 6.57/1.48      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 6.57/1.48      | ~ m1_subset_1(X2,u1_struct_0(sK6))
% 6.57/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
% 6.57/1.48      | ~ v1_funct_1(X1)
% 6.57/1.48      | ~ v2_pre_topc(X0)
% 6.57/1.48      | v2_struct_0(X0)
% 6.57/1.48      | ~ l1_pre_topc(X0) ),
% 6.57/1.48      inference(renaming,[status(thm)],[c_785]) ).
% 6.57/1.48  
% 6.57/1.48  cnf(c_22,plain,
% 6.57/1.48      ( ~ m1_pre_topc(X0,X1)
% 6.57/1.48      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 6.57/1.48      | m1_subset_1(X2,u1_struct_0(X1))
% 6.57/1.48      | v2_struct_0(X1)
% 6.57/1.48      | v2_struct_0(X0)
% 6.57/1.48      | ~ l1_pre_topc(X1) ),
% 6.57/1.48      inference(cnf_transformation,[],[f89]) ).
% 6.57/1.48  
% 6.57/1.48  cnf(c_751,plain,
% 6.57/1.48      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 6.57/1.48      | m1_subset_1(X0,u1_struct_0(X2))
% 6.57/1.48      | v2_struct_0(X1)
% 6.57/1.48      | v2_struct_0(X2)
% 6.57/1.48      | ~ l1_pre_topc(X2)
% 6.57/1.48      | sK4 != X2
% 6.57/1.48      | sK6 != X1 ),
% 6.57/1.48      inference(resolution_lifted,[status(thm)],[c_22,c_35]) ).
% 6.57/1.48  
% 6.57/1.48  cnf(c_752,plain,
% 6.57/1.48      ( m1_subset_1(X0,u1_struct_0(sK4))
% 6.57/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 6.57/1.48      | v2_struct_0(sK4)
% 6.57/1.48      | v2_struct_0(sK6)
% 6.57/1.48      | ~ l1_pre_topc(sK4) ),
% 6.57/1.48      inference(unflattening,[status(thm)],[c_751]) ).
% 6.57/1.48  
% 6.57/1.48  cnf(c_756,plain,
% 6.57/1.48      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 6.57/1.48      | m1_subset_1(X0,u1_struct_0(sK4)) ),
% 6.57/1.48      inference(global_propositional_subsumption,
% 6.57/1.48                [status(thm)],
% 6.57/1.48                [c_752,c_40,c_38,c_36]) ).
% 6.57/1.48  
% 6.57/1.48  cnf(c_757,plain,
% 6.57/1.48      ( m1_subset_1(X0,u1_struct_0(sK4))
% 6.57/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
% 6.57/1.48      inference(renaming,[status(thm)],[c_756]) ).
% 6.57/1.48  
% 6.57/1.48  cnf(c_801,plain,
% 6.57/1.48      ( ~ r1_tmap_1(sK4,X0,X1,X2)
% 6.57/1.48      | r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,X1,sK6),X2)
% 6.57/1.48      | ~ v1_funct_2(X1,u1_struct_0(sK4),u1_struct_0(X0))
% 6.57/1.48      | ~ m1_subset_1(X2,u1_struct_0(sK6))
% 6.57/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
% 6.57/1.48      | ~ v1_funct_1(X1)
% 6.57/1.48      | ~ v2_pre_topc(X0)
% 6.57/1.48      | v2_struct_0(X0)
% 6.57/1.48      | ~ l1_pre_topc(X0) ),
% 6.57/1.48      inference(forward_subsumption_resolution,
% 6.57/1.48                [status(thm)],
% 6.57/1.48                [c_786,c_757]) ).
% 6.57/1.48  
% 6.57/1.48  cnf(c_2263,plain,
% 6.57/1.48      ( r1_tmap_1(sK4,X0,X1,X2) != iProver_top
% 6.57/1.48      | r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,X1,sK6),X2) = iProver_top
% 6.57/1.48      | v1_funct_2(X1,u1_struct_0(sK4),u1_struct_0(X0)) != iProver_top
% 6.57/1.48      | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top
% 6.57/1.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 6.57/1.48      | v1_funct_1(X1) != iProver_top
% 6.57/1.48      | v2_pre_topc(X0) != iProver_top
% 6.57/1.48      | v2_struct_0(X0) = iProver_top
% 6.57/1.48      | l1_pre_topc(X0) != iProver_top ),
% 6.57/1.48      inference(predicate_to_equality,[status(thm)],[c_801]) ).
% 6.57/1.48  
% 6.57/1.48  cnf(c_32,negated_conjecture,
% 6.57/1.48      ( ~ r1_tmap_1(sK6,k6_tmap_1(sK4,sK5),k2_tmap_1(sK4,k6_tmap_1(sK4,sK5),k7_tmap_1(sK4,sK5),sK6),sK7) ),
% 6.57/1.48      inference(cnf_transformation,[],[f107]) ).
% 6.57/1.48  
% 6.57/1.48  cnf(c_2274,plain,
% 6.57/1.48      ( r1_tmap_1(sK6,k6_tmap_1(sK4,sK5),k2_tmap_1(sK4,k6_tmap_1(sK4,sK5),k7_tmap_1(sK4,sK5),sK6),sK7) != iProver_top ),
% 6.57/1.48      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 6.57/1.48  
% 6.57/1.48  cnf(c_2690,plain,
% 6.57/1.48      ( r1_tmap_1(sK4,k6_tmap_1(sK4,sK5),k7_tmap_1(sK4,sK5),sK7) != iProver_top
% 6.57/1.49      | v1_funct_2(k7_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5))) != iProver_top
% 6.57/1.49      | m1_subset_1(k7_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5))))) != iProver_top
% 6.57/1.49      | m1_subset_1(sK7,u1_struct_0(sK6)) != iProver_top
% 6.57/1.49      | v1_funct_1(k7_tmap_1(sK4,sK5)) != iProver_top
% 6.57/1.49      | v2_pre_topc(k6_tmap_1(sK4,sK5)) != iProver_top
% 6.57/1.49      | v2_struct_0(k6_tmap_1(sK4,sK5)) = iProver_top
% 6.57/1.49      | l1_pre_topc(k6_tmap_1(sK4,sK5)) != iProver_top ),
% 6.57/1.49      inference(superposition,[status(thm)],[c_2263,c_2274]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_41,plain,
% 6.57/1.49      ( v2_struct_0(sK4) != iProver_top ),
% 6.57/1.49      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_42,plain,
% 6.57/1.49      ( v2_pre_topc(sK4) = iProver_top ),
% 6.57/1.49      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_43,plain,
% 6.57/1.49      ( l1_pre_topc(sK4) = iProver_top ),
% 6.57/1.49      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_37,negated_conjecture,
% 6.57/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 6.57/1.49      inference(cnf_transformation,[],[f102]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_44,plain,
% 6.57/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 6.57/1.49      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_33,negated_conjecture,
% 6.57/1.49      ( m1_subset_1(sK7,u1_struct_0(sK6)) ),
% 6.57/1.49      inference(cnf_transformation,[],[f106]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_48,plain,
% 6.57/1.49      ( m1_subset_1(sK7,u1_struct_0(sK6)) = iProver_top ),
% 6.57/1.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_23,plain,
% 6.57/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 6.57/1.49      | ~ v2_pre_topc(X1)
% 6.57/1.49      | v2_struct_0(X1)
% 6.57/1.49      | ~ l1_pre_topc(X1)
% 6.57/1.49      | l1_pre_topc(k6_tmap_1(X1,X0)) ),
% 6.57/1.49      inference(cnf_transformation,[],[f91]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_2607,plain,
% 6.57/1.49      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 6.57/1.49      | ~ v2_pre_topc(sK4)
% 6.57/1.49      | v2_struct_0(sK4)
% 6.57/1.49      | l1_pre_topc(k6_tmap_1(sK4,sK5))
% 6.57/1.49      | ~ l1_pre_topc(sK4) ),
% 6.57/1.49      inference(instantiation,[status(thm)],[c_23]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_2608,plain,
% 6.57/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 6.57/1.49      | v2_pre_topc(sK4) != iProver_top
% 6.57/1.49      | v2_struct_0(sK4) = iProver_top
% 6.57/1.49      | l1_pre_topc(k6_tmap_1(sK4,sK5)) = iProver_top
% 6.57/1.49      | l1_pre_topc(sK4) != iProver_top ),
% 6.57/1.49      inference(predicate_to_equality,[status(thm)],[c_2607]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_27,plain,
% 6.57/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 6.57/1.49      | v1_funct_1(k7_tmap_1(X1,X0))
% 6.57/1.49      | ~ v2_pre_topc(X1)
% 6.57/1.49      | v2_struct_0(X1)
% 6.57/1.49      | ~ l1_pre_topc(X1) ),
% 6.57/1.49      inference(cnf_transformation,[],[f92]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_2616,plain,
% 6.57/1.49      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 6.57/1.49      | v1_funct_1(k7_tmap_1(sK4,sK5))
% 6.57/1.49      | ~ v2_pre_topc(sK4)
% 6.57/1.49      | v2_struct_0(sK4)
% 6.57/1.49      | ~ l1_pre_topc(sK4) ),
% 6.57/1.49      inference(instantiation,[status(thm)],[c_27]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_2617,plain,
% 6.57/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 6.57/1.49      | v1_funct_1(k7_tmap_1(sK4,sK5)) = iProver_top
% 6.57/1.49      | v2_pre_topc(sK4) != iProver_top
% 6.57/1.49      | v2_struct_0(sK4) = iProver_top
% 6.57/1.49      | l1_pre_topc(sK4) != iProver_top ),
% 6.57/1.49      inference(predicate_to_equality,[status(thm)],[c_2616]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_28,plain,
% 6.57/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 6.57/1.49      | ~ v2_pre_topc(X1)
% 6.57/1.49      | v2_pre_topc(k6_tmap_1(X1,X0))
% 6.57/1.49      | v2_struct_0(X1)
% 6.57/1.49      | ~ l1_pre_topc(X1) ),
% 6.57/1.49      inference(cnf_transformation,[],[f96]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_2625,plain,
% 6.57/1.49      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 6.57/1.49      | v2_pre_topc(k6_tmap_1(sK4,sK5))
% 6.57/1.49      | ~ v2_pre_topc(sK4)
% 6.57/1.49      | v2_struct_0(sK4)
% 6.57/1.49      | ~ l1_pre_topc(sK4) ),
% 6.57/1.49      inference(instantiation,[status(thm)],[c_28]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_2626,plain,
% 6.57/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 6.57/1.49      | v2_pre_topc(k6_tmap_1(sK4,sK5)) = iProver_top
% 6.57/1.49      | v2_pre_topc(sK4) != iProver_top
% 6.57/1.49      | v2_struct_0(sK4) = iProver_top
% 6.57/1.49      | l1_pre_topc(sK4) != iProver_top ),
% 6.57/1.49      inference(predicate_to_equality,[status(thm)],[c_2625]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_25,plain,
% 6.57/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 6.57/1.49      | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
% 6.57/1.49      | ~ v2_pre_topc(X1)
% 6.57/1.49      | v2_struct_0(X1)
% 6.57/1.49      | ~ l1_pre_topc(X1) ),
% 6.57/1.49      inference(cnf_transformation,[],[f94]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_2649,plain,
% 6.57/1.49      ( m1_subset_1(k7_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5)))))
% 6.57/1.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 6.57/1.49      | ~ v2_pre_topc(sK4)
% 6.57/1.49      | v2_struct_0(sK4)
% 6.57/1.49      | ~ l1_pre_topc(sK4) ),
% 6.57/1.49      inference(instantiation,[status(thm)],[c_25]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_2650,plain,
% 6.57/1.49      ( m1_subset_1(k7_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5))))) = iProver_top
% 6.57/1.49      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 6.57/1.49      | v2_pre_topc(sK4) != iProver_top
% 6.57/1.49      | v2_struct_0(sK4) = iProver_top
% 6.57/1.49      | l1_pre_topc(sK4) != iProver_top ),
% 6.57/1.49      inference(predicate_to_equality,[status(thm)],[c_2649]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_26,plain,
% 6.57/1.49      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
% 6.57/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 6.57/1.49      | ~ v2_pre_topc(X0)
% 6.57/1.49      | v2_struct_0(X0)
% 6.57/1.49      | ~ l1_pre_topc(X0) ),
% 6.57/1.49      inference(cnf_transformation,[],[f93]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_2658,plain,
% 6.57/1.49      ( v1_funct_2(k7_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5)))
% 6.57/1.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 6.57/1.49      | ~ v2_pre_topc(sK4)
% 6.57/1.49      | v2_struct_0(sK4)
% 6.57/1.49      | ~ l1_pre_topc(sK4) ),
% 6.57/1.49      inference(instantiation,[status(thm)],[c_26]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_2659,plain,
% 6.57/1.49      ( v1_funct_2(k7_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK5))) = iProver_top
% 6.57/1.49      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 6.57/1.49      | v2_pre_topc(sK4) != iProver_top
% 6.57/1.49      | v2_struct_0(sK4) = iProver_top
% 6.57/1.49      | l1_pre_topc(sK4) != iProver_top ),
% 6.57/1.49      inference(predicate_to_equality,[status(thm)],[c_2658]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_3136,plain,
% 6.57/1.49      ( v2_struct_0(k6_tmap_1(sK4,sK5)) = iProver_top
% 6.57/1.49      | r1_tmap_1(sK4,k6_tmap_1(sK4,sK5),k7_tmap_1(sK4,sK5),sK7) != iProver_top ),
% 6.57/1.49      inference(global_propositional_subsumption,
% 6.57/1.49                [status(thm)],
% 6.57/1.49                [c_2690,c_41,c_42,c_43,c_44,c_48,c_2608,c_2617,c_2626,
% 6.57/1.49                 c_2650,c_2659]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_3137,plain,
% 6.57/1.49      ( r1_tmap_1(sK4,k6_tmap_1(sK4,sK5),k7_tmap_1(sK4,sK5),sK7) != iProver_top
% 6.57/1.49      | v2_struct_0(k6_tmap_1(sK4,sK5)) = iProver_top ),
% 6.57/1.49      inference(renaming,[status(thm)],[c_3136]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_5342,plain,
% 6.57/1.49      ( m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
% 6.57/1.49      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 6.57/1.49      | r2_hidden(sK7,sK5) = iProver_top
% 6.57/1.49      | v2_pre_topc(sK4) != iProver_top
% 6.57/1.49      | v2_struct_0(k6_tmap_1(sK4,sK5)) = iProver_top
% 6.57/1.49      | v2_struct_0(sK4) = iProver_top
% 6.57/1.49      | l1_pre_topc(sK4) != iProver_top ),
% 6.57/1.49      inference(superposition,[status(thm)],[c_2275,c_3137]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_2581,plain,
% 6.57/1.49      ( m1_subset_1(sK7,u1_struct_0(sK4))
% 6.57/1.49      | ~ m1_subset_1(sK7,u1_struct_0(sK6)) ),
% 6.57/1.49      inference(instantiation,[status(thm)],[c_757]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_2582,plain,
% 6.57/1.49      ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top
% 6.57/1.49      | m1_subset_1(sK7,u1_struct_0(sK6)) != iProver_top ),
% 6.57/1.49      inference(predicate_to_equality,[status(thm)],[c_2581]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_5921,plain,
% 6.57/1.49      ( r2_hidden(sK7,sK5) = iProver_top
% 6.57/1.49      | v2_struct_0(k6_tmap_1(sK4,sK5)) = iProver_top ),
% 6.57/1.49      inference(global_propositional_subsumption,
% 6.57/1.49                [status(thm)],
% 6.57/1.49                [c_5342,c_41,c_42,c_43,c_44,c_48,c_2582]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_2271,plain,
% 6.57/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 6.57/1.49      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_29,plain,
% 6.57/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 6.57/1.49      | ~ v2_pre_topc(X1)
% 6.57/1.49      | v2_struct_0(X1)
% 6.57/1.49      | ~ v2_struct_0(k6_tmap_1(X1,X0))
% 6.57/1.49      | ~ l1_pre_topc(X1) ),
% 6.57/1.49      inference(cnf_transformation,[],[f95]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_2276,plain,
% 6.57/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 6.57/1.49      | v2_pre_topc(X1) != iProver_top
% 6.57/1.49      | v2_struct_0(X1) = iProver_top
% 6.57/1.49      | v2_struct_0(k6_tmap_1(X1,X0)) != iProver_top
% 6.57/1.49      | l1_pre_topc(X1) != iProver_top ),
% 6.57/1.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_6161,plain,
% 6.57/1.49      ( v2_pre_topc(sK4) != iProver_top
% 6.57/1.49      | v2_struct_0(k6_tmap_1(sK4,sK5)) != iProver_top
% 6.57/1.49      | v2_struct_0(sK4) = iProver_top
% 6.57/1.49      | l1_pre_topc(sK4) != iProver_top ),
% 6.57/1.49      inference(superposition,[status(thm)],[c_2271,c_2276]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_6427,plain,
% 6.57/1.49      ( v2_struct_0(k6_tmap_1(sK4,sK5)) != iProver_top ),
% 6.57/1.49      inference(global_propositional_subsumption,
% 6.57/1.49                [status(thm)],
% 6.57/1.49                [c_6161,c_41,c_42,c_43]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_6432,plain,
% 6.57/1.49      ( r2_hidden(sK7,sK5) = iProver_top ),
% 6.57/1.49      inference(superposition,[status(thm)],[c_5921,c_6427]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_2273,plain,
% 6.57/1.49      ( m1_subset_1(sK7,u1_struct_0(sK6)) = iProver_top ),
% 6.57/1.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_15,plain,
% 6.57/1.49      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 6.57/1.49      inference(cnf_transformation,[],[f82]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_2284,plain,
% 6.57/1.49      ( m1_subset_1(X0,X1) != iProver_top
% 6.57/1.49      | r2_hidden(X0,X1) = iProver_top
% 6.57/1.49      | v1_xboole_0(X1) = iProver_top ),
% 6.57/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_4140,plain,
% 6.57/1.49      ( r2_hidden(sK7,u1_struct_0(sK6)) = iProver_top
% 6.57/1.49      | v1_xboole_0(u1_struct_0(sK6)) = iProver_top ),
% 6.57/1.49      inference(superposition,[status(thm)],[c_2273,c_2284]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_14,plain,
% 6.57/1.49      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 6.57/1.49      inference(cnf_transformation,[],[f81]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_34,negated_conjecture,
% 6.57/1.49      ( r1_xboole_0(u1_struct_0(sK6),sK5) ),
% 6.57/1.49      inference(cnf_transformation,[],[f105]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_513,plain,
% 6.57/1.49      ( k4_xboole_0(X0,X1) = X0 | u1_struct_0(sK6) != X0 | sK5 != X1 ),
% 6.57/1.49      inference(resolution_lifted,[status(thm)],[c_14,c_34]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_514,plain,
% 6.57/1.49      ( k4_xboole_0(u1_struct_0(sK6),sK5) = u1_struct_0(sK6) ),
% 6.57/1.49      inference(unflattening,[status(thm)],[c_513]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_9,plain,
% 6.57/1.49      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 6.57/1.49      inference(cnf_transformation,[],[f109]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_2288,plain,
% 6.57/1.49      ( r2_hidden(X0,X1) != iProver_top
% 6.57/1.49      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 6.57/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_3408,plain,
% 6.57/1.49      ( r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
% 6.57/1.49      | r2_hidden(X0,sK5) != iProver_top ),
% 6.57/1.49      inference(superposition,[status(thm)],[c_514,c_2288]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_4522,plain,
% 6.57/1.49      ( r2_hidden(sK7,sK5) != iProver_top
% 6.57/1.49      | v1_xboole_0(u1_struct_0(sK6)) = iProver_top ),
% 6.57/1.49      inference(superposition,[status(thm)],[c_4140,c_3408]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_6490,plain,
% 6.57/1.49      ( v1_xboole_0(u1_struct_0(sK6)) = iProver_top ),
% 6.57/1.49      inference(superposition,[status(thm)],[c_6432,c_4522]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_7,plain,
% 6.57/1.49      ( r2_hidden(sK2(X0,X1,X2),X0)
% 6.57/1.49      | r2_hidden(sK2(X0,X1,X2),X2)
% 6.57/1.49      | k4_xboole_0(X0,X1) = X2 ),
% 6.57/1.49      inference(cnf_transformation,[],[f75]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_2290,plain,
% 6.57/1.49      ( k4_xboole_0(X0,X1) = X2
% 6.57/1.49      | r2_hidden(sK2(X0,X1,X2),X0) = iProver_top
% 6.57/1.49      | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top ),
% 6.57/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_6,plain,
% 6.57/1.49      ( ~ r2_hidden(sK2(X0,X1,X2),X1)
% 6.57/1.49      | r2_hidden(sK2(X0,X1,X2),X2)
% 6.57/1.49      | k4_xboole_0(X0,X1) = X2 ),
% 6.57/1.49      inference(cnf_transformation,[],[f76]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_2291,plain,
% 6.57/1.49      ( k4_xboole_0(X0,X1) = X2
% 6.57/1.49      | r2_hidden(sK2(X0,X1,X2),X1) != iProver_top
% 6.57/1.49      | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top ),
% 6.57/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_5348,plain,
% 6.57/1.49      ( k4_xboole_0(X0,X0) = X1
% 6.57/1.49      | r2_hidden(sK2(X0,X0,X1),X1) = iProver_top ),
% 6.57/1.49      inference(superposition,[status(thm)],[c_2290,c_2291]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_1,plain,
% 6.57/1.49      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 6.57/1.49      inference(cnf_transformation,[],[f67]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_2296,plain,
% 6.57/1.49      ( r2_hidden(X0,X1) != iProver_top
% 6.57/1.49      | v1_xboole_0(X1) != iProver_top ),
% 6.57/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_6844,plain,
% 6.57/1.49      ( k4_xboole_0(X0,X0) = X1 | v1_xboole_0(X1) != iProver_top ),
% 6.57/1.49      inference(superposition,[status(thm)],[c_5348,c_2296]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_6963,plain,
% 6.57/1.49      ( k4_xboole_0(X0,X0) = u1_struct_0(sK6) ),
% 6.57/1.49      inference(superposition,[status(thm)],[c_6490,c_6844]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_7587,plain,
% 6.57/1.49      ( u1_struct_0(sK6) = X0
% 6.57/1.49      | r2_hidden(sK2(X1,X1,X0),X0) = iProver_top ),
% 6.57/1.49      inference(demodulation,[status(thm)],[c_6963,c_5348]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_18,plain,
% 6.57/1.49      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 6.57/1.49      inference(cnf_transformation,[],[f85]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_21,plain,
% 6.57/1.49      ( m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 6.57/1.49      | v2_struct_0(X0)
% 6.57/1.49      | ~ l1_struct_0(X0) ),
% 6.57/1.49      inference(cnf_transformation,[],[f87]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_519,plain,
% 6.57/1.49      ( m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 6.57/1.49      | v2_struct_0(X0)
% 6.57/1.49      | ~ l1_pre_topc(X0) ),
% 6.57/1.49      inference(resolution,[status(thm)],[c_18,c_21]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_2267,plain,
% 6.57/1.49      ( m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 6.57/1.49      | v2_struct_0(X0) = iProver_top
% 6.57/1.49      | l1_pre_topc(X0) != iProver_top ),
% 6.57/1.49      inference(predicate_to_equality,[status(thm)],[c_519]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_17,plain,
% 6.57/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 6.57/1.49      inference(cnf_transformation,[],[f83]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_2282,plain,
% 6.57/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 6.57/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 6.57/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_4130,plain,
% 6.57/1.49      ( r1_tarski(sK3(X0),u1_struct_0(X0)) = iProver_top
% 6.57/1.49      | v2_struct_0(X0) = iProver_top
% 6.57/1.49      | l1_pre_topc(X0) != iProver_top ),
% 6.57/1.49      inference(superposition,[status(thm)],[c_2267,c_2282]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_4,plain,
% 6.57/1.49      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 6.57/1.49      inference(cnf_transformation,[],[f69]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_2293,plain,
% 6.57/1.49      ( r1_tarski(X0,X1) != iProver_top
% 6.57/1.49      | r2_hidden(X2,X0) != iProver_top
% 6.57/1.49      | r2_hidden(X2,X1) = iProver_top ),
% 6.57/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_6817,plain,
% 6.57/1.49      ( r2_hidden(X0,u1_struct_0(X1)) = iProver_top
% 6.57/1.49      | r2_hidden(X0,sK3(X1)) != iProver_top
% 6.57/1.49      | v2_struct_0(X1) = iProver_top
% 6.57/1.49      | l1_pre_topc(X1) != iProver_top ),
% 6.57/1.49      inference(superposition,[status(thm)],[c_4130,c_2293]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_22031,plain,
% 6.57/1.49      ( sK3(X0) = u1_struct_0(sK6)
% 6.57/1.49      | r2_hidden(sK2(X1,X1,sK3(X0)),u1_struct_0(X0)) = iProver_top
% 6.57/1.49      | v2_struct_0(X0) = iProver_top
% 6.57/1.49      | l1_pre_topc(X0) != iProver_top ),
% 6.57/1.49      inference(superposition,[status(thm)],[c_7587,c_6817]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_20,plain,
% 6.57/1.49      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(sK3(X0)) ),
% 6.57/1.49      inference(cnf_transformation,[],[f88]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_533,plain,
% 6.57/1.49      ( v2_struct_0(X0) | ~ l1_pre_topc(X0) | ~ v1_xboole_0(sK3(X0)) ),
% 6.57/1.49      inference(resolution,[status(thm)],[c_18,c_20]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_534,plain,
% 6.57/1.49      ( v2_struct_0(X0) = iProver_top
% 6.57/1.49      | l1_pre_topc(X0) != iProver_top
% 6.57/1.49      | v1_xboole_0(sK3(X0)) != iProver_top ),
% 6.57/1.49      inference(predicate_to_equality,[status(thm)],[c_533]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_1391,plain,
% 6.57/1.49      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 6.57/1.49      theory(equality) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_2671,plain,
% 6.57/1.49      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK3(X1)) | sK3(X1) != X0 ),
% 6.57/1.49      inference(instantiation,[status(thm)],[c_1391]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_10321,plain,
% 6.57/1.49      ( ~ v1_xboole_0(u1_struct_0(sK6))
% 6.57/1.49      | v1_xboole_0(sK3(X0))
% 6.57/1.49      | sK3(X0) != u1_struct_0(sK6) ),
% 6.57/1.49      inference(instantiation,[status(thm)],[c_2671]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_10326,plain,
% 6.57/1.49      ( sK3(X0) != u1_struct_0(sK6)
% 6.57/1.49      | v1_xboole_0(u1_struct_0(sK6)) != iProver_top
% 6.57/1.49      | v1_xboole_0(sK3(X0)) = iProver_top ),
% 6.57/1.49      inference(predicate_to_equality,[status(thm)],[c_10321]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_28600,plain,
% 6.57/1.49      ( r2_hidden(sK2(X1,X1,sK3(X0)),u1_struct_0(X0)) = iProver_top
% 6.57/1.49      | v2_struct_0(X0) = iProver_top
% 6.57/1.49      | l1_pre_topc(X0) != iProver_top ),
% 6.57/1.49      inference(global_propositional_subsumption,
% 6.57/1.49                [status(thm)],
% 6.57/1.49                [c_22031,c_41,c_42,c_43,c_44,c_48,c_534,c_2582,c_4522,
% 6.57/1.49                 c_5342,c_6161,c_10326]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_28601,plain,
% 6.57/1.49      ( r2_hidden(sK2(X0,X0,sK3(X1)),u1_struct_0(X1)) = iProver_top
% 6.57/1.49      | v2_struct_0(X1) = iProver_top
% 6.57/1.49      | l1_pre_topc(X1) != iProver_top ),
% 6.57/1.49      inference(renaming,[status(thm)],[c_28600]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_10,plain,
% 6.57/1.49      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 6.57/1.49      inference(cnf_transformation,[],[f110]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_2287,plain,
% 6.57/1.49      ( r2_hidden(X0,X1) = iProver_top
% 6.57/1.49      | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
% 6.57/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_7606,plain,
% 6.57/1.49      ( r2_hidden(X0,X1) = iProver_top
% 6.57/1.49      | r2_hidden(X0,u1_struct_0(sK6)) != iProver_top ),
% 6.57/1.49      inference(superposition,[status(thm)],[c_6963,c_2287]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_7607,plain,
% 6.57/1.49      ( r2_hidden(X0,X1) != iProver_top
% 6.57/1.49      | r2_hidden(X0,u1_struct_0(sK6)) != iProver_top ),
% 6.57/1.49      inference(superposition,[status(thm)],[c_6963,c_2288]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_7622,plain,
% 6.57/1.49      ( r2_hidden(X0,u1_struct_0(sK6)) != iProver_top ),
% 6.57/1.49      inference(forward_subsumption_resolution,
% 6.57/1.49                [status(thm)],
% 6.57/1.49                [c_7606,c_7607]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_28612,plain,
% 6.57/1.49      ( v2_struct_0(sK6) = iProver_top
% 6.57/1.49      | l1_pre_topc(sK6) != iProver_top ),
% 6.57/1.49      inference(superposition,[status(thm)],[c_28601,c_7622]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_19,plain,
% 6.57/1.49      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 6.57/1.49      inference(cnf_transformation,[],[f86]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_769,plain,
% 6.57/1.49      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK4 != X0 | sK6 != X1 ),
% 6.57/1.49      inference(resolution_lifted,[status(thm)],[c_19,c_35]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_770,plain,
% 6.57/1.49      ( ~ l1_pre_topc(sK4) | l1_pre_topc(sK6) ),
% 6.57/1.49      inference(unflattening,[status(thm)],[c_769]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_771,plain,
% 6.57/1.49      ( l1_pre_topc(sK4) != iProver_top
% 6.57/1.49      | l1_pre_topc(sK6) = iProver_top ),
% 6.57/1.49      inference(predicate_to_equality,[status(thm)],[c_770]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(c_45,plain,
% 6.57/1.49      ( v2_struct_0(sK6) != iProver_top ),
% 6.57/1.49      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 6.57/1.49  
% 6.57/1.49  cnf(contradiction,plain,
% 6.57/1.49      ( $false ),
% 6.57/1.49      inference(minisat,[status(thm)],[c_28612,c_771,c_45,c_43]) ).
% 6.57/1.49  
% 6.57/1.49  
% 6.57/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 6.57/1.49  
% 6.57/1.49  ------                               Statistics
% 6.57/1.49  
% 6.57/1.49  ------ General
% 6.57/1.49  
% 6.57/1.49  abstr_ref_over_cycles:                  0
% 6.57/1.49  abstr_ref_under_cycles:                 0
% 6.57/1.49  gc_basic_clause_elim:                   0
% 6.57/1.49  forced_gc_time:                         0
% 6.57/1.49  parsing_time:                           0.014
% 6.57/1.49  unif_index_cands_time:                  0.
% 6.57/1.49  unif_index_add_time:                    0.
% 6.57/1.49  orderings_time:                         0.
% 6.57/1.49  out_proof_time:                         0.011
% 6.57/1.49  total_time:                             0.718
% 6.57/1.49  num_of_symbols:                         59
% 6.57/1.49  num_of_terms:                           25209
% 6.57/1.49  
% 6.57/1.49  ------ Preprocessing
% 6.57/1.49  
% 6.57/1.49  num_of_splits:                          0
% 6.57/1.49  num_of_split_atoms:                     0
% 6.57/1.49  num_of_reused_defs:                     0
% 6.57/1.49  num_eq_ax_congr_red:                    30
% 6.57/1.49  num_of_sem_filtered_clauses:            1
% 6.57/1.49  num_of_subtypes:                        0
% 6.57/1.49  monotx_restored_types:                  0
% 6.57/1.49  sat_num_of_epr_types:                   0
% 6.57/1.49  sat_num_of_non_cyclic_types:            0
% 6.57/1.49  sat_guarded_non_collapsed_types:        0
% 6.57/1.49  num_pure_diseq_elim:                    0
% 6.57/1.49  simp_replaced_by:                       0
% 6.57/1.49  res_preprocessed:                       184
% 6.57/1.49  prep_upred:                             0
% 6.57/1.49  prep_unflattend:                        20
% 6.57/1.49  smt_new_axioms:                         0
% 6.57/1.49  pred_elim_cands:                        10
% 6.57/1.49  pred_elim:                              3
% 6.57/1.49  pred_elim_cl:                           3
% 6.57/1.49  pred_elim_cycles:                       11
% 6.57/1.49  merged_defs:                            8
% 6.57/1.49  merged_defs_ncl:                        0
% 6.57/1.49  bin_hyper_res:                          8
% 6.57/1.49  prep_cycles:                            4
% 6.57/1.49  pred_elim_time:                         0.01
% 6.57/1.49  splitting_time:                         0.
% 6.57/1.49  sem_filter_time:                        0.
% 6.57/1.49  monotx_time:                            0.
% 6.57/1.49  subtype_inf_time:                       0.
% 6.57/1.49  
% 6.57/1.49  ------ Problem properties
% 6.57/1.49  
% 6.57/1.49  clauses:                                36
% 6.57/1.49  conjectures:                            7
% 6.57/1.49  epr:                                    10
% 6.57/1.49  horn:                                   21
% 6.57/1.49  ground:                                 9
% 6.57/1.49  unary:                                  10
% 6.57/1.49  binary:                                 9
% 6.57/1.49  lits:                                   102
% 6.57/1.49  lits_eq:                                5
% 6.57/1.49  fd_pure:                                0
% 6.57/1.49  fd_pseudo:                              0
% 6.57/1.49  fd_cond:                                0
% 6.57/1.49  fd_pseudo_cond:                         4
% 6.57/1.49  ac_symbols:                             0
% 6.57/1.49  
% 6.57/1.49  ------ Propositional Solver
% 6.57/1.49  
% 6.57/1.49  prop_solver_calls:                      29
% 6.57/1.49  prop_fast_solver_calls:                 1981
% 6.57/1.49  smt_solver_calls:                       0
% 6.57/1.49  smt_fast_solver_calls:                  0
% 6.57/1.49  prop_num_of_clauses:                    8678
% 6.57/1.49  prop_preprocess_simplified:             19850
% 6.57/1.49  prop_fo_subsumed:                       61
% 6.57/1.49  prop_solver_time:                       0.
% 6.57/1.49  smt_solver_time:                        0.
% 6.57/1.49  smt_fast_solver_time:                   0.
% 6.57/1.49  prop_fast_solver_time:                  0.
% 6.57/1.49  prop_unsat_core_time:                   0.
% 6.57/1.49  
% 6.57/1.49  ------ QBF
% 6.57/1.49  
% 6.57/1.49  qbf_q_res:                              0
% 6.57/1.49  qbf_num_tautologies:                    0
% 6.57/1.49  qbf_prep_cycles:                        0
% 6.57/1.49  
% 6.57/1.49  ------ BMC1
% 6.57/1.49  
% 6.57/1.49  bmc1_current_bound:                     -1
% 6.57/1.49  bmc1_last_solved_bound:                 -1
% 6.57/1.49  bmc1_unsat_core_size:                   -1
% 6.57/1.49  bmc1_unsat_core_parents_size:           -1
% 6.57/1.49  bmc1_merge_next_fun:                    0
% 6.57/1.49  bmc1_unsat_core_clauses_time:           0.
% 6.57/1.49  
% 6.57/1.49  ------ Instantiation
% 6.57/1.49  
% 6.57/1.49  inst_num_of_clauses:                    2287
% 6.57/1.49  inst_num_in_passive:                    857
% 6.57/1.49  inst_num_in_active:                     944
% 6.57/1.49  inst_num_in_unprocessed:                486
% 6.57/1.49  inst_num_of_loops:                      1320
% 6.57/1.49  inst_num_of_learning_restarts:          0
% 6.57/1.49  inst_num_moves_active_passive:          372
% 6.57/1.49  inst_lit_activity:                      0
% 6.57/1.49  inst_lit_activity_moves:                0
% 6.57/1.49  inst_num_tautologies:                   0
% 6.57/1.49  inst_num_prop_implied:                  0
% 6.57/1.49  inst_num_existing_simplified:           0
% 6.57/1.49  inst_num_eq_res_simplified:             0
% 6.57/1.49  inst_num_child_elim:                    0
% 6.57/1.49  inst_num_of_dismatching_blockings:      1668
% 6.57/1.49  inst_num_of_non_proper_insts:           2887
% 6.57/1.49  inst_num_of_duplicates:                 0
% 6.57/1.49  inst_inst_num_from_inst_to_res:         0
% 6.57/1.49  inst_dismatching_checking_time:         0.
% 6.57/1.49  
% 6.57/1.49  ------ Resolution
% 6.57/1.49  
% 6.57/1.49  res_num_of_clauses:                     0
% 6.57/1.49  res_num_in_passive:                     0
% 6.57/1.49  res_num_in_active:                      0
% 6.57/1.49  res_num_of_loops:                       188
% 6.57/1.49  res_forward_subset_subsumed:            213
% 6.57/1.49  res_backward_subset_subsumed:           4
% 6.57/1.49  res_forward_subsumed:                   0
% 6.57/1.49  res_backward_subsumed:                  0
% 6.57/1.49  res_forward_subsumption_resolution:     5
% 6.57/1.49  res_backward_subsumption_resolution:    0
% 6.57/1.49  res_clause_to_clause_subsumption:       5684
% 6.57/1.49  res_orphan_elimination:                 0
% 6.57/1.49  res_tautology_del:                      247
% 6.57/1.49  res_num_eq_res_simplified:              0
% 6.57/1.49  res_num_sel_changes:                    0
% 6.57/1.49  res_moves_from_active_to_pass:          0
% 6.57/1.49  
% 6.57/1.49  ------ Superposition
% 6.57/1.49  
% 6.57/1.49  sup_time_total:                         0.
% 6.57/1.49  sup_time_generating:                    0.
% 6.57/1.49  sup_time_sim_full:                      0.
% 6.57/1.49  sup_time_sim_immed:                     0.
% 6.57/1.49  
% 6.57/1.49  sup_num_of_clauses:                     558
% 6.57/1.49  sup_num_in_active:                      250
% 6.57/1.49  sup_num_in_passive:                     308
% 6.57/1.49  sup_num_of_loops:                       262
% 6.57/1.49  sup_fw_superposition:                   1232
% 6.57/1.49  sup_bw_superposition:                   924
% 6.57/1.49  sup_immediate_simplified:               1137
% 6.57/1.49  sup_given_eliminated:                   1
% 6.57/1.49  comparisons_done:                       0
% 6.57/1.49  comparisons_avoided:                    0
% 6.57/1.49  
% 6.57/1.49  ------ Simplifications
% 6.57/1.49  
% 6.57/1.49  
% 6.57/1.49  sim_fw_subset_subsumed:                 370
% 6.57/1.49  sim_bw_subset_subsumed:                 20
% 6.57/1.49  sim_fw_subsumed:                        260
% 6.57/1.49  sim_bw_subsumed:                        8
% 6.57/1.49  sim_fw_subsumption_res:                 7
% 6.57/1.49  sim_bw_subsumption_res:                 0
% 6.57/1.49  sim_tautology_del:                      25
% 6.57/1.49  sim_eq_tautology_del:                   78
% 6.57/1.49  sim_eq_res_simp:                        1
% 6.57/1.49  sim_fw_demodulated:                     273
% 6.57/1.49  sim_bw_demodulated:                     7
% 6.57/1.49  sim_light_normalised:                   395
% 6.57/1.49  sim_joinable_taut:                      0
% 6.57/1.49  sim_joinable_simp:                      0
% 6.57/1.49  sim_ac_normalised:                      0
% 6.57/1.49  sim_smt_subsumption:                    0
% 6.57/1.49  
%------------------------------------------------------------------------------
