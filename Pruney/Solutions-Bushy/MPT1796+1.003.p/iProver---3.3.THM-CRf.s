%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1796+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:27 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 617 expanded)
%              Number of clauses        :   90 ( 151 expanded)
%              Number of leaves         :   16 ( 188 expanded)
%              Depth                    :   16
%              Number of atoms          :  888 (5674 expanded)
%              Number of equality atoms :  138 ( 578 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal clause size      :   22 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( l1_struct_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(X2)
        & l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f18,axiom,(
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
             => ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => r1_tmap_1(X1,X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X1,X0)
                  | ? [X3] :
                      ( ~ r1_tmap_1(X1,X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X1)) ) )
                & ( ! [X3] :
                      ( r1_tmap_1(X1,X0,X2,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                  | ~ v5_pre_topc(X2,X1,X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f50])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X1,X0)
                  | ? [X3] :
                      ( ~ r1_tmap_1(X1,X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X1)) ) )
                & ( ! [X4] :
                      ( r1_tmap_1(X1,X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ v5_pre_topc(X2,X1,X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f57])).

fof(f59,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tmap_1(X1,X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_tmap_1(X1,X0,X2,sK2(X0,X1,X2))
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X1,X0)
                  | ( ~ r1_tmap_1(X1,X0,X2,sK2(X0,X1,X2))
                    & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) )
                & ( ! [X4] :
                      ( r1_tmap_1(X1,X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ v5_pre_topc(X2,X1,X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f58,f59])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X1,X0)
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( u1_struct_0(X2) = X1
               => ( m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                  & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                  & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                  & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( u1_struct_0(X2) = X1
                 => ( m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                    & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                    & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                    & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                | ~ v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) )
              & u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                | ~ v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) )
              & u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
            | ~ v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
            | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
            | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) )
          & u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ( ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k6_tmap_1(X0,X1)))))
          | ~ v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),sK5),sK5,k6_tmap_1(X0,X1))
          | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),sK5),u1_struct_0(sK5),u1_struct_0(k6_tmap_1(X0,X1)))
          | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),sK5)) )
        & u1_struct_0(sK5) = X1
        & m1_pre_topc(sK5,X0)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                | ~ v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) )
              & u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ( ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,sK4),k7_tmap_1(X0,sK4),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,sK4)))))
              | ~ v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,sK4),k7_tmap_1(X0,sK4),X2),X2,k6_tmap_1(X0,sK4))
              | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,sK4),k7_tmap_1(X0,sK4),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,sK4)))
              | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,sK4),k7_tmap_1(X0,sK4),X2)) )
            & u1_struct_0(X2) = sK4
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                  | ~ v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                  | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                  | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) )
                & u1_struct_0(X2) = X1
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(k2_tmap_1(sK3,k6_tmap_1(sK3,X1),k7_tmap_1(sK3,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(sK3,X1)))))
                | ~ v5_pre_topc(k2_tmap_1(sK3,k6_tmap_1(sK3,X1),k7_tmap_1(sK3,X1),X2),X2,k6_tmap_1(sK3,X1))
                | ~ v1_funct_2(k2_tmap_1(sK3,k6_tmap_1(sK3,X1),k7_tmap_1(sK3,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(sK3,X1)))
                | ~ v1_funct_1(k2_tmap_1(sK3,k6_tmap_1(sK3,X1),k7_tmap_1(sK3,X1),X2)) )
              & u1_struct_0(X2) = X1
              & m1_pre_topc(X2,sK3)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,
    ( ( ~ m1_subset_1(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k6_tmap_1(sK3,sK4)))))
      | ~ v5_pre_topc(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5),sK5,k6_tmap_1(sK3,sK4))
      | ~ v1_funct_2(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k6_tmap_1(sK3,sK4)))
      | ~ v1_funct_1(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5)) )
    & u1_struct_0(sK5) = sK4
    & m1_pre_topc(sK5,sK3)
    & ~ v2_struct_0(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f52,f63,f62,f61])).

fof(f101,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k6_tmap_1(sK3,sK4)))))
    | ~ v5_pre_topc(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5),sK5,k6_tmap_1(sK3,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k6_tmap_1(sK3,sK4)))
    | ~ v1_funct_1(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5)) ),
    inference(cnf_transformation,[],[f64])).

fof(f95,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f64])).

fof(f96,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f64])).

fof(f98,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f64])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f82,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f99,plain,(
    m1_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f64])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f100,plain,(
    u1_struct_0(sK5) = sK4 ),
    inference(cnf_transformation,[],[f64])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( u1_struct_0(X2) = X1
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X2))
                   => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | u1_struct_0(X2) != X1
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | u1_struct_0(X2) != X1
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | u1_struct_0(X2) != X1
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f102,plain,(
    ! [X2,X0,X3] :
      ( r1_tmap_1(X2,k6_tmap_1(X0,u1_struct_0(X2)),k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f90])).

fof(f94,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f64])).

fof(f97,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f64])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X1,X0)
      | ~ r1_tmap_1(X1,X0,X2,sK2(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f77,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f87,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f81,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2053,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK3,sK4),u1_struct_0(X0),u1_struct_0(X1))
    | m1_subset_1(k2_tmap_1(X0,X1,k7_tmap_1(sK3,sK4),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(k7_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(k7_tmap_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2621,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK4)))
    | m1_subset_1(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(sK3,sK4)))))
    | ~ m1_subset_1(k7_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK4)))))
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(k6_tmap_1(sK3,sK4))
    | ~ l1_struct_0(sK3)
    | ~ v1_funct_1(k7_tmap_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_2053])).

cnf(c_9566,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK4)))
    | m1_subset_1(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k6_tmap_1(sK3,sK4)))))
    | ~ m1_subset_1(k7_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK4)))))
    | ~ l1_struct_0(k6_tmap_1(sK3,sK4))
    | ~ l1_struct_0(sK5)
    | ~ l1_struct_0(sK3)
    | ~ v1_funct_1(k7_tmap_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_2621])).

cnf(c_1684,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) = iProver_top
    | l1_struct_0(X3) != iProver_top
    | l1_struct_0(X2) != iProver_top
    | l1_struct_0(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_27,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1))
    | ~ v1_funct_1(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_29,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5),sK5,k6_tmap_1(sK3,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k6_tmap_1(sK3,sK4)))
    | ~ m1_subset_1(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k6_tmap_1(sK3,sK4)))))
    | ~ v1_funct_1(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_909,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k6_tmap_1(sK3,sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k6_tmap_1(sK3,sK4)))))
    | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5) != X0
    | k6_tmap_1(sK3,sK4) != X2
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_29])).

cnf(c_910,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k6_tmap_1(sK3,sK4)))
    | ~ m1_subset_1(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k6_tmap_1(sK3,sK4)))))
    | m1_subset_1(sK2(k6_tmap_1(sK3,sK4),sK5,k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5)),u1_struct_0(sK5))
    | ~ v1_funct_1(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5))
    | v2_struct_0(k6_tmap_1(sK3,sK4))
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(k6_tmap_1(sK3,sK4))
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(k6_tmap_1(sK3,sK4))
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_909])).

cnf(c_35,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_34,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_31,negated_conjecture,
    ( m1_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_559,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK5 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_31])).

cnf(c_560,plain,
    ( l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_559])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_570,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | sK5 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_31])).

cnf(c_571,plain,
    ( v2_pre_topc(sK5)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_570])).

cnf(c_912,plain,
    ( ~ l1_pre_topc(k6_tmap_1(sK3,sK4))
    | v2_struct_0(k6_tmap_1(sK3,sK4))
    | ~ v1_funct_1(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5))
    | m1_subset_1(sK2(k6_tmap_1(sK3,sK4),sK5,k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5)),u1_struct_0(sK5))
    | ~ m1_subset_1(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k6_tmap_1(sK3,sK4)))))
    | ~ v1_funct_2(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k6_tmap_1(sK3,sK4)))
    | ~ v2_pre_topc(k6_tmap_1(sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_910,c_35,c_34,c_32,c_560,c_571])).

cnf(c_913,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k6_tmap_1(sK3,sK4)))
    | ~ m1_subset_1(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k6_tmap_1(sK3,sK4)))))
    | m1_subset_1(sK2(k6_tmap_1(sK3,sK4),sK5,k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5)),u1_struct_0(sK5))
    | ~ v1_funct_1(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5))
    | v2_struct_0(k6_tmap_1(sK3,sK4))
    | ~ v2_pre_topc(k6_tmap_1(sK3,sK4))
    | ~ l1_pre_topc(k6_tmap_1(sK3,sK4)) ),
    inference(renaming,[status(thm)],[c_912])).

cnf(c_1653,plain,
    ( v1_funct_2(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k6_tmap_1(sK3,sK4))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k6_tmap_1(sK3,sK4))))) != iProver_top
    | m1_subset_1(sK2(k6_tmap_1(sK3,sK4),sK5,k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5)),u1_struct_0(sK5)) = iProver_top
    | v1_funct_1(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5)) != iProver_top
    | v2_struct_0(k6_tmap_1(sK3,sK4)) = iProver_top
    | v2_pre_topc(k6_tmap_1(sK3,sK4)) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK3,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_913])).

cnf(c_5367,plain,
    ( v1_funct_2(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k6_tmap_1(sK3,sK4))) != iProver_top
    | v1_funct_2(k7_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK4))) != iProver_top
    | m1_subset_1(sK2(k6_tmap_1(sK3,sK4),sK5,k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5)),u1_struct_0(sK5)) = iProver_top
    | m1_subset_1(k7_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK4))))) != iProver_top
    | l1_struct_0(k6_tmap_1(sK3,sK4)) != iProver_top
    | l1_struct_0(sK5) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | v1_funct_1(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5)) != iProver_top
    | v1_funct_1(k7_tmap_1(sK3,sK4)) != iProver_top
    | v2_struct_0(k6_tmap_1(sK3,sK4)) = iProver_top
    | v2_pre_topc(k6_tmap_1(sK3,sK4)) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1684,c_1653])).

cnf(c_5388,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k6_tmap_1(sK3,sK4)))
    | ~ v1_funct_2(k7_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK4)))
    | m1_subset_1(sK2(k6_tmap_1(sK3,sK4),sK5,k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5)),u1_struct_0(sK5))
    | ~ m1_subset_1(k7_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK4)))))
    | ~ l1_struct_0(k6_tmap_1(sK3,sK4))
    | ~ l1_struct_0(sK5)
    | ~ l1_struct_0(sK3)
    | ~ v1_funct_1(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5))
    | ~ v1_funct_1(k7_tmap_1(sK3,sK4))
    | v2_struct_0(k6_tmap_1(sK3,sK4))
    | ~ v2_pre_topc(k6_tmap_1(sK3,sK4))
    | ~ l1_pre_topc(k6_tmap_1(sK3,sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5367])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2052,plain,
    ( v1_funct_2(k2_tmap_1(X0,X1,k7_tmap_1(sK3,sK4),X2),u1_struct_0(X2),u1_struct_0(X1))
    | ~ v1_funct_2(k7_tmap_1(sK3,sK4),u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(k7_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(k7_tmap_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2616,plain,
    ( v1_funct_2(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),X0),u1_struct_0(X0),u1_struct_0(k6_tmap_1(sK3,sK4)))
    | ~ v1_funct_2(k7_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK4)))
    | ~ m1_subset_1(k7_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK4)))))
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(k6_tmap_1(sK3,sK4))
    | ~ l1_struct_0(sK3)
    | ~ v1_funct_1(k7_tmap_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_2052])).

cnf(c_4976,plain,
    ( v1_funct_2(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k6_tmap_1(sK3,sK4)))
    | ~ v1_funct_2(k7_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK4)))
    | ~ m1_subset_1(k7_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK4)))))
    | ~ l1_struct_0(k6_tmap_1(sK3,sK4))
    | ~ l1_struct_0(sK5)
    | ~ l1_struct_0(sK3)
    | ~ v1_funct_1(k7_tmap_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_2616])).

cnf(c_30,negated_conjecture,
    ( u1_struct_0(sK5) = sK4 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_25,plain,
    ( r1_tmap_1(X0,k6_tmap_1(X1,u1_struct_0(X0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_538,plain,
    ( r1_tmap_1(X0,k6_tmap_1(X1,u1_struct_0(X0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK5 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_31])).

cnf(c_539,plain,
    ( r1_tmap_1(sK5,k6_tmap_1(sK3,u1_struct_0(sK5)),k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK5)),k7_tmap_1(sK3,u1_struct_0(sK5)),sK5),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK5)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_538])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_543,plain,
    ( r1_tmap_1(sK5,k6_tmap_1(sK3,u1_struct_0(sK5)),k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK5)),k7_tmap_1(sK3,u1_struct_0(sK5)),sK5),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_539,c_36,c_35,c_34,c_32])).

cnf(c_1661,plain,
    ( r1_tmap_1(sK5,k6_tmap_1(sK3,u1_struct_0(sK5)),k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK5)),k7_tmap_1(sK3,u1_struct_0(sK5)),sK5),X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_543])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_40,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_545,plain,
    ( r1_tmap_1(sK5,k6_tmap_1(sK3,u1_struct_0(sK5)),k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK5)),k7_tmap_1(sK3,u1_struct_0(sK5)),sK5),X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_543])).

cnf(c_967,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1917,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | X1 != k1_zfmisc_1(u1_struct_0(sK3))
    | X0 != sK4 ),
    inference(instantiation,[status(thm)],[c_967])).

cnf(c_2141,plain,
    ( m1_subset_1(u1_struct_0(sK5),X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | X0 != k1_zfmisc_1(u1_struct_0(sK3))
    | u1_struct_0(sK5) != sK4 ),
    inference(instantiation,[status(thm)],[c_1917])).

cnf(c_2230,plain,
    ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3))
    | u1_struct_0(sK5) != sK4 ),
    inference(instantiation,[status(thm)],[c_2141])).

cnf(c_2232,plain,
    ( k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3))
    | u1_struct_0(sK5) != sK4
    | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2230])).

cnf(c_957,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2231,plain,
    ( k1_zfmisc_1(u1_struct_0(sK3)) = k1_zfmisc_1(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_957])).

cnf(c_4108,plain,
    ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | r1_tmap_1(sK5,k6_tmap_1(sK3,u1_struct_0(sK5)),k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK5)),k7_tmap_1(sK3,u1_struct_0(sK5)),sK5),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1661,c_40,c_30,c_545,c_2232,c_2231])).

cnf(c_4109,plain,
    ( r1_tmap_1(sK5,k6_tmap_1(sK3,u1_struct_0(sK5)),k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK5)),k7_tmap_1(sK3,u1_struct_0(sK5)),sK5),X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4108])).

cnf(c_4114,plain,
    ( r1_tmap_1(sK5,k6_tmap_1(sK3,sK4),k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5),X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_30,c_4109])).

cnf(c_26,plain,
    ( ~ r1_tmap_1(X0,X1,X2,sK2(X1,X0,X2))
    | v5_pre_topc(X2,X0,X1)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_880,plain,
    ( ~ r1_tmap_1(X0,X1,X2,sK2(X1,X0,X2))
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_2(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k6_tmap_1(sK3,sK4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k6_tmap_1(sK3,sK4)))))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5) != X2
    | k6_tmap_1(sK3,sK4) != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_29])).

cnf(c_881,plain,
    ( ~ r1_tmap_1(sK5,k6_tmap_1(sK3,sK4),k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5),sK2(k6_tmap_1(sK3,sK4),sK5,k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5)))
    | ~ v1_funct_2(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k6_tmap_1(sK3,sK4)))
    | ~ m1_subset_1(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k6_tmap_1(sK3,sK4)))))
    | ~ v1_funct_1(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5))
    | v2_struct_0(k6_tmap_1(sK3,sK4))
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(k6_tmap_1(sK3,sK4))
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(k6_tmap_1(sK3,sK4))
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_880])).

cnf(c_883,plain,
    ( ~ l1_pre_topc(k6_tmap_1(sK3,sK4))
    | v2_struct_0(k6_tmap_1(sK3,sK4))
    | ~ v1_funct_1(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5))
    | ~ m1_subset_1(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k6_tmap_1(sK3,sK4)))))
    | ~ v1_funct_2(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k6_tmap_1(sK3,sK4)))
    | ~ r1_tmap_1(sK5,k6_tmap_1(sK3,sK4),k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5),sK2(k6_tmap_1(sK3,sK4),sK5,k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5)))
    | ~ v2_pre_topc(k6_tmap_1(sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_881,c_35,c_34,c_32,c_560,c_571])).

cnf(c_884,plain,
    ( ~ r1_tmap_1(sK5,k6_tmap_1(sK3,sK4),k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5),sK2(k6_tmap_1(sK3,sK4),sK5,k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5)))
    | ~ v1_funct_2(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k6_tmap_1(sK3,sK4)))
    | ~ m1_subset_1(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k6_tmap_1(sK3,sK4)))))
    | ~ v1_funct_1(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5))
    | v2_struct_0(k6_tmap_1(sK3,sK4))
    | ~ v2_pre_topc(k6_tmap_1(sK3,sK4))
    | ~ l1_pre_topc(k6_tmap_1(sK3,sK4)) ),
    inference(renaming,[status(thm)],[c_883])).

cnf(c_1654,plain,
    ( r1_tmap_1(sK5,k6_tmap_1(sK3,sK4),k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5),sK2(k6_tmap_1(sK3,sK4),sK5,k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5))) != iProver_top
    | v1_funct_2(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k6_tmap_1(sK3,sK4))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k6_tmap_1(sK3,sK4))))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5)) != iProver_top
    | v2_struct_0(k6_tmap_1(sK3,sK4)) = iProver_top
    | v2_pre_topc(k6_tmap_1(sK3,sK4)) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK3,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_884])).

cnf(c_37,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_38,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_39,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_41,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_561,plain,
    ( l1_pre_topc(sK5) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_560])).

cnf(c_572,plain,
    ( v2_pre_topc(sK5) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_571])).

cnf(c_882,plain,
    ( r1_tmap_1(sK5,k6_tmap_1(sK3,sK4),k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5),sK2(k6_tmap_1(sK3,sK4),sK5,k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5))) != iProver_top
    | v1_funct_2(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k6_tmap_1(sK3,sK4))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k6_tmap_1(sK3,sK4))))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5)) != iProver_top
    | v2_struct_0(k6_tmap_1(sK3,sK4)) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(k6_tmap_1(sK3,sK4)) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK3,sK4)) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_881])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k6_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1833,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | l1_pre_topc(k6_tmap_1(sK3,sK4))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1834,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK3,sK4)) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1833])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k6_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1843,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | v2_pre_topc(k6_tmap_1(sK3,sK4))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1844,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(k6_tmap_1(sK3,sK4)) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1843])).

cnf(c_1848,plain,
    ( r1_tmap_1(sK5,k6_tmap_1(sK3,sK4),k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5),sK2(k6_tmap_1(sK3,sK4),sK5,k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5))) != iProver_top
    | v1_funct_2(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k6_tmap_1(sK3,sK4))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k6_tmap_1(sK3,sK4))))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5)) != iProver_top
    | v2_struct_0(k6_tmap_1(sK3,sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1654,c_37,c_38,c_39,c_40,c_41,c_561,c_572,c_882,c_1834,c_1844])).

cnf(c_4121,plain,
    ( v1_funct_2(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k6_tmap_1(sK3,sK4))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k6_tmap_1(sK3,sK4))))) != iProver_top
    | m1_subset_1(sK2(k6_tmap_1(sK3,sK4),sK5,k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5)),u1_struct_0(sK5)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5)) != iProver_top
    | v2_struct_0(k6_tmap_1(sK3,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4114,c_1848])).

cnf(c_4122,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k6_tmap_1(sK3,sK4)))
    | ~ m1_subset_1(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k6_tmap_1(sK3,sK4)))))
    | ~ m1_subset_1(sK2(k6_tmap_1(sK3,sK4),sK5,k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5)),u1_struct_0(sK5))
    | ~ v1_funct_1(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5))
    | v2_struct_0(k6_tmap_1(sK3,sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4121])).

cnf(c_16,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_3147,plain,
    ( l1_struct_0(k6_tmap_1(sK3,sK4))
    | ~ l1_pre_topc(k6_tmap_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_3101,plain,
    ( l1_struct_0(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1668,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k6_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1672,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(k6_tmap_1(X1,X0)) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3003,plain,
    ( v2_struct_0(k6_tmap_1(sK3,sK4)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1668,c_1672])).

cnf(c_3008,plain,
    ( ~ v2_struct_0(k6_tmap_1(sK3,sK4))
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3003])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tmap_1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2054,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK3,sK4),u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(k7_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X2)
    | v1_funct_1(k2_tmap_1(X0,X1,k7_tmap_1(sK3,sK4),X2))
    | ~ v1_funct_1(k7_tmap_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2611,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK4)))
    | ~ m1_subset_1(k7_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK4)))))
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(k6_tmap_1(sK3,sK4))
    | ~ l1_struct_0(sK3)
    | v1_funct_1(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),X0))
    | ~ v1_funct_1(k7_tmap_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_2054])).

cnf(c_2998,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK4)))
    | ~ m1_subset_1(k7_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK4)))))
    | ~ l1_struct_0(k6_tmap_1(sK3,sK4))
    | ~ l1_struct_0(sK5)
    | ~ l1_struct_0(sK3)
    | v1_funct_1(k2_tmap_1(sK3,k6_tmap_1(sK3,sK4),k7_tmap_1(sK3,sK4),sK5))
    | ~ v1_funct_1(k7_tmap_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_2611])).

cnf(c_14,plain,
    ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1974,plain,
    ( v1_funct_2(k7_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK4)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1969,plain,
    ( m1_subset_1(k7_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK4)))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_funct_1(k7_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1838,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_funct_1(k7_tmap_1(sK3,sK4))
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_77,plain,
    ( l1_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9566,c_5388,c_4976,c_4122,c_3147,c_3101,c_3008,c_2998,c_1974,c_1969,c_1843,c_1838,c_1833,c_560,c_77,c_33,c_34,c_35,c_36])).


%------------------------------------------------------------------------------
