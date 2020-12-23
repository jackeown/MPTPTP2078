%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1804+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:30 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 641 expanded)
%              Number of clauses        :  102 ( 216 expanded)
%              Number of leaves         :   14 ( 163 expanded)
%              Depth                    :   19
%              Number of atoms          :  984 (5600 expanded)
%              Number of equality atoms :  179 ( 283 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal clause size      :   24 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( r1_tsep_1(X1,X2)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X2))
                   => r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | ~ r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | ~ r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

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
             => ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => r1_tmap_1(X1,X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f46])).

fof(f52,plain,(
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
    inference(rectify,[],[f51])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tmap_1(X1,X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_tmap_1(X1,X0,X2,sK1(X0,X1,X2))
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X1,X0)
                  | ( ~ r1_tmap_1(X1,X0,X2,sK1(X0,X1,X2))
                    & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f52,f53])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X1,X0)
      | ~ r1_tmap_1(X1,X0,X2,sK1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( r1_tsep_1(X1,X2)
               => ( m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))))
                  & v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1))
                  & v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))
                  & v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( r1_tsep_1(X1,X2)
                 => ( m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))))
                    & v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1))
                    & v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))
                    & v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))))
                | ~ v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1))
                | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))
                | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)) )
              & r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))))
                | ~ v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1))
                | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))
                | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)) )
              & r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))))
            | ~ v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1))
            | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))
            | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)) )
          & r1_tsep_1(X1,X2)
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ( ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(X0,X1)))))
          | ~ v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),sK4),sK4,k8_tmap_1(X0,X1))
          | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(X0,X1)))
          | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),sK4)) )
        & r1_tsep_1(X1,sK4)
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))))
                | ~ v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1))
                | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))
                | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)) )
              & r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ( ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,sK3),k9_tmap_1(X0,sK3),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,sK3)))))
              | ~ v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,sK3),k9_tmap_1(X0,sK3),X2),X2,k8_tmap_1(X0,sK3))
              | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,sK3),k9_tmap_1(X0,sK3),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,sK3)))
              | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,sK3),k9_tmap_1(X0,sK3),X2)) )
            & r1_tsep_1(sK3,X2)
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))))
                  | ~ v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1))
                  | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))
                  | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)) )
                & r1_tsep_1(X1,X2)
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(k2_tmap_1(sK2,k8_tmap_1(sK2,X1),k9_tmap_1(sK2,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK2,X1)))))
                | ~ v5_pre_topc(k2_tmap_1(sK2,k8_tmap_1(sK2,X1),k9_tmap_1(sK2,X1),X2),X2,k8_tmap_1(sK2,X1))
                | ~ v1_funct_2(k2_tmap_1(sK2,k8_tmap_1(sK2,X1),k9_tmap_1(sK2,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK2,X1)))
                | ~ v1_funct_1(k2_tmap_1(sK2,k8_tmap_1(sK2,X1),k9_tmap_1(sK2,X1),X2)) )
              & r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,sK2)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK2)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( ( ~ m1_subset_1(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK2,sK3)))))
      | ~ v5_pre_topc(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),sK4,k8_tmap_1(sK2,sK3))
      | ~ v1_funct_2(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK2,sK3)))
      | ~ v1_funct_1(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)) )
    & r1_tsep_1(sK3,sK4)
    & m1_pre_topc(sK4,sK2)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f48,f57,f56,f55])).

fof(f95,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v5_pre_topc(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),sK4,k8_tmap_1(sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ v1_funct_1(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)) ),
    inference(cnf_transformation,[],[f58])).

fof(f92,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f58])).

fof(f87,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f58])).

fof(f88,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f58])).

fof(f89,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f58])).

fof(f91,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f58])).

fof(f93,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f58])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f60,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1))
        & ~ v2_struct_0(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1))
        & ~ v2_struct_0(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1))
        & ~ v2_struct_0(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f70,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f75,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f90,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f94,plain,(
    r1_tsep_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f58])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f74,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k9_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X1,X0)
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_987,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(X1_57))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
    | m1_subset_1(k2_tmap_1(X0_57,X1_57,X0_55,X2_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X1_57))))
    | ~ l1_struct_0(X1_57)
    | ~ l1_struct_0(X0_57)
    | ~ l1_struct_0(X2_57)
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1698,plain,
    ( v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(X1_57)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57)))) != iProver_top
    | m1_subset_1(k2_tmap_1(X0_57,X1_57,X0_55,X2_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X1_57)))) = iProver_top
    | l1_struct_0(X1_57) != iProver_top
    | l1_struct_0(X0_57) != iProver_top
    | l1_struct_0(X2_57) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_987])).

cnf(c_24,plain,
    ( r1_tmap_1(X0,k8_tmap_1(X1,X2),k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X0),X3)
    | ~ r1_tsep_1(X2,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_971,plain,
    ( r1_tmap_1(X0_57,k8_tmap_1(X1_57,X2_57),k2_tmap_1(X1_57,k8_tmap_1(X1_57,X2_57),k9_tmap_1(X1_57,X2_57),X0_57),X0_55)
    | ~ r1_tsep_1(X2_57,X0_57)
    | ~ m1_subset_1(X0_55,u1_struct_0(X0_57))
    | ~ m1_pre_topc(X2_57,X1_57)
    | ~ m1_pre_topc(X0_57,X1_57)
    | v2_struct_0(X0_57)
    | v2_struct_0(X1_57)
    | v2_struct_0(X2_57)
    | ~ v2_pre_topc(X1_57)
    | ~ l1_pre_topc(X1_57) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1714,plain,
    ( r1_tmap_1(X0_57,k8_tmap_1(X1_57,X2_57),k2_tmap_1(X1_57,k8_tmap_1(X1_57,X2_57),k9_tmap_1(X1_57,X2_57),X0_57),X0_55) = iProver_top
    | r1_tsep_1(X2_57,X0_57) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X0_57)) != iProver_top
    | m1_pre_topc(X2_57,X1_57) != iProver_top
    | m1_pre_topc(X0_57,X1_57) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(X2_57) = iProver_top
    | v2_pre_topc(X1_57) != iProver_top
    | l1_pre_topc(X1_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_971])).

cnf(c_25,plain,
    ( ~ r1_tmap_1(X0,X1,X2,sK1(X1,X0,X2))
    | v5_pre_topc(X2,X0,X1)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_28,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),sK4,k8_tmap_1(sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v1_funct_1(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_588,plain,
    ( ~ r1_tmap_1(X0,X1,X2,sK1(X1,X0,X2))
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_2(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4) != X2
    | k8_tmap_1(sK2,sK3) != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_28])).

cnf(c_589,plain,
    ( ~ r1_tmap_1(sK4,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),sK1(k8_tmap_1(sK2,sK3),sK4,k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | v2_struct_0(k8_tmap_1(sK2,sK3))
    | v2_struct_0(sK4)
    | ~ v1_funct_1(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4))
    | ~ v2_pre_topc(k8_tmap_1(sK2,sK3))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(k8_tmap_1(sK2,sK3))
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_588])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_591,plain,
    ( v2_struct_0(k8_tmap_1(sK2,sK3))
    | ~ m1_subset_1(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v1_funct_2(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ r1_tmap_1(sK4,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),sK1(k8_tmap_1(sK2,sK3),sK4,k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)))
    | ~ v1_funct_1(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4))
    | ~ v2_pre_topc(k8_tmap_1(sK2,sK3))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(k8_tmap_1(sK2,sK3))
    | ~ l1_pre_topc(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_589,c_31])).

cnf(c_592,plain,
    ( ~ r1_tmap_1(sK4,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),sK1(k8_tmap_1(sK2,sK3),sK4,k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | v2_struct_0(k8_tmap_1(sK2,sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4))
    | ~ v2_pre_topc(k8_tmap_1(sK2,sK3))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(k8_tmap_1(sK2,sK3))
    | ~ l1_pre_topc(sK4) ),
    inference(renaming,[status(thm)],[c_591])).

cnf(c_960,plain,
    ( ~ r1_tmap_1(sK4,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),sK1(k8_tmap_1(sK2,sK3),sK4,k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | v2_struct_0(k8_tmap_1(sK2,sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4))
    | ~ v2_pre_topc(k8_tmap_1(sK2,sK3))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(k8_tmap_1(sK2,sK3))
    | ~ l1_pre_topc(sK4) ),
    inference(subtyping,[status(esa)],[c_592])).

cnf(c_1725,plain,
    ( r1_tmap_1(sK4,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),sK1(k8_tmap_1(sK2,sK3),sK4,k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4))) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | v1_funct_1(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)) != iProver_top
    | v2_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_960])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_37,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_38,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_39,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_32,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_41,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_42,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_43,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_590,plain,
    ( r1_tmap_1(sK4,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),sK1(k8_tmap_1(sK2,sK3),sK4,k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4))) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v1_funct_1(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)) != iProver_top
    | v2_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_589])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_992,plain,
    ( ~ m1_pre_topc(X0_57,X1_57)
    | ~ v2_pre_topc(X1_57)
    | v2_pre_topc(X0_57)
    | ~ l1_pre_topc(X1_57) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2126,plain,
    ( ~ m1_pre_topc(sK4,X0_57)
    | ~ v2_pre_topc(X0_57)
    | v2_pre_topc(sK4)
    | ~ l1_pre_topc(X0_57) ),
    inference(instantiation,[status(thm)],[c_992])).

cnf(c_2127,plain,
    ( m1_pre_topc(sK4,X0_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(sK4) = iProver_top
    | l1_pre_topc(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2126])).

cnf(c_2129,plain,
    ( m1_pre_topc(sK4,sK2) != iProver_top
    | v2_pre_topc(sK4) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2127])).

cnf(c_21,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_974,plain,
    ( ~ m1_pre_topc(X0_57,X1_57)
    | v2_struct_0(X1_57)
    | ~ v2_struct_0(k8_tmap_1(X1_57,X0_57))
    | ~ v2_pre_topc(X1_57)
    | ~ l1_pre_topc(X1_57) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_2137,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ v2_struct_0(k8_tmap_1(sK2,sK3))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_974])).

cnf(c_2138,plain,
    ( m1_pre_topc(sK3,sK2) != iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2137])).

cnf(c_19,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k8_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_983,plain,
    ( ~ m1_pre_topc(X0_57,X1_57)
    | v2_struct_0(X1_57)
    | ~ v2_pre_topc(X1_57)
    | v2_pre_topc(k8_tmap_1(X1_57,X0_57))
    | ~ l1_pre_topc(X1_57) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_2159,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK2)
    | v2_pre_topc(k8_tmap_1(sK2,sK3))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_983])).

cnf(c_2160,plain,
    ( m1_pre_topc(sK3,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(k8_tmap_1(sK2,sK3)) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2159])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_984,plain,
    ( ~ m1_pre_topc(X0_57,X1_57)
    | v2_struct_0(X1_57)
    | ~ v2_pre_topc(X1_57)
    | ~ l1_pre_topc(X1_57)
    | l1_pre_topc(k8_tmap_1(X1_57,X0_57)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_2165,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | l1_pre_topc(k8_tmap_1(sK2,sK3))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_984])).

cnf(c_2166,plain,
    ( m1_pre_topc(sK3,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2165])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_977,plain,
    ( ~ m1_pre_topc(X0_57,X1_57)
    | ~ l1_pre_topc(X1_57)
    | l1_pre_topc(X0_57) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_2390,plain,
    ( ~ m1_pre_topc(sK4,X0_57)
    | ~ l1_pre_topc(X0_57)
    | l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_977])).

cnf(c_2391,plain,
    ( m1_pre_topc(sK4,X0_57) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2390])).

cnf(c_2393,plain,
    ( m1_pre_topc(sK4,sK2) != iProver_top
    | l1_pre_topc(sK4) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2391])).

cnf(c_2404,plain,
    ( m1_subset_1(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
    | r1_tmap_1(sK4,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),sK1(k8_tmap_1(sK2,sK3),sK4,k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1725,c_37,c_38,c_39,c_41,c_42,c_43,c_590,c_2129,c_2138,c_2160,c_2166,c_2393])).

cnf(c_2405,plain,
    ( r1_tmap_1(sK4,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),sK1(k8_tmap_1(sK2,sK3),sK4,k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4))) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2404])).

cnf(c_4473,plain,
    ( v1_funct_2(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
    | r1_tsep_1(sK3,sK4) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top
    | m1_subset_1(sK1(k8_tmap_1(sK2,sK3),sK4,k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)),u1_struct_0(sK4)) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1714,c_2405])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_40,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_29,negated_conjecture,
    ( r1_tsep_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_44,plain,
    ( r1_tsep_1(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_15,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_76,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_78,plain,
    ( l1_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_76])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v1_funct_1(k9_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_979,plain,
    ( ~ m1_pre_topc(X0_57,X1_57)
    | v2_struct_0(X1_57)
    | v1_funct_1(k9_tmap_1(X1_57,X0_57))
    | ~ v2_pre_topc(X1_57)
    | ~ l1_pre_topc(X1_57) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_2143,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK2)
    | v1_funct_1(k9_tmap_1(sK2,sK3))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_979])).

cnf(c_2144,plain,
    ( m1_pre_topc(sK3,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k9_tmap_1(sK2,sK3)) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2143])).

cnf(c_13,plain,
    ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_980,plain,
    ( v1_funct_2(k9_tmap_1(X0_57,X1_57),u1_struct_0(X0_57),u1_struct_0(k8_tmap_1(X0_57,X1_57)))
    | ~ m1_pre_topc(X1_57,X0_57)
    | v2_struct_0(X0_57)
    | ~ v2_pre_topc(X0_57)
    | ~ l1_pre_topc(X0_57) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_2195,plain,
    ( v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_980])).

cnf(c_2196,plain,
    ( v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) = iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2195])).

cnf(c_12,plain,
    ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_981,plain,
    ( m1_subset_1(k9_tmap_1(X0_57,X1_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(k8_tmap_1(X0_57,X1_57)))))
    | ~ m1_pre_topc(X1_57,X0_57)
    | v2_struct_0(X0_57)
    | ~ v2_pre_topc(X0_57)
    | ~ l1_pre_topc(X0_57) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_2201,plain,
    ( m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_981])).

cnf(c_2202,plain,
    ( m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) = iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2201])).

cnf(c_978,plain,
    ( l1_struct_0(X0_57)
    | ~ l1_pre_topc(X0_57) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_2566,plain,
    ( l1_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_978])).

cnf(c_2567,plain,
    ( l1_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2566])).

cnf(c_2862,plain,
    ( l1_struct_0(k8_tmap_1(sK2,sK3))
    | ~ l1_pre_topc(k8_tmap_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_978])).

cnf(c_2863,plain,
    ( l1_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2862])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tmap_1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_985,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(X1_57))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
    | ~ l1_struct_0(X1_57)
    | ~ l1_struct_0(X0_57)
    | ~ l1_struct_0(X2_57)
    | ~ v1_funct_1(X0_55)
    | v1_funct_1(k2_tmap_1(X0_57,X1_57,X0_55,X2_57)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_2293,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(X0_57),u1_struct_0(X1_57))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
    | ~ l1_struct_0(X1_57)
    | ~ l1_struct_0(X0_57)
    | ~ l1_struct_0(X2_57)
    | v1_funct_1(k2_tmap_1(X0_57,X1_57,k9_tmap_1(sK2,sK3),X2_57))
    | ~ v1_funct_1(k9_tmap_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_985])).

cnf(c_2697,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ l1_struct_0(X0_57)
    | ~ l1_struct_0(k8_tmap_1(sK2,sK3))
    | ~ l1_struct_0(sK2)
    | v1_funct_1(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),X0_57))
    | ~ v1_funct_1(k9_tmap_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_2293])).

cnf(c_3201,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ l1_struct_0(k8_tmap_1(sK2,sK3))
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK2)
    | v1_funct_1(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4))
    | ~ v1_funct_1(k9_tmap_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_2697])).

cnf(c_3202,plain,
    ( v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
    | m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top
    | l1_struct_0(k8_tmap_1(sK2,sK3)) != iProver_top
    | l1_struct_0(sK4) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)) = iProver_top
    | v1_funct_1(k9_tmap_1(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3201])).

cnf(c_26,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK1(X2,X1,X0),u1_struct_0(X1))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_623,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | m1_subset_1(sK1(X2,X1,X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4) != X0
    | k8_tmap_1(sK2,sK3) != X2
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_28])).

cnf(c_624,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | m1_subset_1(sK1(k8_tmap_1(sK2,sK3),sK4,k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)),u1_struct_0(sK4))
    | v2_struct_0(k8_tmap_1(sK2,sK3))
    | v2_struct_0(sK4)
    | ~ v1_funct_1(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4))
    | ~ v2_pre_topc(k8_tmap_1(sK2,sK3))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(k8_tmap_1(sK2,sK3))
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_623])).

cnf(c_626,plain,
    ( v2_struct_0(k8_tmap_1(sK2,sK3))
    | m1_subset_1(sK1(k8_tmap_1(sK2,sK3),sK4,k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)),u1_struct_0(sK4))
    | ~ m1_subset_1(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v1_funct_2(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ v1_funct_1(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4))
    | ~ v2_pre_topc(k8_tmap_1(sK2,sK3))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(k8_tmap_1(sK2,sK3))
    | ~ l1_pre_topc(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_624,c_31])).

cnf(c_627,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | m1_subset_1(sK1(k8_tmap_1(sK2,sK3),sK4,k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)),u1_struct_0(sK4))
    | v2_struct_0(k8_tmap_1(sK2,sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4))
    | ~ v2_pre_topc(k8_tmap_1(sK2,sK3))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(k8_tmap_1(sK2,sK3))
    | ~ l1_pre_topc(sK4) ),
    inference(renaming,[status(thm)],[c_626])).

cnf(c_959,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | m1_subset_1(sK1(k8_tmap_1(sK2,sK3),sK4,k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)),u1_struct_0(sK4))
    | v2_struct_0(k8_tmap_1(sK2,sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4))
    | ~ v2_pre_topc(k8_tmap_1(sK2,sK3))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(k8_tmap_1(sK2,sK3))
    | ~ l1_pre_topc(sK4) ),
    inference(subtyping,[status(esa)],[c_627])).

cnf(c_1726,plain,
    ( v1_funct_2(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top
    | m1_subset_1(sK1(k8_tmap_1(sK2,sK3),sK4,k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)),u1_struct_0(sK4)) = iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | v1_funct_1(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)) != iProver_top
    | v2_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_959])).

cnf(c_625,plain,
    ( v1_funct_2(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top
    | m1_subset_1(sK1(k8_tmap_1(sK2,sK3),sK4,k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)),u1_struct_0(sK4)) = iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v1_funct_1(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)) != iProver_top
    | v2_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_624])).

cnf(c_2495,plain,
    ( m1_subset_1(sK1(k8_tmap_1(sK2,sK3),sK4,k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)),u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1726,c_37,c_38,c_39,c_41,c_42,c_43,c_625,c_2129,c_2138,c_2160,c_2166,c_2393])).

cnf(c_2496,plain,
    ( v1_funct_2(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top
    | m1_subset_1(sK1(k8_tmap_1(sK2,sK3),sK4,k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)),u1_struct_0(sK4)) = iProver_top
    | v1_funct_1(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2495])).

cnf(c_3731,plain,
    ( v1_funct_2(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
    | v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
    | m1_subset_1(sK1(k8_tmap_1(sK2,sK3),sK4,k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)),u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top
    | l1_struct_0(k8_tmap_1(sK2,sK3)) != iProver_top
    | l1_struct_0(sK4) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)) != iProver_top
    | v1_funct_1(k9_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1698,c_2496])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_986,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(X1_57))
    | v1_funct_2(k2_tmap_1(X0_57,X1_57,X0_55,X2_57),u1_struct_0(X2_57),u1_struct_0(X1_57))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
    | ~ l1_struct_0(X1_57)
    | ~ l1_struct_0(X0_57)
    | ~ l1_struct_0(X2_57)
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_2292,plain,
    ( v1_funct_2(k2_tmap_1(X0_57,X1_57,k9_tmap_1(sK2,sK3),X2_57),u1_struct_0(X2_57),u1_struct_0(X1_57))
    | ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(X0_57),u1_struct_0(X1_57))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
    | ~ l1_struct_0(X1_57)
    | ~ l1_struct_0(X0_57)
    | ~ l1_struct_0(X2_57)
    | ~ v1_funct_1(k9_tmap_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_986])).

cnf(c_2717,plain,
    ( v1_funct_2(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),X0_57),u1_struct_0(X0_57),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ l1_struct_0(X0_57)
    | ~ l1_struct_0(k8_tmap_1(sK2,sK3))
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(k9_tmap_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_2292])).

cnf(c_4007,plain,
    ( v1_funct_2(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ l1_struct_0(k8_tmap_1(sK2,sK3))
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(k9_tmap_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_2717])).

cnf(c_4008,plain,
    ( v1_funct_2(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK2,sK3))) = iProver_top
    | v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
    | m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top
    | l1_struct_0(k8_tmap_1(sK2,sK3)) != iProver_top
    | l1_struct_0(sK4) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(k9_tmap_1(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4007])).

cnf(c_4758,plain,
    ( m1_subset_1(k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4473,c_37,c_38,c_39,c_40,c_41,c_42,c_43,c_44,c_78,c_2144,c_2166,c_2196,c_2202,c_2393,c_2567,c_2863,c_3202,c_3731,c_4008])).

cnf(c_4763,plain,
    ( v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
    | m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top
    | l1_struct_0(k8_tmap_1(sK2,sK3)) != iProver_top
    | l1_struct_0(sK4) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(k9_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1698,c_4758])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4763,c_2863,c_2567,c_2393,c_2202,c_2196,c_2166,c_2144,c_78,c_43,c_41,c_39,c_38,c_37])).


%------------------------------------------------------------------------------
