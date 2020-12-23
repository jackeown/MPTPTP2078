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
% DateTime   : Thu Dec  3 12:24:14 EST 2020

% Result     : Theorem 3.69s
% Output     : CNFRefutation 3.69s
% Verified   : 
% Statistics : Number of formulae       :  288 (3775 expanded)
%              Number of clauses        :  194 ( 910 expanded)
%              Number of leaves         :   23 ( 827 expanded)
%              Depth                    :   28
%              Number of atoms          : 1508 (40460 expanded)
%              Number of equality atoms :  359 (1374 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <=> ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1))
              & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              & v1_funct_1(k9_tmap_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ( ( m1_pre_topc(X1,X0)
                & v1_tsep_1(X1,X0) )
            <=> ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
                & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1))
                & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
                & v1_funct_1(k9_tmap_1(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <~> ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1))
              & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              & v1_funct_1(k9_tmap_1(X0,X1)) ) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <~> ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1))
              & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              & v1_funct_1(k9_tmap_1(X0,X1)) ) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f59,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
            | ~ v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1))
            | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
            | ~ v1_funct_1(k9_tmap_1(X0,X1))
            | ~ m1_pre_topc(X1,X0)
            | ~ v1_tsep_1(X1,X0) )
          & ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1))
              & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              & v1_funct_1(k9_tmap_1(X0,X1)) )
            | ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) ) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f60,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
            | ~ v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1))
            | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
            | ~ v1_funct_1(k9_tmap_1(X0,X1))
            | ~ m1_pre_topc(X1,X0)
            | ~ v1_tsep_1(X1,X0) )
          & ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1))
              & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              & v1_funct_1(k9_tmap_1(X0,X1)) )
            | ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) ) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f59])).

fof(f62,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
            | ~ v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1))
            | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
            | ~ v1_funct_1(k9_tmap_1(X0,X1))
            | ~ m1_pre_topc(X1,X0)
            | ~ v1_tsep_1(X1,X0) )
          & ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1))
              & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              & v1_funct_1(k9_tmap_1(X0,X1)) )
            | ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) ) )
          & m1_pre_topc(X1,X0) )
     => ( ( ~ m1_subset_1(k9_tmap_1(X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,sK4)))))
          | ~ v5_pre_topc(k9_tmap_1(X0,sK4),X0,k8_tmap_1(X0,sK4))
          | ~ v1_funct_2(k9_tmap_1(X0,sK4),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,sK4)))
          | ~ v1_funct_1(k9_tmap_1(X0,sK4))
          | ~ m1_pre_topc(sK4,X0)
          | ~ v1_tsep_1(sK4,X0) )
        & ( ( m1_subset_1(k9_tmap_1(X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,sK4)))))
            & v5_pre_topc(k9_tmap_1(X0,sK4),X0,k8_tmap_1(X0,sK4))
            & v1_funct_2(k9_tmap_1(X0,sK4),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,sK4)))
            & v1_funct_1(k9_tmap_1(X0,sK4)) )
          | ( m1_pre_topc(sK4,X0)
            & v1_tsep_1(sK4,X0) ) )
        & m1_pre_topc(sK4,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1))
              | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(k9_tmap_1(X0,X1))
              | ~ m1_pre_topc(X1,X0)
              | ~ v1_tsep_1(X1,X0) )
            & ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
                & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1))
                & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
                & v1_funct_1(k9_tmap_1(X0,X1)) )
              | ( m1_pre_topc(X1,X0)
                & v1_tsep_1(X1,X0) ) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(k9_tmap_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X1)))))
            | ~ v5_pre_topc(k9_tmap_1(sK3,X1),sK3,k8_tmap_1(sK3,X1))
            | ~ v1_funct_2(k9_tmap_1(sK3,X1),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X1)))
            | ~ v1_funct_1(k9_tmap_1(sK3,X1))
            | ~ m1_pre_topc(X1,sK3)
            | ~ v1_tsep_1(X1,sK3) )
          & ( ( m1_subset_1(k9_tmap_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X1)))))
              & v5_pre_topc(k9_tmap_1(sK3,X1),sK3,k8_tmap_1(sK3,X1))
              & v1_funct_2(k9_tmap_1(sK3,X1),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X1)))
              & v1_funct_1(k9_tmap_1(sK3,X1)) )
            | ( m1_pre_topc(X1,sK3)
              & v1_tsep_1(X1,sK3) ) )
          & m1_pre_topc(X1,sK3) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( ( ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
      | ~ v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4))
      | ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
      | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
      | ~ m1_pre_topc(sK4,sK3)
      | ~ v1_tsep_1(sK4,sK3) )
    & ( ( m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
        & v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4))
        & v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
        & v1_funct_1(k9_tmap_1(sK3,sK4)) )
      | ( m1_pre_topc(sK4,sK3)
        & v1_tsep_1(sK4,sK3) ) )
    & m1_pre_topc(sK4,sK3)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f60,f62,f61])).

fof(f102,plain,(
    m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f63])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & v1_pre_topc(X2) )
             => ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( u1_struct_0(X1) = X3
                     => k6_tmap_1(X0,X3) = X2 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( k6_tmap_1(X0,X3) != X2
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( k6_tmap_1(X0,X3) = X2
                      | u1_struct_0(X1) != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( k6_tmap_1(X0,X3) != X2
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( k6_tmap_1(X0,X4) = X2
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f45])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k6_tmap_1(X0,X3) != X2
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k6_tmap_1(X0,sK0(X0,X1,X2)) != X2
        & u1_struct_0(X1) = sK0(X0,X1,X2)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ( k6_tmap_1(X0,sK0(X0,X1,X2)) != X2
                    & u1_struct_0(X1) = sK0(X0,X1,X2)
                    & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( k6_tmap_1(X0,X4) = X2
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f46,f47])).

fof(f69,plain,(
    ! [X4,X2,X0,X1] :
      ( k6_tmap_1(X0,X4) = X2
      | u1_struct_0(X1) != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( k6_tmap_1(X0,u1_struct_0(X1)) = X2
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f114,plain,(
    ! [X0,X1] :
      ( k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f113])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f97,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f86,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f99,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f63])).

fof(f100,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f63])).

fof(f101,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f63])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f20])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
          | X4 != X5 )
        & ( X4 = X5
          | ~ r1_funct_2(X0,X1,X2,X3,X4,X5) ) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X4 = X5
      | ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f89,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f87,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k9_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
                & v1_funct_1(X2) )
             => ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( u1_struct_0(X1) = X3
                     => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k9_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                      | u1_struct_0(X1) != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k9_tmap_1(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k9_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4))
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k9_tmap_1(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f49])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2)))
        & u1_struct_0(X1) = sK1(X0,X1,X2)
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k9_tmap_1(X0,X1) = X2
                  | ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2)))
                    & u1_struct_0(X1) = sK1(X0,X1,X2)
                    & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4))
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k9_tmap_1(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f50,f51])).

fof(f73,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4))
      | u1_struct_0(X1) != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | k9_tmap_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),X2,k7_tmap_1(X0,u1_struct_0(X1)))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k9_tmap_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f73])).

fof(f116,plain,(
    ! [X0,X1] :
      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(k9_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f115])).

fof(f88,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f90,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              | ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              | ~ v1_funct_1(k7_tmap_1(X0,X1)) )
            & ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
                & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
                & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
                & v1_funct_1(k7_tmap_1(X0,X1)) )
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              | ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              | ~ v1_funct_1(k7_tmap_1(X0,X1)) )
            & ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
                & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
                & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
                & v1_funct_1(k7_tmap_1(X0,X1)) )
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f57])).

fof(f96,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
      | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ v1_funct_1(k7_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f107,plain,
    ( v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4))
    | v1_tsep_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f63])).

fof(f94,plain,(
    ! [X0,X1] :
      ( v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f111,plain,
    ( ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4))
    | ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
    | ~ m1_pre_topc(sK4,sK3)
    | ~ v1_tsep_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f63])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tsep_1(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v3_pre_topc(X2,X0)
                  | u1_struct_0(X1) != X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tsep_1(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tsep_1(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tsep_1(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f53])).

fof(f55,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK2(X0,X1),X0)
        & u1_struct_0(X1) = sK2(X0,X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tsep_1(X1,X0)
              | ( ~ v3_pre_topc(sK2(X0,X1),X0)
                & u1_struct_0(X1) = sK2(X0,X1)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tsep_1(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f54,f55])).

fof(f77,plain,(
    ! [X0,X3,X1] :
      ( v3_pre_topc(X3,X0)
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f117,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f77])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(sK2(X0,X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | u1_struct_0(X1) = sK2(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f64,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_44,negated_conjecture,
    ( m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_4689,negated_conjecture,
    ( m1_pre_topc(sK4,sK3) ),
    inference(subtyping,[status(esa)],[c_44])).

cnf(c_5398,plain,
    ( m1_pre_topc(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4689])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(k8_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(k8_tmap_1(X1,X0))
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_33,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_22,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_21,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k8_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_20,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_352,plain,
    ( ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8,c_33,c_22,c_21,c_20])).

cnf(c_353,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(renaming,[status(thm)],[c_352])).

cnf(c_47,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1544,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_353,c_47])).

cnf(c_1545,plain,
    ( ~ m1_pre_topc(X0,sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | k6_tmap_1(sK3,u1_struct_0(X0)) = k8_tmap_1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_1544])).

cnf(c_46,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_45,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1549,plain,
    ( ~ m1_pre_topc(X0,sK3)
    | k6_tmap_1(sK3,u1_struct_0(X0)) = k8_tmap_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1545,c_46,c_45])).

cnf(c_4682,plain,
    ( ~ m1_pre_topc(X0_58,sK3)
    | k6_tmap_1(sK3,u1_struct_0(X0_58)) = k8_tmap_1(sK3,X0_58) ),
    inference(subtyping,[status(esa)],[c_1549])).

cnf(c_5406,plain,
    ( k6_tmap_1(sK3,u1_struct_0(X0_58)) = k8_tmap_1(sK3,X0_58)
    | m1_pre_topc(X0_58,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4682])).

cnf(c_5953,plain,
    ( k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_5398,c_5406])).

cnf(c_3,plain,
    ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
    | ~ v1_funct_2(X5,X2,X3)
    | ~ v1_funct_2(X4,X0,X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | X4 = X5 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2255,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_45])).

cnf(c_2256,plain,
    ( ~ m1_pre_topc(X0,sK3)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unflattening,[status(thm)],[c_2255])).

cnf(c_23,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(k9_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X0)))))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1620,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(k9_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X0)))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_47])).

cnf(c_1621,plain,
    ( ~ m1_pre_topc(X0,sK3)
    | m1_subset_1(k9_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X0)))))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1620])).

cnf(c_1625,plain,
    ( ~ m1_pre_topc(X0,sK3)
    | m1_subset_1(k9_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X0))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1621,c_46,c_45])).

cnf(c_25,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k9_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1598,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k9_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_47])).

cnf(c_1599,plain,
    ( ~ m1_pre_topc(X0,sK3)
    | ~ v2_pre_topc(sK3)
    | v1_funct_1(k9_tmap_1(sK3,X0))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1598])).

cnf(c_1603,plain,
    ( v1_funct_1(k9_tmap_1(sK3,X0))
    | ~ m1_pre_topc(X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1599,c_46,c_45])).

cnf(c_1604,plain,
    ( ~ m1_pre_topc(X0,sK3)
    | v1_funct_1(k9_tmap_1(sK3,X0)) ),
    inference(renaming,[status(thm)],[c_1603])).

cnf(c_12,plain,
    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
    | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_24,plain,
    ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_342,plain,
    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_24])).

cnf(c_1451,plain,
    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_342,c_47])).

cnf(c_1452,plain,
    ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X0)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0))),k9_tmap_1(sK3,X0),k7_tmap_1(sK3,u1_struct_0(X0)))
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_subset_1(k9_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X0)))))
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(k9_tmap_1(sK3,X0))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1451])).

cnf(c_1456,plain,
    ( ~ v1_funct_1(k9_tmap_1(sK3,X0))
    | r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X0)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0))),k9_tmap_1(sK3,X0),k7_tmap_1(sK3,u1_struct_0(X0)))
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_subset_1(k9_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X0)))))
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1452,c_46,c_45])).

cnf(c_1457,plain,
    ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X0)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0))),k9_tmap_1(sK3,X0),k7_tmap_1(sK3,u1_struct_0(X0)))
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_subset_1(k9_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X0)))))
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_funct_1(k9_tmap_1(sK3,X0)) ),
    inference(renaming,[status(thm)],[c_1456])).

cnf(c_1615,plain,
    ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X0)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0))),k9_tmap_1(sK3,X0),k7_tmap_1(sK3,u1_struct_0(X0)))
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_subset_1(k9_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X0)))))
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1604,c_1457])).

cnf(c_1637,plain,
    ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X0)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0))),k9_tmap_1(sK3,X0),k7_tmap_1(sK3,u1_struct_0(X0)))
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1625,c_1615])).

cnf(c_2381,plain,
    ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X0)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0))),k9_tmap_1(sK3,X0),k7_tmap_1(sK3,u1_struct_0(X0)))
    | ~ m1_pre_topc(X0,sK3) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2256,c_1637])).

cnf(c_2444,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X5)
    | ~ m1_pre_topc(X6,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X5)
    | X3 = X0
    | k9_tmap_1(sK3,X6) != X0
    | k7_tmap_1(sK3,u1_struct_0(X6)) != X3
    | u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X6))) != X5
    | u1_struct_0(k8_tmap_1(sK3,X6)) != X2
    | u1_struct_0(sK3) != X4
    | u1_struct_0(sK3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_2381])).

cnf(c_2445,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK3,X0),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X0)))
    | ~ v1_funct_2(k7_tmap_1(sK3,u1_struct_0(X0)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0))))
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_subset_1(k9_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X0)))))
    | ~ m1_subset_1(k7_tmap_1(sK3,u1_struct_0(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0))))))
    | ~ v1_funct_1(k9_tmap_1(sK3,X0))
    | ~ v1_funct_1(k7_tmap_1(sK3,u1_struct_0(X0)))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,X0)))
    | k7_tmap_1(sK3,u1_struct_0(X0)) = k9_tmap_1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_2444])).

cnf(c_1478,plain,
    ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_47])).

cnf(c_1479,plain,
    ( v1_funct_2(k9_tmap_1(sK3,X0),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X0)))
    | ~ m1_pre_topc(X0,sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1478])).

cnf(c_1483,plain,
    ( v1_funct_2(k9_tmap_1(sK3,X0),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X0)))
    | ~ m1_pre_topc(X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1479,c_46,c_45])).

cnf(c_2449,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK3,u1_struct_0(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0))))))
    | ~ v1_funct_2(k7_tmap_1(sK3,u1_struct_0(X0)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0))))
    | ~ m1_pre_topc(X0,sK3)
    | ~ v1_funct_1(k7_tmap_1(sK3,u1_struct_0(X0)))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,X0)))
    | k7_tmap_1(sK3,u1_struct_0(X0)) = k9_tmap_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2445,c_46,c_45,c_1479,c_1599,c_1621])).

cnf(c_2450,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK3,u1_struct_0(X0)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0))))
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_subset_1(k7_tmap_1(sK3,u1_struct_0(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0))))))
    | ~ v1_funct_1(k7_tmap_1(sK3,u1_struct_0(X0)))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,X0)))
    | k7_tmap_1(sK3,u1_struct_0(X0)) = k9_tmap_1(sK3,X0) ),
    inference(renaming,[status(thm)],[c_2449])).

cnf(c_4666,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK3,u1_struct_0(X0_58)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0_58))))
    | ~ m1_pre_topc(X0_58,sK3)
    | ~ m1_subset_1(k7_tmap_1(sK3,u1_struct_0(X0_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0_58))))))
    | ~ v1_funct_1(k7_tmap_1(sK3,u1_struct_0(X0_58)))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0_58))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,X0_58)))
    | k7_tmap_1(sK3,u1_struct_0(X0_58)) = k9_tmap_1(sK3,X0_58) ),
    inference(subtyping,[status(esa)],[c_2450])).

cnf(c_5422,plain,
    ( k7_tmap_1(sK3,u1_struct_0(X0_58)) = k9_tmap_1(sK3,X0_58)
    | v1_funct_2(k7_tmap_1(sK3,u1_struct_0(X0_58)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0_58)))) != iProver_top
    | m1_pre_topc(X0_58,sK3) != iProver_top
    | m1_subset_1(k7_tmap_1(sK3,u1_struct_0(X0_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0_58)))))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK3,u1_struct_0(X0_58))) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0_58)))) = iProver_top
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,X0_58))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4666])).

cnf(c_50,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_4775,plain,
    ( k6_tmap_1(sK3,u1_struct_0(X0_58)) = k8_tmap_1(sK3,X0_58)
    | m1_pre_topc(X0_58,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4682])).

cnf(c_4817,plain,
    ( k7_tmap_1(sK3,u1_struct_0(X0_58)) = k9_tmap_1(sK3,X0_58)
    | v1_funct_2(k7_tmap_1(sK3,u1_struct_0(X0_58)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0_58)))) != iProver_top
    | m1_pre_topc(X0_58,sK3) != iProver_top
    | m1_subset_1(k7_tmap_1(sK3,u1_struct_0(X0_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0_58)))))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK3,u1_struct_0(X0_58))) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0_58)))) = iProver_top
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,X0_58))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4666])).

cnf(c_4694,plain,
    ( ~ m1_pre_topc(X0_58,X1_58)
    | m1_subset_1(u1_struct_0(X0_58),k1_zfmisc_1(u1_struct_0(X1_58)))
    | ~ l1_pre_topc(X1_58) ),
    inference(subtyping,[status(esa)],[c_33])).

cnf(c_5766,plain,
    ( ~ m1_pre_topc(X0_58,sK3)
    | m1_subset_1(u1_struct_0(X0_58),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_4694])).

cnf(c_5772,plain,
    ( m1_pre_topc(X0_58,sK3) != iProver_top
    | m1_subset_1(u1_struct_0(X0_58),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5766])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1714,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_47])).

cnf(c_1715,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1714])).

cnf(c_1719,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1715,c_46,c_45])).

cnf(c_4675,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k7_tmap_1(sK3,X0_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0_57))))) ),
    inference(subtyping,[status(esa)],[c_1719])).

cnf(c_5768,plain,
    ( m1_subset_1(k7_tmap_1(sK3,u1_struct_0(X0_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0_58))))))
    | ~ m1_subset_1(u1_struct_0(X0_58),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_4675])).

cnf(c_5786,plain,
    ( m1_subset_1(k7_tmap_1(sK3,u1_struct_0(X0_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0_58)))))) = iProver_top
    | m1_subset_1(u1_struct_0(X0_58),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5768])).

cnf(c_18,plain,
    ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1496,plain,
    ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_47])).

cnf(c_1497,plain,
    ( v1_funct_2(k7_tmap_1(sK3,X0),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1496])).

cnf(c_1501,plain,
    ( v1_funct_2(k7_tmap_1(sK3,X0),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1497,c_46,c_45])).

cnf(c_4683,plain,
    ( v1_funct_2(k7_tmap_1(sK3,X0_57),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0_57)))
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subtyping,[status(esa)],[c_1501])).

cnf(c_5767,plain,
    ( v1_funct_2(k7_tmap_1(sK3,u1_struct_0(X0_58)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0_58))))
    | ~ m1_subset_1(u1_struct_0(X0_58),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_4683])).

cnf(c_5790,plain,
    ( v1_funct_2(k7_tmap_1(sK3,u1_struct_0(X0_58)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0_58)))) = iProver_top
    | m1_subset_1(u1_struct_0(X0_58),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5767])).

cnf(c_5393,plain,
    ( m1_pre_topc(X0_58,X1_58) != iProver_top
    | m1_subset_1(u1_struct_0(X0_58),k1_zfmisc_1(u1_struct_0(X1_58))) = iProver_top
    | l1_pre_topc(X1_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4694])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k7_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1696,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k7_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_47])).

cnf(c_1697,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | v1_funct_1(k7_tmap_1(sK3,X0))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1696])).

cnf(c_1701,plain,
    ( v1_funct_1(k7_tmap_1(sK3,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1697,c_46,c_45])).

cnf(c_1702,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_funct_1(k7_tmap_1(sK3,X0)) ),
    inference(renaming,[status(thm)],[c_1701])).

cnf(c_4676,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_funct_1(k7_tmap_1(sK3,X0_57)) ),
    inference(subtyping,[status(esa)],[c_1702])).

cnf(c_5412,plain,
    ( m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK3,X0_57)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4676])).

cnf(c_5998,plain,
    ( m1_pre_topc(X0_58,sK3) != iProver_top
    | v1_funct_1(k7_tmap_1(sK3,u1_struct_0(X0_58))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5393,c_5412])).

cnf(c_4709,plain,
    ( X0_58 != X1_58
    | u1_struct_0(X0_58) = u1_struct_0(X1_58) ),
    theory(equality)).

cnf(c_6079,plain,
    ( X0_58 != k8_tmap_1(sK3,X1_58)
    | u1_struct_0(X0_58) = u1_struct_0(k8_tmap_1(sK3,X1_58)) ),
    inference(instantiation,[status(thm)],[c_4709])).

cnf(c_6332,plain,
    ( k6_tmap_1(sK3,u1_struct_0(X0_58)) != k8_tmap_1(sK3,X0_58)
    | u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0_58))) = u1_struct_0(k8_tmap_1(sK3,X0_58)) ),
    inference(instantiation,[status(thm)],[c_6079])).

cnf(c_4710,plain,
    ( ~ v1_xboole_0(X0_57)
    | v1_xboole_0(X1_57)
    | X1_57 != X0_57 ),
    theory(equality)).

cnf(c_5962,plain,
    ( v1_xboole_0(X0_57)
    | ~ v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,X0_58)))
    | X0_57 != u1_struct_0(k8_tmap_1(sK3,X0_58)) ),
    inference(instantiation,[status(thm)],[c_4710])).

cnf(c_6078,plain,
    ( v1_xboole_0(u1_struct_0(X0_58))
    | ~ v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,X1_58)))
    | u1_struct_0(X0_58) != u1_struct_0(k8_tmap_1(sK3,X1_58)) ),
    inference(instantiation,[status(thm)],[c_5962])).

cnf(c_6408,plain,
    ( v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0_58))))
    | ~ v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,X0_58)))
    | u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0_58))) != u1_struct_0(k8_tmap_1(sK3,X0_58)) ),
    inference(instantiation,[status(thm)],[c_6078])).

cnf(c_6409,plain,
    ( u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0_58))) != u1_struct_0(k8_tmap_1(sK3,X0_58))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0_58)))) = iProver_top
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,X0_58))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6408])).

cnf(c_11240,plain,
    ( v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0_58)))) = iProver_top
    | m1_pre_topc(X0_58,sK3) != iProver_top
    | k7_tmap_1(sK3,u1_struct_0(X0_58)) = k9_tmap_1(sK3,X0_58) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5422,c_50,c_4775,c_4817,c_5772,c_5786,c_5790,c_5998,c_6332,c_6409])).

cnf(c_11241,plain,
    ( k7_tmap_1(sK3,u1_struct_0(X0_58)) = k9_tmap_1(sK3,X0_58)
    | m1_pre_topc(X0_58,sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0_58)))) = iProver_top ),
    inference(renaming,[status(thm)],[c_11240])).

cnf(c_11250,plain,
    ( k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4)
    | m1_pre_topc(sK4,sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5953,c_11241])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1562,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_47])).

cnf(c_1563,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | u1_struct_0(k6_tmap_1(sK3,X0)) = u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_1562])).

cnf(c_1567,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | u1_struct_0(k6_tmap_1(sK3,X0)) = u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1563,c_46,c_45])).

cnf(c_4681,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK3)))
    | u1_struct_0(k6_tmap_1(sK3,X0_57)) = u1_struct_0(sK3) ),
    inference(subtyping,[status(esa)],[c_1567])).

cnf(c_5407,plain,
    ( u1_struct_0(k6_tmap_1(sK3,X0_57)) = u1_struct_0(sK3)
    | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4681])).

cnf(c_6089,plain,
    ( u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0_58))) = u1_struct_0(sK3)
    | m1_pre_topc(X0_58,sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5393,c_5407])).

cnf(c_6888,plain,
    ( m1_pre_topc(X0_58,sK3) != iProver_top
    | u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0_58))) = u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6089,c_50])).

cnf(c_6889,plain,
    ( u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0_58))) = u1_struct_0(sK3)
    | m1_pre_topc(X0_58,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_6888])).

cnf(c_6896,plain,
    ( u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))) = u1_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_5398,c_6889])).

cnf(c_6904,plain,
    ( u1_struct_0(k8_tmap_1(sK3,sK4)) = u1_struct_0(sK3) ),
    inference(light_normalisation,[status(thm)],[c_6896,c_5953])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1876,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_47])).

cnf(c_1877,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | k7_tmap_1(sK3,X0) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_1876])).

cnf(c_1881,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k7_tmap_1(sK3,X0) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1877,c_46,c_45])).

cnf(c_4672,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK3)))
    | k7_tmap_1(sK3,X0_57) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_1881])).

cnf(c_5416,plain,
    ( k7_tmap_1(sK3,X0_57) = k6_partfun1(u1_struct_0(sK3))
    | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4672])).

cnf(c_6114,plain,
    ( k7_tmap_1(sK3,u1_struct_0(X0_58)) = k6_partfun1(u1_struct_0(sK3))
    | m1_pre_topc(X0_58,sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5393,c_5416])).

cnf(c_7212,plain,
    ( m1_pre_topc(X0_58,sK3) != iProver_top
    | k7_tmap_1(sK3,u1_struct_0(X0_58)) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6114,c_50])).

cnf(c_7213,plain,
    ( k7_tmap_1(sK3,u1_struct_0(X0_58)) = k6_partfun1(u1_struct_0(sK3))
    | m1_pre_topc(X0_58,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_7212])).

cnf(c_7220,plain,
    ( k7_tmap_1(sK3,u1_struct_0(sK4)) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(superposition,[status(thm)],[c_5398,c_7213])).

cnf(c_11272,plain,
    ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
    | m1_pre_topc(sK4,sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11250,c_6904,c_7220])).

cnf(c_28,plain,
    ( ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
    | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | v3_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k7_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_314,plain,
    ( ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
    | v3_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k7_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_28,c_18])).

cnf(c_39,negated_conjecture,
    ( v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4))
    | v1_tsep_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_617,plain,
    ( v3_pre_topc(X0,X1)
    | v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(k7_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(X1,X0) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(X1,X0) != k9_tmap_1(sK3,sK4)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_314,c_39])).

cnf(c_618,plain,
    ( v3_pre_topc(X0,sK3)
    | v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))))
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(k7_tmap_1(sK3,X0))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_617])).

cnf(c_622,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_tsep_1(sK4,sK3)
    | v3_pre_topc(X0,sK3)
    | ~ v1_funct_1(k7_tmap_1(sK3,X0))
    | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_618,c_47,c_46,c_45])).

cnf(c_623,plain,
    ( v3_pre_topc(X0,sK3)
    | v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))))
    | ~ v1_funct_1(k7_tmap_1(sK3,X0))
    | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4) ),
    inference(renaming,[status(thm)],[c_622])).

cnf(c_1939,plain,
    ( v3_pre_topc(X0,sK3)
    | v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))))
    | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1702,c_623])).

cnf(c_1946,plain,
    ( v3_pre_topc(X0,sK3)
    | v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1719,c_1939])).

cnf(c_4671,plain,
    ( v3_pre_topc(X0_57,sK3)
    | v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK3)))
    | k6_tmap_1(sK3,X0_57) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,X0_57) != k9_tmap_1(sK3,sK4) ),
    inference(subtyping,[status(esa)],[c_1946])).

cnf(c_5417,plain,
    ( k6_tmap_1(sK3,X0_57) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,X0_57) != k9_tmap_1(sK3,sK4)
    | v3_pre_topc(X0_57,sK3) = iProver_top
    | v1_tsep_1(sK4,sK3) = iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4671])).

cnf(c_7102,plain,
    ( k7_tmap_1(sK3,u1_struct_0(sK4)) != k9_tmap_1(sK3,sK4)
    | v3_pre_topc(u1_struct_0(sK4),sK3) = iProver_top
    | v1_tsep_1(sK4,sK3) = iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5953,c_5417])).

cnf(c_51,plain,
    ( m1_pre_topc(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_4702,plain,
    ( X0_58 = X0_58 ),
    theory(equality)).

cnf(c_4750,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_4702])).

cnf(c_6145,plain,
    ( ~ m1_pre_topc(sK4,sK3)
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_5766])).

cnf(c_6146,plain,
    ( m1_pre_topc(sK4,sK3) != iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6145])).

cnf(c_30,plain,
    ( v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
    | ~ v3_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_35,negated_conjecture,
    ( ~ v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4))
    | ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ v1_tsep_1(sK4,sK3)
    | ~ m1_pre_topc(sK4,sK3)
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4)) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_291,plain,
    ( ~ v1_tsep_1(sK4,sK3)
    | ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_35,c_44])).

cnf(c_292,negated_conjecture,
    ( ~ v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4))
    | ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4)) ),
    inference(renaming,[status(thm)],[c_291])).

cnf(c_581,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ v3_pre_topc(X0,X1)
    | ~ v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(X1,X0) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(X1,X0) != k9_tmap_1(sK3,sK4)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_292])).

cnf(c_582,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ v3_pre_topc(X0,sK3)
    | ~ v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_581])).

cnf(c_586,plain,
    ( ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_tsep_1(sK4,sK3)
    | ~ v3_pre_topc(X0,sK3)
    | ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
    | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_582,c_47,c_46,c_45])).

cnf(c_587,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ v3_pre_topc(X0,sK3)
    | ~ v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
    | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4) ),
    inference(renaming,[status(thm)],[c_586])).

cnf(c_4686,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ v3_pre_topc(X0_57,sK3)
    | ~ v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
    | k6_tmap_1(sK3,X0_57) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,X0_57) != k9_tmap_1(sK3,sK4) ),
    inference(subtyping,[status(esa)],[c_587])).

cnf(c_4698,plain,
    ( ~ v3_pre_topc(X0_57,sK3)
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK3)))
    | k6_tmap_1(sK3,X0_57) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,X0_57) != k9_tmap_1(sK3,sK4)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_4686])).

cnf(c_5402,plain,
    ( k6_tmap_1(sK3,X0_57) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,X0_57) != k9_tmap_1(sK3,sK4)
    | v3_pre_topc(X0_57,sK3) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4698])).

cnf(c_6651,plain,
    ( k7_tmap_1(sK3,u1_struct_0(sK4)) != k9_tmap_1(sK3,sK4)
    | v3_pre_topc(u1_struct_0(sK4),sK3) != iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_5953,c_5402])).

cnf(c_5795,plain,
    ( ~ v3_pre_topc(u1_struct_0(X0_58),sK3)
    | ~ m1_subset_1(u1_struct_0(X0_58),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ sP0_iProver_split
    | k6_tmap_1(sK3,u1_struct_0(X0_58)) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,u1_struct_0(X0_58)) != k9_tmap_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_4698])).

cnf(c_5911,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK4),sK3)
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ sP0_iProver_split
    | k6_tmap_1(sK3,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,u1_struct_0(sK4)) != k9_tmap_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_5795])).

cnf(c_5913,plain,
    ( k6_tmap_1(sK3,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,u1_struct_0(sK4)) != k9_tmap_1(sK3,sK4)
    | v3_pre_topc(u1_struct_0(sK4),sK3) != iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5911])).

cnf(c_5912,plain,
    ( ~ m1_pre_topc(sK4,sK3)
    | k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_4682])).

cnf(c_16,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_332,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16,c_33])).

cnf(c_333,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_332])).

cnf(c_4687,plain,
    ( v3_pre_topc(u1_struct_0(X0_58),X1_58)
    | ~ v1_tsep_1(X0_58,X1_58)
    | ~ m1_pre_topc(X0_58,X1_58)
    | ~ l1_pre_topc(X1_58) ),
    inference(subtyping,[status(esa)],[c_333])).

cnf(c_5794,plain,
    ( v3_pre_topc(u1_struct_0(X0_58),sK3)
    | ~ v1_tsep_1(X0_58,sK3)
    | ~ m1_pre_topc(X0_58,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_4687])).

cnf(c_5987,plain,
    ( v3_pre_topc(u1_struct_0(sK4),sK3)
    | ~ v1_tsep_1(sK4,sK3)
    | ~ m1_pre_topc(sK4,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_5794])).

cnf(c_5988,plain,
    ( v3_pre_topc(u1_struct_0(sK4),sK3) = iProver_top
    | v1_tsep_1(sK4,sK3) != iProver_top
    | m1_pre_topc(sK4,sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5987])).

cnf(c_8306,plain,
    ( k7_tmap_1(sK3,u1_struct_0(sK4)) != k9_tmap_1(sK3,sK4)
    | sP0_iProver_split != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6651,c_50,c_44,c_51,c_5913,c_5912,c_5988,c_6146,c_7102])).

cnf(c_13,plain,
    ( ~ v3_pre_topc(sK2(X0,X1),X0)
    | v1_tsep_1(X1,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_4697,plain,
    ( ~ v3_pre_topc(sK2(X0_58,X1_58),X0_58)
    | v1_tsep_1(X1_58,X0_58)
    | ~ m1_pre_topc(X1_58,X0_58)
    | ~ l1_pre_topc(X0_58) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_8634,plain,
    ( ~ v3_pre_topc(sK2(sK3,sK4),sK3)
    | v1_tsep_1(sK4,sK3)
    | ~ m1_pre_topc(sK4,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_4697])).

cnf(c_8635,plain,
    ( v3_pre_topc(sK2(sK3,sK4),sK3) != iProver_top
    | v1_tsep_1(sK4,sK3) = iProver_top
    | m1_pre_topc(sK4,sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8634])).

cnf(c_4679,plain,
    ( ~ m1_pre_topc(X0_58,sK3)
    | v1_funct_1(k9_tmap_1(sK3,X0_58)) ),
    inference(subtyping,[status(esa)],[c_1604])).

cnf(c_5409,plain,
    ( m1_pre_topc(X0_58,sK3) != iProver_top
    | v1_funct_1(k9_tmap_1(sK3,X0_58)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4679])).

cnf(c_4678,plain,
    ( ~ m1_pre_topc(X0_58,sK3)
    | m1_subset_1(k9_tmap_1(sK3,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X0_58))))) ),
    inference(subtyping,[status(esa)],[c_1625])).

cnf(c_5410,plain,
    ( m1_pre_topc(X0_58,sK3) != iProver_top
    | m1_subset_1(k9_tmap_1(sK3,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X0_58))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4678])).

cnf(c_4699,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_4686])).

cnf(c_5401,plain,
    ( v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
    | v1_tsep_1(sK4,sK3) != iProver_top
    | m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) != iProver_top
    | v1_funct_1(k9_tmap_1(sK3,sK4)) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4699])).

cnf(c_6679,plain,
    ( v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
    | v1_tsep_1(sK4,sK3) != iProver_top
    | m1_pre_topc(sK4,sK3) != iProver_top
    | v1_funct_1(k9_tmap_1(sK3,sK4)) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_5410,c_5401])).

cnf(c_6908,plain,
    ( v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
    | v1_tsep_1(sK4,sK3) != iProver_top
    | m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k9_tmap_1(sK3,sK4)) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_6904,c_5401])).

cnf(c_6937,plain,
    ( m1_pre_topc(sK4,sK3) != iProver_top
    | m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6904,c_5410])).

cnf(c_4684,plain,
    ( v1_funct_2(k9_tmap_1(sK3,X0_58),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X0_58)))
    | ~ m1_pre_topc(X0_58,sK3) ),
    inference(subtyping,[status(esa)],[c_1483])).

cnf(c_5404,plain,
    ( v1_funct_2(k9_tmap_1(sK3,X0_58),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X0_58))) = iProver_top
    | m1_pre_topc(X0_58,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4684])).

cnf(c_6938,plain,
    ( v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK3)) = iProver_top
    | m1_pre_topc(sK4,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6904,c_5404])).

cnf(c_8673,plain,
    ( v1_tsep_1(sK4,sK3) != iProver_top
    | v1_funct_1(k9_tmap_1(sK3,sK4)) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6679,c_51,c_6908,c_6937,c_6938])).

cnf(c_8681,plain,
    ( v1_tsep_1(sK4,sK3) != iProver_top
    | m1_pre_topc(sK4,sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_5409,c_8673])).

cnf(c_8818,plain,
    ( v1_tsep_1(sK4,sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8681,c_51])).

cnf(c_14,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK2(X1,X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_4696,plain,
    ( v1_tsep_1(X0_58,X1_58)
    | ~ m1_pre_topc(X0_58,X1_58)
    | ~ l1_pre_topc(X1_58)
    | sK2(X1_58,X0_58) = u1_struct_0(X0_58) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_5391,plain,
    ( sK2(X0_58,X1_58) = u1_struct_0(X1_58)
    | v1_tsep_1(X1_58,X0_58) = iProver_top
    | m1_pre_topc(X1_58,X0_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4696])).

cnf(c_5871,plain,
    ( sK2(sK3,sK4) = u1_struct_0(sK4)
    | v1_tsep_1(sK4,sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5398,c_5391])).

cnf(c_6391,plain,
    ( v1_tsep_1(sK4,sK3) = iProver_top
    | sK2(sK3,sK4) = u1_struct_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5871,c_50])).

cnf(c_6392,plain,
    ( sK2(sK3,sK4) = u1_struct_0(sK4)
    | v1_tsep_1(sK4,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_6391])).

cnf(c_8825,plain,
    ( sK2(sK3,sK4) = u1_struct_0(sK4)
    | sP0_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_6392,c_8818])).

cnf(c_4725,plain,
    ( ~ v3_pre_topc(X0_57,X0_58)
    | v3_pre_topc(X1_57,X1_58)
    | X1_58 != X0_58
    | X1_57 != X0_57 ),
    theory(equality)).

cnf(c_5831,plain,
    ( v3_pre_topc(X0_57,X0_58)
    | ~ v3_pre_topc(u1_struct_0(X1_58),X2_58)
    | X0_58 != X2_58
    | X0_57 != u1_struct_0(X1_58) ),
    inference(instantiation,[status(thm)],[c_4725])).

cnf(c_9538,plain,
    ( v3_pre_topc(sK2(sK3,sK4),X0_58)
    | ~ v3_pre_topc(u1_struct_0(sK4),X1_58)
    | X0_58 != X1_58
    | sK2(sK3,sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_5831])).

cnf(c_9539,plain,
    ( X0_58 != X1_58
    | sK2(sK3,sK4) != u1_struct_0(sK4)
    | v3_pre_topc(sK2(sK3,sK4),X0_58) = iProver_top
    | v3_pre_topc(u1_struct_0(sK4),X1_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9538])).

cnf(c_9541,plain,
    ( sK3 != sK3
    | sK2(sK3,sK4) != u1_struct_0(sK4)
    | v3_pre_topc(sK2(sK3,sK4),sK3) = iProver_top
    | v3_pre_topc(u1_struct_0(sK4),sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_9539])).

cnf(c_10076,plain,
    ( k7_tmap_1(sK3,u1_struct_0(sK4)) != k9_tmap_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7102,c_50,c_51,c_4750,c_6146,c_8306,c_8635,c_8818,c_8825,c_9541])).

cnf(c_10078,plain,
    ( k9_tmap_1(sK3,sK4) != k6_partfun1(u1_struct_0(sK3)) ),
    inference(light_normalisation,[status(thm)],[c_10076,c_7220])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_163,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_165,plain,
    ( l1_pre_topc(sK3) != iProver_top
    | l1_struct_0(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_163])).

cnf(c_1,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_160,plain,
    ( v2_struct_0(X0) = iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_162,plain,
    ( v2_struct_0(sK3) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top
    | l1_struct_0(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_160])).

cnf(c_48,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11272,c_10078,c_165,c_162,c_51,c_50,c_48])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:24:54 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.69/0.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.69/0.96  
% 3.69/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.69/0.96  
% 3.69/0.96  ------  iProver source info
% 3.69/0.96  
% 3.69/0.96  git: date: 2020-06-30 10:37:57 +0100
% 3.69/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.69/0.96  git: non_committed_changes: false
% 3.69/0.96  git: last_make_outside_of_git: false
% 3.69/0.96  
% 3.69/0.96  ------ 
% 3.69/0.96  
% 3.69/0.96  ------ Input Options
% 3.69/0.96  
% 3.69/0.96  --out_options                           all
% 3.69/0.96  --tptp_safe_out                         true
% 3.69/0.96  --problem_path                          ""
% 3.69/0.96  --include_path                          ""
% 3.69/0.96  --clausifier                            res/vclausify_rel
% 3.69/0.96  --clausifier_options                    --mode clausify
% 3.69/0.96  --stdin                                 false
% 3.69/0.96  --stats_out                             all
% 3.69/0.96  
% 3.69/0.96  ------ General Options
% 3.69/0.96  
% 3.69/0.96  --fof                                   false
% 3.69/0.96  --time_out_real                         305.
% 3.69/0.96  --time_out_virtual                      -1.
% 3.69/0.96  --symbol_type_check                     false
% 3.69/0.96  --clausify_out                          false
% 3.69/0.96  --sig_cnt_out                           false
% 3.69/0.96  --trig_cnt_out                          false
% 3.69/0.96  --trig_cnt_out_tolerance                1.
% 3.69/0.96  --trig_cnt_out_sk_spl                   false
% 3.69/0.96  --abstr_cl_out                          false
% 3.69/0.96  
% 3.69/0.96  ------ Global Options
% 3.69/0.96  
% 3.69/0.96  --schedule                              default
% 3.69/0.96  --add_important_lit                     false
% 3.69/0.96  --prop_solver_per_cl                    1000
% 3.69/0.96  --min_unsat_core                        false
% 3.69/0.96  --soft_assumptions                      false
% 3.69/0.96  --soft_lemma_size                       3
% 3.69/0.96  --prop_impl_unit_size                   0
% 3.69/0.96  --prop_impl_unit                        []
% 3.69/0.96  --share_sel_clauses                     true
% 3.69/0.96  --reset_solvers                         false
% 3.69/0.96  --bc_imp_inh                            [conj_cone]
% 3.69/0.96  --conj_cone_tolerance                   3.
% 3.69/0.96  --extra_neg_conj                        none
% 3.69/0.96  --large_theory_mode                     true
% 3.69/0.96  --prolific_symb_bound                   200
% 3.69/0.96  --lt_threshold                          2000
% 3.69/0.96  --clause_weak_htbl                      true
% 3.69/0.96  --gc_record_bc_elim                     false
% 3.69/0.96  
% 3.69/0.96  ------ Preprocessing Options
% 3.69/0.96  
% 3.69/0.96  --preprocessing_flag                    true
% 3.69/0.96  --time_out_prep_mult                    0.1
% 3.69/0.96  --splitting_mode                        input
% 3.69/0.96  --splitting_grd                         true
% 3.69/0.96  --splitting_cvd                         false
% 3.69/0.96  --splitting_cvd_svl                     false
% 3.69/0.96  --splitting_nvd                         32
% 3.69/0.96  --sub_typing                            true
% 3.69/0.96  --prep_gs_sim                           true
% 3.69/0.96  --prep_unflatten                        true
% 3.69/0.96  --prep_res_sim                          true
% 3.69/0.96  --prep_upred                            true
% 3.69/0.96  --prep_sem_filter                       exhaustive
% 3.69/0.96  --prep_sem_filter_out                   false
% 3.69/0.96  --pred_elim                             true
% 3.69/0.96  --res_sim_input                         true
% 3.69/0.96  --eq_ax_congr_red                       true
% 3.69/0.96  --pure_diseq_elim                       true
% 3.69/0.96  --brand_transform                       false
% 3.69/0.96  --non_eq_to_eq                          false
% 3.69/0.96  --prep_def_merge                        true
% 3.69/0.96  --prep_def_merge_prop_impl              false
% 3.69/0.96  --prep_def_merge_mbd                    true
% 3.69/0.96  --prep_def_merge_tr_red                 false
% 3.69/0.96  --prep_def_merge_tr_cl                  false
% 3.69/0.96  --smt_preprocessing                     true
% 3.69/0.96  --smt_ac_axioms                         fast
% 3.69/0.96  --preprocessed_out                      false
% 3.69/0.96  --preprocessed_stats                    false
% 3.69/0.96  
% 3.69/0.96  ------ Abstraction refinement Options
% 3.69/0.96  
% 3.69/0.96  --abstr_ref                             []
% 3.69/0.96  --abstr_ref_prep                        false
% 3.69/0.96  --abstr_ref_until_sat                   false
% 3.69/0.96  --abstr_ref_sig_restrict                funpre
% 3.69/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 3.69/0.96  --abstr_ref_under                       []
% 3.69/0.96  
% 3.69/0.96  ------ SAT Options
% 3.69/0.96  
% 3.69/0.96  --sat_mode                              false
% 3.69/0.96  --sat_fm_restart_options                ""
% 3.69/0.96  --sat_gr_def                            false
% 3.69/0.96  --sat_epr_types                         true
% 3.69/0.96  --sat_non_cyclic_types                  false
% 3.69/0.96  --sat_finite_models                     false
% 3.69/0.96  --sat_fm_lemmas                         false
% 3.69/0.96  --sat_fm_prep                           false
% 3.69/0.96  --sat_fm_uc_incr                        true
% 3.69/0.96  --sat_out_model                         small
% 3.69/0.96  --sat_out_clauses                       false
% 3.69/0.96  
% 3.69/0.96  ------ QBF Options
% 3.69/0.96  
% 3.69/0.96  --qbf_mode                              false
% 3.69/0.96  --qbf_elim_univ                         false
% 3.69/0.96  --qbf_dom_inst                          none
% 3.69/0.96  --qbf_dom_pre_inst                      false
% 3.69/0.96  --qbf_sk_in                             false
% 3.69/0.96  --qbf_pred_elim                         true
% 3.69/0.96  --qbf_split                             512
% 3.69/0.96  
% 3.69/0.96  ------ BMC1 Options
% 3.69/0.96  
% 3.69/0.96  --bmc1_incremental                      false
% 3.69/0.96  --bmc1_axioms                           reachable_all
% 3.69/0.96  --bmc1_min_bound                        0
% 3.69/0.96  --bmc1_max_bound                        -1
% 3.69/0.96  --bmc1_max_bound_default                -1
% 3.69/0.96  --bmc1_symbol_reachability              true
% 3.69/0.96  --bmc1_property_lemmas                  false
% 3.69/0.96  --bmc1_k_induction                      false
% 3.69/0.96  --bmc1_non_equiv_states                 false
% 3.69/0.96  --bmc1_deadlock                         false
% 3.69/0.96  --bmc1_ucm                              false
% 3.69/0.96  --bmc1_add_unsat_core                   none
% 3.69/0.96  --bmc1_unsat_core_children              false
% 3.69/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 3.69/0.96  --bmc1_out_stat                         full
% 3.69/0.96  --bmc1_ground_init                      false
% 3.69/0.96  --bmc1_pre_inst_next_state              false
% 3.69/0.96  --bmc1_pre_inst_state                   false
% 3.69/0.96  --bmc1_pre_inst_reach_state             false
% 3.69/0.96  --bmc1_out_unsat_core                   false
% 3.69/0.96  --bmc1_aig_witness_out                  false
% 3.69/0.96  --bmc1_verbose                          false
% 3.69/0.96  --bmc1_dump_clauses_tptp                false
% 3.69/0.96  --bmc1_dump_unsat_core_tptp             false
% 3.69/0.96  --bmc1_dump_file                        -
% 3.69/0.96  --bmc1_ucm_expand_uc_limit              128
% 3.69/0.96  --bmc1_ucm_n_expand_iterations          6
% 3.69/0.96  --bmc1_ucm_extend_mode                  1
% 3.69/0.96  --bmc1_ucm_init_mode                    2
% 3.69/0.96  --bmc1_ucm_cone_mode                    none
% 3.69/0.96  --bmc1_ucm_reduced_relation_type        0
% 3.69/0.96  --bmc1_ucm_relax_model                  4
% 3.69/0.96  --bmc1_ucm_full_tr_after_sat            true
% 3.69/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 3.69/0.96  --bmc1_ucm_layered_model                none
% 3.69/0.96  --bmc1_ucm_max_lemma_size               10
% 3.69/0.96  
% 3.69/0.96  ------ AIG Options
% 3.69/0.96  
% 3.69/0.96  --aig_mode                              false
% 3.69/0.96  
% 3.69/0.96  ------ Instantiation Options
% 3.69/0.96  
% 3.69/0.96  --instantiation_flag                    true
% 3.69/0.96  --inst_sos_flag                         false
% 3.69/0.96  --inst_sos_phase                        true
% 3.69/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.69/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.69/0.96  --inst_lit_sel_side                     num_symb
% 3.69/0.96  --inst_solver_per_active                1400
% 3.69/0.96  --inst_solver_calls_frac                1.
% 3.69/0.96  --inst_passive_queue_type               priority_queues
% 3.69/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.69/0.96  --inst_passive_queues_freq              [25;2]
% 3.69/0.96  --inst_dismatching                      true
% 3.69/0.96  --inst_eager_unprocessed_to_passive     true
% 3.69/0.96  --inst_prop_sim_given                   true
% 3.69/0.96  --inst_prop_sim_new                     false
% 3.69/0.96  --inst_subs_new                         false
% 3.69/0.96  --inst_eq_res_simp                      false
% 3.69/0.96  --inst_subs_given                       false
% 3.69/0.96  --inst_orphan_elimination               true
% 3.69/0.96  --inst_learning_loop_flag               true
% 3.69/0.96  --inst_learning_start                   3000
% 3.69/0.96  --inst_learning_factor                  2
% 3.69/0.96  --inst_start_prop_sim_after_learn       3
% 3.69/0.96  --inst_sel_renew                        solver
% 3.69/0.96  --inst_lit_activity_flag                true
% 3.69/0.96  --inst_restr_to_given                   false
% 3.69/0.96  --inst_activity_threshold               500
% 3.69/0.96  --inst_out_proof                        true
% 3.69/0.96  
% 3.69/0.96  ------ Resolution Options
% 3.69/0.96  
% 3.69/0.96  --resolution_flag                       true
% 3.69/0.96  --res_lit_sel                           adaptive
% 3.69/0.96  --res_lit_sel_side                      none
% 3.69/0.96  --res_ordering                          kbo
% 3.69/0.96  --res_to_prop_solver                    active
% 3.69/0.96  --res_prop_simpl_new                    false
% 3.69/0.96  --res_prop_simpl_given                  true
% 3.69/0.96  --res_passive_queue_type                priority_queues
% 3.69/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.69/0.96  --res_passive_queues_freq               [15;5]
% 3.69/0.96  --res_forward_subs                      full
% 3.69/0.96  --res_backward_subs                     full
% 3.69/0.96  --res_forward_subs_resolution           true
% 3.69/0.96  --res_backward_subs_resolution          true
% 3.69/0.96  --res_orphan_elimination                true
% 3.69/0.96  --res_time_limit                        2.
% 3.69/0.96  --res_out_proof                         true
% 3.69/0.96  
% 3.69/0.96  ------ Superposition Options
% 3.69/0.96  
% 3.69/0.96  --superposition_flag                    true
% 3.69/0.96  --sup_passive_queue_type                priority_queues
% 3.69/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.69/0.96  --sup_passive_queues_freq               [8;1;4]
% 3.69/0.96  --demod_completeness_check              fast
% 3.69/0.96  --demod_use_ground                      true
% 3.69/0.96  --sup_to_prop_solver                    passive
% 3.69/0.96  --sup_prop_simpl_new                    true
% 3.69/0.96  --sup_prop_simpl_given                  true
% 3.69/0.96  --sup_fun_splitting                     false
% 3.69/0.96  --sup_smt_interval                      50000
% 3.69/0.96  
% 3.69/0.96  ------ Superposition Simplification Setup
% 3.69/0.96  
% 3.69/0.96  --sup_indices_passive                   []
% 3.69/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.69/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.69/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.69/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 3.69/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.69/0.96  --sup_full_bw                           [BwDemod]
% 3.69/0.96  --sup_immed_triv                        [TrivRules]
% 3.69/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.69/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.69/0.96  --sup_immed_bw_main                     []
% 3.69/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.69/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 3.69/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.69/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.69/0.96  
% 3.69/0.96  ------ Combination Options
% 3.69/0.96  
% 3.69/0.96  --comb_res_mult                         3
% 3.69/0.96  --comb_sup_mult                         2
% 3.69/0.96  --comb_inst_mult                        10
% 3.69/0.96  
% 3.69/0.96  ------ Debug Options
% 3.69/0.96  
% 3.69/0.96  --dbg_backtrace                         false
% 3.69/0.96  --dbg_dump_prop_clauses                 false
% 3.69/0.96  --dbg_dump_prop_clauses_file            -
% 3.69/0.96  --dbg_out_stat                          false
% 3.69/0.96  ------ Parsing...
% 3.69/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.69/0.96  
% 3.69/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 3.69/0.96  
% 3.69/0.96  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.69/0.96  
% 3.69/0.96  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.69/0.96  ------ Proving...
% 3.69/0.96  ------ Problem Properties 
% 3.69/0.96  
% 3.69/0.96  
% 3.69/0.96  clauses                                 34
% 3.69/0.96  conjectures                             5
% 3.69/0.96  EPR                                     3
% 3.69/0.96  Horn                                    22
% 3.69/0.96  unary                                   3
% 3.69/0.96  binary                                  15
% 3.69/0.96  lits                                    116
% 3.69/0.96  lits eq                                 24
% 3.69/0.96  fd_pure                                 0
% 3.69/0.96  fd_pseudo                               0
% 3.69/0.96  fd_cond                                 0
% 3.69/0.96  fd_pseudo_cond                          3
% 3.69/0.96  AC symbols                              0
% 3.69/0.96  
% 3.69/0.96  ------ Schedule dynamic 5 is on 
% 3.69/0.96  
% 3.69/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.69/0.96  
% 3.69/0.96  
% 3.69/0.96  ------ 
% 3.69/0.96  Current options:
% 3.69/0.96  ------ 
% 3.69/0.96  
% 3.69/0.96  ------ Input Options
% 3.69/0.96  
% 3.69/0.96  --out_options                           all
% 3.69/0.96  --tptp_safe_out                         true
% 3.69/0.96  --problem_path                          ""
% 3.69/0.96  --include_path                          ""
% 3.69/0.96  --clausifier                            res/vclausify_rel
% 3.69/0.96  --clausifier_options                    --mode clausify
% 3.69/0.96  --stdin                                 false
% 3.69/0.96  --stats_out                             all
% 3.69/0.96  
% 3.69/0.96  ------ General Options
% 3.69/0.96  
% 3.69/0.96  --fof                                   false
% 3.69/0.96  --time_out_real                         305.
% 3.69/0.96  --time_out_virtual                      -1.
% 3.69/0.96  --symbol_type_check                     false
% 3.69/0.96  --clausify_out                          false
% 3.69/0.96  --sig_cnt_out                           false
% 3.69/0.96  --trig_cnt_out                          false
% 3.69/0.96  --trig_cnt_out_tolerance                1.
% 3.69/0.96  --trig_cnt_out_sk_spl                   false
% 3.69/0.96  --abstr_cl_out                          false
% 3.69/0.96  
% 3.69/0.96  ------ Global Options
% 3.69/0.96  
% 3.69/0.96  --schedule                              default
% 3.69/0.96  --add_important_lit                     false
% 3.69/0.96  --prop_solver_per_cl                    1000
% 3.69/0.96  --min_unsat_core                        false
% 3.69/0.96  --soft_assumptions                      false
% 3.69/0.96  --soft_lemma_size                       3
% 3.69/0.96  --prop_impl_unit_size                   0
% 3.69/0.96  --prop_impl_unit                        []
% 3.69/0.96  --share_sel_clauses                     true
% 3.69/0.96  --reset_solvers                         false
% 3.69/0.96  --bc_imp_inh                            [conj_cone]
% 3.69/0.96  --conj_cone_tolerance                   3.
% 3.69/0.96  --extra_neg_conj                        none
% 3.69/0.96  --large_theory_mode                     true
% 3.69/0.96  --prolific_symb_bound                   200
% 3.69/0.96  --lt_threshold                          2000
% 3.69/0.96  --clause_weak_htbl                      true
% 3.69/0.96  --gc_record_bc_elim                     false
% 3.69/0.96  
% 3.69/0.96  ------ Preprocessing Options
% 3.69/0.96  
% 3.69/0.96  --preprocessing_flag                    true
% 3.69/0.96  --time_out_prep_mult                    0.1
% 3.69/0.96  --splitting_mode                        input
% 3.69/0.96  --splitting_grd                         true
% 3.69/0.96  --splitting_cvd                         false
% 3.69/0.96  --splitting_cvd_svl                     false
% 3.69/0.96  --splitting_nvd                         32
% 3.69/0.96  --sub_typing                            true
% 3.69/0.96  --prep_gs_sim                           true
% 3.69/0.96  --prep_unflatten                        true
% 3.69/0.96  --prep_res_sim                          true
% 3.69/0.96  --prep_upred                            true
% 3.69/0.96  --prep_sem_filter                       exhaustive
% 3.69/0.96  --prep_sem_filter_out                   false
% 3.69/0.96  --pred_elim                             true
% 3.69/0.96  --res_sim_input                         true
% 3.69/0.96  --eq_ax_congr_red                       true
% 3.69/0.96  --pure_diseq_elim                       true
% 3.69/0.96  --brand_transform                       false
% 3.69/0.96  --non_eq_to_eq                          false
% 3.69/0.96  --prep_def_merge                        true
% 3.69/0.96  --prep_def_merge_prop_impl              false
% 3.69/0.96  --prep_def_merge_mbd                    true
% 3.69/0.96  --prep_def_merge_tr_red                 false
% 3.69/0.96  --prep_def_merge_tr_cl                  false
% 3.69/0.96  --smt_preprocessing                     true
% 3.69/0.96  --smt_ac_axioms                         fast
% 3.69/0.96  --preprocessed_out                      false
% 3.69/0.96  --preprocessed_stats                    false
% 3.69/0.96  
% 3.69/0.96  ------ Abstraction refinement Options
% 3.69/0.96  
% 3.69/0.96  --abstr_ref                             []
% 3.69/0.96  --abstr_ref_prep                        false
% 3.69/0.96  --abstr_ref_until_sat                   false
% 3.69/0.96  --abstr_ref_sig_restrict                funpre
% 3.69/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 3.69/0.96  --abstr_ref_under                       []
% 3.69/0.96  
% 3.69/0.96  ------ SAT Options
% 3.69/0.96  
% 3.69/0.96  --sat_mode                              false
% 3.69/0.96  --sat_fm_restart_options                ""
% 3.69/0.96  --sat_gr_def                            false
% 3.69/0.96  --sat_epr_types                         true
% 3.69/0.96  --sat_non_cyclic_types                  false
% 3.69/0.96  --sat_finite_models                     false
% 3.69/0.96  --sat_fm_lemmas                         false
% 3.69/0.96  --sat_fm_prep                           false
% 3.69/0.96  --sat_fm_uc_incr                        true
% 3.69/0.96  --sat_out_model                         small
% 3.69/0.96  --sat_out_clauses                       false
% 3.69/0.96  
% 3.69/0.96  ------ QBF Options
% 3.69/0.96  
% 3.69/0.96  --qbf_mode                              false
% 3.69/0.96  --qbf_elim_univ                         false
% 3.69/0.96  --qbf_dom_inst                          none
% 3.69/0.96  --qbf_dom_pre_inst                      false
% 3.69/0.96  --qbf_sk_in                             false
% 3.69/0.96  --qbf_pred_elim                         true
% 3.69/0.96  --qbf_split                             512
% 3.69/0.96  
% 3.69/0.96  ------ BMC1 Options
% 3.69/0.96  
% 3.69/0.96  --bmc1_incremental                      false
% 3.69/0.96  --bmc1_axioms                           reachable_all
% 3.69/0.96  --bmc1_min_bound                        0
% 3.69/0.96  --bmc1_max_bound                        -1
% 3.69/0.96  --bmc1_max_bound_default                -1
% 3.69/0.96  --bmc1_symbol_reachability              true
% 3.69/0.96  --bmc1_property_lemmas                  false
% 3.69/0.96  --bmc1_k_induction                      false
% 3.69/0.96  --bmc1_non_equiv_states                 false
% 3.69/0.96  --bmc1_deadlock                         false
% 3.69/0.96  --bmc1_ucm                              false
% 3.69/0.96  --bmc1_add_unsat_core                   none
% 3.69/0.96  --bmc1_unsat_core_children              false
% 3.69/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 3.69/0.96  --bmc1_out_stat                         full
% 3.69/0.96  --bmc1_ground_init                      false
% 3.69/0.96  --bmc1_pre_inst_next_state              false
% 3.69/0.96  --bmc1_pre_inst_state                   false
% 3.69/0.96  --bmc1_pre_inst_reach_state             false
% 3.69/0.96  --bmc1_out_unsat_core                   false
% 3.69/0.96  --bmc1_aig_witness_out                  false
% 3.69/0.96  --bmc1_verbose                          false
% 3.69/0.96  --bmc1_dump_clauses_tptp                false
% 3.69/0.96  --bmc1_dump_unsat_core_tptp             false
% 3.69/0.96  --bmc1_dump_file                        -
% 3.69/0.96  --bmc1_ucm_expand_uc_limit              128
% 3.69/0.96  --bmc1_ucm_n_expand_iterations          6
% 3.69/0.96  --bmc1_ucm_extend_mode                  1
% 3.69/0.96  --bmc1_ucm_init_mode                    2
% 3.69/0.96  --bmc1_ucm_cone_mode                    none
% 3.69/0.96  --bmc1_ucm_reduced_relation_type        0
% 3.69/0.96  --bmc1_ucm_relax_model                  4
% 3.69/0.96  --bmc1_ucm_full_tr_after_sat            true
% 3.69/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 3.69/0.96  --bmc1_ucm_layered_model                none
% 3.69/0.96  --bmc1_ucm_max_lemma_size               10
% 3.69/0.96  
% 3.69/0.96  ------ AIG Options
% 3.69/0.96  
% 3.69/0.96  --aig_mode                              false
% 3.69/0.96  
% 3.69/0.96  ------ Instantiation Options
% 3.69/0.96  
% 3.69/0.96  --instantiation_flag                    true
% 3.69/0.96  --inst_sos_flag                         false
% 3.69/0.96  --inst_sos_phase                        true
% 3.69/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.69/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.69/0.96  --inst_lit_sel_side                     none
% 3.69/0.96  --inst_solver_per_active                1400
% 3.69/0.96  --inst_solver_calls_frac                1.
% 3.69/0.96  --inst_passive_queue_type               priority_queues
% 3.69/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.69/0.96  --inst_passive_queues_freq              [25;2]
% 3.69/0.96  --inst_dismatching                      true
% 3.69/0.96  --inst_eager_unprocessed_to_passive     true
% 3.69/0.96  --inst_prop_sim_given                   true
% 3.69/0.96  --inst_prop_sim_new                     false
% 3.69/0.96  --inst_subs_new                         false
% 3.69/0.96  --inst_eq_res_simp                      false
% 3.69/0.96  --inst_subs_given                       false
% 3.69/0.96  --inst_orphan_elimination               true
% 3.69/0.96  --inst_learning_loop_flag               true
% 3.69/0.96  --inst_learning_start                   3000
% 3.69/0.96  --inst_learning_factor                  2
% 3.69/0.96  --inst_start_prop_sim_after_learn       3
% 3.69/0.96  --inst_sel_renew                        solver
% 3.69/0.96  --inst_lit_activity_flag                true
% 3.69/0.96  --inst_restr_to_given                   false
% 3.69/0.96  --inst_activity_threshold               500
% 3.69/0.96  --inst_out_proof                        true
% 3.69/0.96  
% 3.69/0.96  ------ Resolution Options
% 3.69/0.96  
% 3.69/0.96  --resolution_flag                       false
% 3.69/0.96  --res_lit_sel                           adaptive
% 3.69/0.96  --res_lit_sel_side                      none
% 3.69/0.96  --res_ordering                          kbo
% 3.69/0.96  --res_to_prop_solver                    active
% 3.69/0.96  --res_prop_simpl_new                    false
% 3.69/0.96  --res_prop_simpl_given                  true
% 3.69/0.96  --res_passive_queue_type                priority_queues
% 3.69/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.69/0.96  --res_passive_queues_freq               [15;5]
% 3.69/0.96  --res_forward_subs                      full
% 3.69/0.96  --res_backward_subs                     full
% 3.69/0.96  --res_forward_subs_resolution           true
% 3.69/0.96  --res_backward_subs_resolution          true
% 3.69/0.96  --res_orphan_elimination                true
% 3.69/0.96  --res_time_limit                        2.
% 3.69/0.96  --res_out_proof                         true
% 3.69/0.96  
% 3.69/0.96  ------ Superposition Options
% 3.69/0.96  
% 3.69/0.96  --superposition_flag                    true
% 3.69/0.96  --sup_passive_queue_type                priority_queues
% 3.69/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.69/0.96  --sup_passive_queues_freq               [8;1;4]
% 3.69/0.96  --demod_completeness_check              fast
% 3.69/0.96  --demod_use_ground                      true
% 3.69/0.96  --sup_to_prop_solver                    passive
% 3.69/0.96  --sup_prop_simpl_new                    true
% 3.69/0.96  --sup_prop_simpl_given                  true
% 3.69/0.96  --sup_fun_splitting                     false
% 3.69/0.96  --sup_smt_interval                      50000
% 3.69/0.96  
% 3.69/0.96  ------ Superposition Simplification Setup
% 3.69/0.96  
% 3.69/0.96  --sup_indices_passive                   []
% 3.69/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.69/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.69/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.69/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 3.69/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.69/0.96  --sup_full_bw                           [BwDemod]
% 3.69/0.96  --sup_immed_triv                        [TrivRules]
% 3.69/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.69/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.69/0.96  --sup_immed_bw_main                     []
% 3.69/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.69/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 3.69/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.69/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.69/0.96  
% 3.69/0.96  ------ Combination Options
% 3.69/0.96  
% 3.69/0.96  --comb_res_mult                         3
% 3.69/0.96  --comb_sup_mult                         2
% 3.69/0.96  --comb_inst_mult                        10
% 3.69/0.96  
% 3.69/0.96  ------ Debug Options
% 3.69/0.96  
% 3.69/0.96  --dbg_backtrace                         false
% 3.69/0.96  --dbg_dump_prop_clauses                 false
% 3.69/0.96  --dbg_dump_prop_clauses_file            -
% 3.69/0.96  --dbg_out_stat                          false
% 3.69/0.96  
% 3.69/0.96  
% 3.69/0.96  
% 3.69/0.96  
% 3.69/0.96  ------ Proving...
% 3.69/0.96  
% 3.69/0.96  
% 3.69/0.96  % SZS status Theorem for theBenchmark.p
% 3.69/0.96  
% 3.69/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 3.69/0.96  
% 3.69/0.96  fof(f15,conjecture,(
% 3.69/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))))))),
% 3.69/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.96  
% 3.69/0.96  fof(f16,negated_conjecture,(
% 3.69/0.96    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))))))),
% 3.69/0.96    inference(negated_conjecture,[],[f15])).
% 3.69/0.96  
% 3.69/0.96  fof(f42,plain,(
% 3.69/0.96    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1)))) & m1_pre_topc(X1,X0)) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.69/0.96    inference(ennf_transformation,[],[f16])).
% 3.69/0.96  
% 3.69/0.96  fof(f43,plain,(
% 3.69/0.96    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.69/0.96    inference(flattening,[],[f42])).
% 3.69/0.96  
% 3.69/0.96  fof(f59,plain,(
% 3.69/0.96    ? [X0] : (? [X1] : ((((~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) & ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.69/0.96    inference(nnf_transformation,[],[f43])).
% 3.69/0.96  
% 3.69/0.96  fof(f60,plain,(
% 3.69/0.96    ? [X0] : (? [X1] : ((~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.69/0.96    inference(flattening,[],[f59])).
% 3.69/0.96  
% 3.69/0.96  fof(f62,plain,(
% 3.69/0.96    ( ! [X0] : (? [X1] : ((~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0)) => ((~m1_subset_1(k9_tmap_1(X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,sK4))))) | ~v5_pre_topc(k9_tmap_1(X0,sK4),X0,k8_tmap_1(X0,sK4)) | ~v1_funct_2(k9_tmap_1(X0,sK4),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,sK4))) | ~v1_funct_1(k9_tmap_1(X0,sK4)) | ~m1_pre_topc(sK4,X0) | ~v1_tsep_1(sK4,X0)) & ((m1_subset_1(k9_tmap_1(X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,sK4))))) & v5_pre_topc(k9_tmap_1(X0,sK4),X0,k8_tmap_1(X0,sK4)) & v1_funct_2(k9_tmap_1(X0,sK4),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,sK4))) & v1_funct_1(k9_tmap_1(X0,sK4))) | (m1_pre_topc(sK4,X0) & v1_tsep_1(sK4,X0))) & m1_pre_topc(sK4,X0))) )),
% 3.69/0.96    introduced(choice_axiom,[])).
% 3.69/0.96  
% 3.69/0.96  fof(f61,plain,(
% 3.69/0.96    ? [X0] : (? [X1] : ((~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~m1_subset_1(k9_tmap_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X1))))) | ~v5_pre_topc(k9_tmap_1(sK3,X1),sK3,k8_tmap_1(sK3,X1)) | ~v1_funct_2(k9_tmap_1(sK3,X1),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X1))) | ~v1_funct_1(k9_tmap_1(sK3,X1)) | ~m1_pre_topc(X1,sK3) | ~v1_tsep_1(X1,sK3)) & ((m1_subset_1(k9_tmap_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X1))))) & v5_pre_topc(k9_tmap_1(sK3,X1),sK3,k8_tmap_1(sK3,X1)) & v1_funct_2(k9_tmap_1(sK3,X1),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X1))) & v1_funct_1(k9_tmap_1(sK3,X1))) | (m1_pre_topc(X1,sK3) & v1_tsep_1(X1,sK3))) & m1_pre_topc(X1,sK3)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 3.69/0.96    introduced(choice_axiom,[])).
% 3.69/0.96  
% 3.69/0.96  fof(f63,plain,(
% 3.69/0.96    ((~m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) | ~v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4)) | ~v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) | ~v1_funct_1(k9_tmap_1(sK3,sK4)) | ~m1_pre_topc(sK4,sK3) | ~v1_tsep_1(sK4,sK3)) & ((m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) & v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4)) & v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) & v1_funct_1(k9_tmap_1(sK3,sK4))) | (m1_pre_topc(sK4,sK3) & v1_tsep_1(sK4,sK3))) & m1_pre_topc(sK4,sK3)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 3.69/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f60,f62,f61])).
% 3.69/0.96  
% 3.69/0.96  fof(f102,plain,(
% 3.69/0.96    m1_pre_topc(sK4,sK3)),
% 3.69/0.96    inference(cnf_transformation,[],[f63])).
% 3.69/0.96  
% 3.69/0.96  fof(f5,axiom,(
% 3.69/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & v1_pre_topc(X2)) => (k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => k6_tmap_1(X0,X3) = X2))))))),
% 3.69/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.96  
% 3.69/0.96  fof(f24,plain,(
% 3.69/0.96    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : ((k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.69/0.96    inference(ennf_transformation,[],[f5])).
% 3.69/0.96  
% 3.69/0.96  fof(f25,plain,(
% 3.69/0.96    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.69/0.96    inference(flattening,[],[f24])).
% 3.69/0.96  
% 3.69/0.96  fof(f45,plain,(
% 3.69/0.96    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.69/0.96    inference(nnf_transformation,[],[f25])).
% 3.69/0.96  
% 3.69/0.96  fof(f46,plain,(
% 3.69/0.96    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.69/0.96    inference(rectify,[],[f45])).
% 3.69/0.96  
% 3.69/0.96  fof(f47,plain,(
% 3.69/0.96    ! [X2,X1,X0] : (? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (k6_tmap_1(X0,sK0(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK0(X0,X1,X2) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.69/0.96    introduced(choice_axiom,[])).
% 3.69/0.96  
% 3.69/0.96  fof(f48,plain,(
% 3.69/0.96    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | (k6_tmap_1(X0,sK0(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK0(X0,X1,X2) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.69/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f46,f47])).
% 3.69/0.96  
% 3.69/0.96  fof(f69,plain,(
% 3.69/0.96    ( ! [X4,X2,X0,X1] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.69/0.96    inference(cnf_transformation,[],[f48])).
% 3.69/0.96  
% 3.69/0.96  fof(f113,plain,(
% 3.69/0.96    ( ! [X2,X0,X1] : (k6_tmap_1(X0,u1_struct_0(X1)) = X2 | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.69/0.96    inference(equality_resolution,[],[f69])).
% 3.69/0.96  
% 3.69/0.96  fof(f114,plain,(
% 3.69/0.96    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.69/0.96    inference(equality_resolution,[],[f113])).
% 3.69/0.96  
% 3.69/0.96  fof(f13,axiom,(
% 3.69/0.96    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.69/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.96  
% 3.69/0.96  fof(f40,plain,(
% 3.69/0.96    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.69/0.96    inference(ennf_transformation,[],[f13])).
% 3.69/0.96  
% 3.69/0.96  fof(f97,plain,(
% 3.69/0.96    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.69/0.96    inference(cnf_transformation,[],[f40])).
% 3.69/0.96  
% 3.69/0.96  fof(f9,axiom,(
% 3.69/0.96    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 3.69/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.96  
% 3.69/0.96  fof(f32,plain,(
% 3.69/0.96    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.69/0.97    inference(ennf_transformation,[],[f9])).
% 3.69/0.97  
% 3.69/0.97  fof(f33,plain,(
% 3.69/0.97    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.69/0.97    inference(flattening,[],[f32])).
% 3.69/0.97  
% 3.69/0.97  fof(f84,plain,(
% 3.69/0.97    ( ! [X0,X1] : (v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.69/0.97    inference(cnf_transformation,[],[f33])).
% 3.69/0.97  
% 3.69/0.97  fof(f85,plain,(
% 3.69/0.97    ( ! [X0,X1] : (v2_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.69/0.97    inference(cnf_transformation,[],[f33])).
% 3.69/0.97  
% 3.69/0.97  fof(f86,plain,(
% 3.69/0.97    ( ! [X0,X1] : (l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.69/0.97    inference(cnf_transformation,[],[f33])).
% 3.69/0.97  
% 3.69/0.97  fof(f99,plain,(
% 3.69/0.97    ~v2_struct_0(sK3)),
% 3.69/0.97    inference(cnf_transformation,[],[f63])).
% 3.69/0.97  
% 3.69/0.97  fof(f100,plain,(
% 3.69/0.97    v2_pre_topc(sK3)),
% 3.69/0.97    inference(cnf_transformation,[],[f63])).
% 3.69/0.97  
% 3.69/0.97  fof(f101,plain,(
% 3.69/0.97    l1_pre_topc(sK3)),
% 3.69/0.97    inference(cnf_transformation,[],[f63])).
% 3.69/0.97  
% 3.69/0.97  fof(f3,axiom,(
% 3.69/0.97    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 3.69/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.97  
% 3.69/0.97  fof(f20,plain,(
% 3.69/0.97    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 3.69/0.97    inference(ennf_transformation,[],[f3])).
% 3.69/0.97  
% 3.69/0.97  fof(f21,plain,(
% 3.69/0.97    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 3.69/0.97    inference(flattening,[],[f20])).
% 3.69/0.97  
% 3.69/0.97  fof(f44,plain,(
% 3.69/0.97    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 3.69/0.97    inference(nnf_transformation,[],[f21])).
% 3.69/0.97  
% 3.69/0.97  fof(f66,plain,(
% 3.69/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 3.69/0.97    inference(cnf_transformation,[],[f44])).
% 3.69/0.97  
% 3.69/0.97  fof(f10,axiom,(
% 3.69/0.97    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))))),
% 3.69/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.97  
% 3.69/0.97  fof(f34,plain,(
% 3.69/0.97    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.69/0.97    inference(ennf_transformation,[],[f10])).
% 3.69/0.97  
% 3.69/0.97  fof(f35,plain,(
% 3.69/0.97    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.69/0.97    inference(flattening,[],[f34])).
% 3.69/0.97  
% 3.69/0.97  fof(f89,plain,(
% 3.69/0.97    ( ! [X0,X1] : (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.69/0.97    inference(cnf_transformation,[],[f35])).
% 3.69/0.97  
% 3.69/0.97  fof(f87,plain,(
% 3.69/0.97    ( ! [X0,X1] : (v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.69/0.97    inference(cnf_transformation,[],[f35])).
% 3.69/0.97  
% 3.69/0.97  fof(f6,axiom,(
% 3.69/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(X2)) => (k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))))))))),
% 3.69/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.97  
% 3.69/0.97  fof(f26,plain,(
% 3.69/0.97    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : ((r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.69/0.97    inference(ennf_transformation,[],[f6])).
% 3.69/0.97  
% 3.69/0.97  fof(f27,plain,(
% 3.69/0.97    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.69/0.97    inference(flattening,[],[f26])).
% 3.69/0.97  
% 3.69/0.97  fof(f49,plain,(
% 3.69/0.97    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | ? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.69/0.97    inference(nnf_transformation,[],[f27])).
% 3.69/0.97  
% 3.69/0.97  fof(f50,plain,(
% 3.69/0.97    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | ? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.69/0.97    inference(rectify,[],[f49])).
% 3.69/0.97  
% 3.69/0.97  fof(f51,plain,(
% 3.69/0.97    ! [X2,X1,X0] : (? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2))) & u1_struct_0(X1) = sK1(X0,X1,X2) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.69/0.97    introduced(choice_axiom,[])).
% 3.69/0.97  
% 3.69/0.97  fof(f52,plain,(
% 3.69/0.97    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2))) & u1_struct_0(X1) = sK1(X0,X1,X2) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.69/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f50,f51])).
% 3.69/0.97  
% 3.69/0.97  fof(f73,plain,(
% 3.69/0.97    ( ! [X4,X2,X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k9_tmap_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.69/0.97    inference(cnf_transformation,[],[f52])).
% 3.69/0.97  
% 3.69/0.97  fof(f115,plain,(
% 3.69/0.97    ( ! [X2,X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),X2,k7_tmap_1(X0,u1_struct_0(X1))) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k9_tmap_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.69/0.97    inference(equality_resolution,[],[f73])).
% 3.69/0.97  
% 3.69/0.97  fof(f116,plain,(
% 3.69/0.97    ( ! [X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1))) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.69/0.97    inference(equality_resolution,[],[f115])).
% 3.69/0.97  
% 3.69/0.97  fof(f88,plain,(
% 3.69/0.97    ( ! [X0,X1] : (v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.69/0.97    inference(cnf_transformation,[],[f35])).
% 3.69/0.97  
% 3.69/0.97  fof(f8,axiom,(
% 3.69/0.97    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 3.69/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.97  
% 3.69/0.97  fof(f30,plain,(
% 3.69/0.97    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.69/0.97    inference(ennf_transformation,[],[f8])).
% 3.69/0.97  
% 3.69/0.97  fof(f31,plain,(
% 3.69/0.97    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.69/0.97    inference(flattening,[],[f30])).
% 3.69/0.97  
% 3.69/0.97  fof(f83,plain,(
% 3.69/0.97    ( ! [X0,X1] : (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.69/0.97    inference(cnf_transformation,[],[f31])).
% 3.69/0.97  
% 3.69/0.97  fof(f82,plain,(
% 3.69/0.97    ( ! [X0,X1] : (v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.69/0.97    inference(cnf_transformation,[],[f31])).
% 3.69/0.97  
% 3.69/0.97  fof(f81,plain,(
% 3.69/0.97    ( ! [X0,X1] : (v1_funct_1(k7_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.69/0.97    inference(cnf_transformation,[],[f31])).
% 3.69/0.97  
% 3.69/0.97  fof(f11,axiom,(
% 3.69/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 3.69/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.97  
% 3.69/0.97  fof(f36,plain,(
% 3.69/0.97    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.69/0.97    inference(ennf_transformation,[],[f11])).
% 3.69/0.97  
% 3.69/0.97  fof(f37,plain,(
% 3.69/0.97    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.69/0.97    inference(flattening,[],[f36])).
% 3.69/0.97  
% 3.69/0.97  fof(f90,plain,(
% 3.69/0.97    ( ! [X0,X1] : (u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.69/0.97    inference(cnf_transformation,[],[f37])).
% 3.69/0.97  
% 3.69/0.97  fof(f4,axiom,(
% 3.69/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))))),
% 3.69/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.97  
% 3.69/0.97  fof(f22,plain,(
% 3.69/0.97    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.69/0.97    inference(ennf_transformation,[],[f4])).
% 3.69/0.97  
% 3.69/0.97  fof(f23,plain,(
% 3.69/0.97    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.69/0.97    inference(flattening,[],[f22])).
% 3.69/0.97  
% 3.69/0.97  fof(f68,plain,(
% 3.69/0.97    ( ! [X0,X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.69/0.97    inference(cnf_transformation,[],[f23])).
% 3.69/0.97  
% 3.69/0.97  fof(f12,axiom,(
% 3.69/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))))),
% 3.69/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.97  
% 3.69/0.97  fof(f38,plain,(
% 3.69/0.97    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.69/0.97    inference(ennf_transformation,[],[f12])).
% 3.69/0.97  
% 3.69/0.97  fof(f39,plain,(
% 3.69/0.97    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.69/0.97    inference(flattening,[],[f38])).
% 3.69/0.97  
% 3.69/0.97  fof(f57,plain,(
% 3.69/0.97    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | (~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1)))) & ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.69/0.97    inference(nnf_transformation,[],[f39])).
% 3.69/0.97  
% 3.69/0.97  fof(f58,plain,(
% 3.69/0.97    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1))) & ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.69/0.97    inference(flattening,[],[f57])).
% 3.69/0.97  
% 3.69/0.97  fof(f96,plain,(
% 3.69/0.97    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.69/0.97    inference(cnf_transformation,[],[f58])).
% 3.69/0.97  
% 3.69/0.97  fof(f107,plain,(
% 3.69/0.97    v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4)) | v1_tsep_1(sK4,sK3)),
% 3.69/0.97    inference(cnf_transformation,[],[f63])).
% 3.69/0.97  
% 3.69/0.97  fof(f94,plain,(
% 3.69/0.97    ( ! [X0,X1] : (v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.69/0.97    inference(cnf_transformation,[],[f58])).
% 3.69/0.97  
% 3.69/0.97  fof(f111,plain,(
% 3.69/0.97    ~m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) | ~v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4)) | ~v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) | ~v1_funct_1(k9_tmap_1(sK3,sK4)) | ~m1_pre_topc(sK4,sK3) | ~v1_tsep_1(sK4,sK3)),
% 3.69/0.97    inference(cnf_transformation,[],[f63])).
% 3.69/0.97  
% 3.69/0.97  fof(f7,axiom,(
% 3.69/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tsep_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v3_pre_topc(X2,X0))))))),
% 3.69/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.97  
% 3.69/0.97  fof(f28,plain,(
% 3.69/0.97    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.69/0.97    inference(ennf_transformation,[],[f7])).
% 3.69/0.97  
% 3.69/0.97  fof(f29,plain,(
% 3.69/0.97    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.69/0.97    inference(flattening,[],[f28])).
% 3.69/0.97  
% 3.69/0.97  fof(f53,plain,(
% 3.69/0.97    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.69/0.97    inference(nnf_transformation,[],[f29])).
% 3.69/0.97  
% 3.69/0.97  fof(f54,plain,(
% 3.69/0.97    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.69/0.97    inference(rectify,[],[f53])).
% 3.69/0.97  
% 3.69/0.97  fof(f55,plain,(
% 3.69/0.97    ! [X1,X0] : (? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK2(X0,X1),X0) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.69/0.97    introduced(choice_axiom,[])).
% 3.69/0.97  
% 3.69/0.97  fof(f56,plain,(
% 3.69/0.97    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | (~v3_pre_topc(sK2(X0,X1),X0) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.69/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f54,f55])).
% 3.69/0.97  
% 3.69/0.97  fof(f77,plain,(
% 3.69/0.97    ( ! [X0,X3,X1] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.69/0.97    inference(cnf_transformation,[],[f56])).
% 3.69/0.97  
% 3.69/0.97  fof(f117,plain,(
% 3.69/0.97    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.69/0.97    inference(equality_resolution,[],[f77])).
% 3.69/0.97  
% 3.69/0.97  fof(f80,plain,(
% 3.69/0.97    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(sK2(X0,X1),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.69/0.97    inference(cnf_transformation,[],[f56])).
% 3.69/0.97  
% 3.69/0.97  fof(f79,plain,(
% 3.69/0.97    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | u1_struct_0(X1) = sK2(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.69/0.97    inference(cnf_transformation,[],[f56])).
% 3.69/0.97  
% 3.69/0.97  fof(f1,axiom,(
% 3.69/0.97    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.69/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.97  
% 3.69/0.97  fof(f17,plain,(
% 3.69/0.97    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.69/0.97    inference(ennf_transformation,[],[f1])).
% 3.69/0.97  
% 3.69/0.97  fof(f64,plain,(
% 3.69/0.97    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.69/0.97    inference(cnf_transformation,[],[f17])).
% 3.69/0.97  
% 3.69/0.97  fof(f2,axiom,(
% 3.69/0.97    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.69/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.97  
% 3.69/0.97  fof(f18,plain,(
% 3.69/0.97    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.69/0.97    inference(ennf_transformation,[],[f2])).
% 3.69/0.97  
% 3.69/0.97  fof(f19,plain,(
% 3.69/0.97    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.69/0.97    inference(flattening,[],[f18])).
% 3.69/0.97  
% 3.69/0.97  fof(f65,plain,(
% 3.69/0.97    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.69/0.97    inference(cnf_transformation,[],[f19])).
% 3.69/0.97  
% 3.69/0.97  cnf(c_44,negated_conjecture,
% 3.69/0.97      ( m1_pre_topc(sK4,sK3) ),
% 3.69/0.97      inference(cnf_transformation,[],[f102]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_4689,negated_conjecture,
% 3.69/0.97      ( m1_pre_topc(sK4,sK3) ),
% 3.69/0.97      inference(subtyping,[status(esa)],[c_44]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_5398,plain,
% 3.69/0.97      ( m1_pre_topc(sK4,sK3) = iProver_top ),
% 3.69/0.97      inference(predicate_to_equality,[status(thm)],[c_4689]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_8,plain,
% 3.69/0.97      ( ~ m1_pre_topc(X0,X1)
% 3.69/0.97      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/0.97      | ~ v1_pre_topc(k8_tmap_1(X1,X0))
% 3.69/0.97      | ~ v2_pre_topc(X1)
% 3.69/0.97      | ~ v2_pre_topc(k8_tmap_1(X1,X0))
% 3.69/0.97      | v2_struct_0(X1)
% 3.69/0.97      | ~ l1_pre_topc(X1)
% 3.69/0.97      | ~ l1_pre_topc(k8_tmap_1(X1,X0))
% 3.69/0.97      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 3.69/0.97      inference(cnf_transformation,[],[f114]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_33,plain,
% 3.69/0.97      ( ~ m1_pre_topc(X0,X1)
% 3.69/0.97      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/0.97      | ~ l1_pre_topc(X1) ),
% 3.69/0.97      inference(cnf_transformation,[],[f97]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_22,plain,
% 3.69/0.97      ( ~ m1_pre_topc(X0,X1)
% 3.69/0.97      | v1_pre_topc(k8_tmap_1(X1,X0))
% 3.69/0.97      | ~ v2_pre_topc(X1)
% 3.69/0.97      | v2_struct_0(X1)
% 3.69/0.97      | ~ l1_pre_topc(X1) ),
% 3.69/0.97      inference(cnf_transformation,[],[f84]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_21,plain,
% 3.69/0.97      ( ~ m1_pre_topc(X0,X1)
% 3.69/0.97      | ~ v2_pre_topc(X1)
% 3.69/0.97      | v2_pre_topc(k8_tmap_1(X1,X0))
% 3.69/0.97      | v2_struct_0(X1)
% 3.69/0.97      | ~ l1_pre_topc(X1) ),
% 3.69/0.97      inference(cnf_transformation,[],[f85]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_20,plain,
% 3.69/0.97      ( ~ m1_pre_topc(X0,X1)
% 3.69/0.97      | ~ v2_pre_topc(X1)
% 3.69/0.97      | v2_struct_0(X1)
% 3.69/0.97      | ~ l1_pre_topc(X1)
% 3.69/0.97      | l1_pre_topc(k8_tmap_1(X1,X0)) ),
% 3.69/0.97      inference(cnf_transformation,[],[f86]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_352,plain,
% 3.69/0.97      ( ~ l1_pre_topc(X1)
% 3.69/0.97      | v2_struct_0(X1)
% 3.69/0.97      | ~ m1_pre_topc(X0,X1)
% 3.69/0.97      | ~ v2_pre_topc(X1)
% 3.69/0.97      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 3.69/0.97      inference(global_propositional_subsumption,
% 3.69/0.97                [status(thm)],
% 3.69/0.97                [c_8,c_33,c_22,c_21,c_20]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_353,plain,
% 3.69/0.97      ( ~ m1_pre_topc(X0,X1)
% 3.69/0.97      | ~ v2_pre_topc(X1)
% 3.69/0.97      | v2_struct_0(X1)
% 3.69/0.97      | ~ l1_pre_topc(X1)
% 3.69/0.97      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 3.69/0.97      inference(renaming,[status(thm)],[c_352]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_47,negated_conjecture,
% 3.69/0.97      ( ~ v2_struct_0(sK3) ),
% 3.69/0.97      inference(cnf_transformation,[],[f99]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_1544,plain,
% 3.69/0.97      ( ~ m1_pre_topc(X0,X1)
% 3.69/0.97      | ~ v2_pre_topc(X1)
% 3.69/0.97      | ~ l1_pre_topc(X1)
% 3.69/0.97      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0)
% 3.69/0.97      | sK3 != X1 ),
% 3.69/0.97      inference(resolution_lifted,[status(thm)],[c_353,c_47]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_1545,plain,
% 3.69/0.97      ( ~ m1_pre_topc(X0,sK3)
% 3.69/0.97      | ~ v2_pre_topc(sK3)
% 3.69/0.97      | ~ l1_pre_topc(sK3)
% 3.69/0.97      | k6_tmap_1(sK3,u1_struct_0(X0)) = k8_tmap_1(sK3,X0) ),
% 3.69/0.97      inference(unflattening,[status(thm)],[c_1544]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_46,negated_conjecture,
% 3.69/0.97      ( v2_pre_topc(sK3) ),
% 3.69/0.97      inference(cnf_transformation,[],[f100]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_45,negated_conjecture,
% 3.69/0.97      ( l1_pre_topc(sK3) ),
% 3.69/0.97      inference(cnf_transformation,[],[f101]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_1549,plain,
% 3.69/0.97      ( ~ m1_pre_topc(X0,sK3)
% 3.69/0.97      | k6_tmap_1(sK3,u1_struct_0(X0)) = k8_tmap_1(sK3,X0) ),
% 3.69/0.97      inference(global_propositional_subsumption,
% 3.69/0.97                [status(thm)],
% 3.69/0.97                [c_1545,c_46,c_45]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_4682,plain,
% 3.69/0.97      ( ~ m1_pre_topc(X0_58,sK3)
% 3.69/0.97      | k6_tmap_1(sK3,u1_struct_0(X0_58)) = k8_tmap_1(sK3,X0_58) ),
% 3.69/0.97      inference(subtyping,[status(esa)],[c_1549]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_5406,plain,
% 3.69/0.97      ( k6_tmap_1(sK3,u1_struct_0(X0_58)) = k8_tmap_1(sK3,X0_58)
% 3.69/0.97      | m1_pre_topc(X0_58,sK3) != iProver_top ),
% 3.69/0.97      inference(predicate_to_equality,[status(thm)],[c_4682]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_5953,plain,
% 3.69/0.97      ( k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4) ),
% 3.69/0.97      inference(superposition,[status(thm)],[c_5398,c_5406]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_3,plain,
% 3.69/0.97      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
% 3.69/0.97      | ~ v1_funct_2(X5,X2,X3)
% 3.69/0.97      | ~ v1_funct_2(X4,X0,X1)
% 3.69/0.97      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.69/0.97      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.69/0.97      | ~ v1_funct_1(X5)
% 3.69/0.97      | ~ v1_funct_1(X4)
% 3.69/0.97      | v1_xboole_0(X1)
% 3.69/0.97      | v1_xboole_0(X3)
% 3.69/0.97      | X4 = X5 ),
% 3.69/0.97      inference(cnf_transformation,[],[f66]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_2255,plain,
% 3.69/0.97      ( ~ m1_pre_topc(X0,X1)
% 3.69/0.97      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/0.97      | sK3 != X1 ),
% 3.69/0.97      inference(resolution_lifted,[status(thm)],[c_33,c_45]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_2256,plain,
% 3.69/0.97      ( ~ m1_pre_topc(X0,sK3)
% 3.69/0.97      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.69/0.97      inference(unflattening,[status(thm)],[c_2255]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_23,plain,
% 3.69/0.97      ( ~ m1_pre_topc(X0,X1)
% 3.69/0.97      | m1_subset_1(k9_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X0)))))
% 3.69/0.97      | ~ v2_pre_topc(X1)
% 3.69/0.97      | v2_struct_0(X1)
% 3.69/0.97      | ~ l1_pre_topc(X1) ),
% 3.69/0.97      inference(cnf_transformation,[],[f89]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_1620,plain,
% 3.69/0.97      ( ~ m1_pre_topc(X0,X1)
% 3.69/0.97      | m1_subset_1(k9_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X0)))))
% 3.69/0.97      | ~ v2_pre_topc(X1)
% 3.69/0.97      | ~ l1_pre_topc(X1)
% 3.69/0.97      | sK3 != X1 ),
% 3.69/0.97      inference(resolution_lifted,[status(thm)],[c_23,c_47]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_1621,plain,
% 3.69/0.97      ( ~ m1_pre_topc(X0,sK3)
% 3.69/0.97      | m1_subset_1(k9_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X0)))))
% 3.69/0.97      | ~ v2_pre_topc(sK3)
% 3.69/0.97      | ~ l1_pre_topc(sK3) ),
% 3.69/0.97      inference(unflattening,[status(thm)],[c_1620]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_1625,plain,
% 3.69/0.97      ( ~ m1_pre_topc(X0,sK3)
% 3.69/0.97      | m1_subset_1(k9_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X0))))) ),
% 3.69/0.97      inference(global_propositional_subsumption,
% 3.69/0.97                [status(thm)],
% 3.69/0.97                [c_1621,c_46,c_45]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_25,plain,
% 3.69/0.97      ( ~ m1_pre_topc(X0,X1)
% 3.69/0.97      | ~ v2_pre_topc(X1)
% 3.69/0.97      | v1_funct_1(k9_tmap_1(X1,X0))
% 3.69/0.97      | v2_struct_0(X1)
% 3.69/0.97      | ~ l1_pre_topc(X1) ),
% 3.69/0.97      inference(cnf_transformation,[],[f87]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_1598,plain,
% 3.69/0.97      ( ~ m1_pre_topc(X0,X1)
% 3.69/0.97      | ~ v2_pre_topc(X1)
% 3.69/0.97      | v1_funct_1(k9_tmap_1(X1,X0))
% 3.69/0.97      | ~ l1_pre_topc(X1)
% 3.69/0.97      | sK3 != X1 ),
% 3.69/0.97      inference(resolution_lifted,[status(thm)],[c_25,c_47]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_1599,plain,
% 3.69/0.97      ( ~ m1_pre_topc(X0,sK3)
% 3.69/0.97      | ~ v2_pre_topc(sK3)
% 3.69/0.97      | v1_funct_1(k9_tmap_1(sK3,X0))
% 3.69/0.97      | ~ l1_pre_topc(sK3) ),
% 3.69/0.97      inference(unflattening,[status(thm)],[c_1598]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_1603,plain,
% 3.69/0.97      ( v1_funct_1(k9_tmap_1(sK3,X0)) | ~ m1_pre_topc(X0,sK3) ),
% 3.69/0.97      inference(global_propositional_subsumption,
% 3.69/0.97                [status(thm)],
% 3.69/0.97                [c_1599,c_46,c_45]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_1604,plain,
% 3.69/0.97      ( ~ m1_pre_topc(X0,sK3) | v1_funct_1(k9_tmap_1(sK3,X0)) ),
% 3.69/0.97      inference(renaming,[status(thm)],[c_1603]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_12,plain,
% 3.69/0.97      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
% 3.69/0.97      | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 3.69/0.97      | ~ m1_pre_topc(X1,X0)
% 3.69/0.97      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 3.69/0.97      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
% 3.69/0.97      | ~ v2_pre_topc(X0)
% 3.69/0.97      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 3.69/0.97      | v2_struct_0(X0)
% 3.69/0.97      | ~ l1_pre_topc(X0) ),
% 3.69/0.97      inference(cnf_transformation,[],[f116]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_24,plain,
% 3.69/0.97      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 3.69/0.97      | ~ m1_pre_topc(X1,X0)
% 3.69/0.97      | ~ v2_pre_topc(X0)
% 3.69/0.97      | v2_struct_0(X0)
% 3.69/0.97      | ~ l1_pre_topc(X0) ),
% 3.69/0.97      inference(cnf_transformation,[],[f88]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_342,plain,
% 3.69/0.97      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
% 3.69/0.97      | ~ m1_pre_topc(X1,X0)
% 3.69/0.97      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 3.69/0.97      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
% 3.69/0.97      | ~ v2_pre_topc(X0)
% 3.69/0.97      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 3.69/0.97      | v2_struct_0(X0)
% 3.69/0.97      | ~ l1_pre_topc(X0) ),
% 3.69/0.97      inference(global_propositional_subsumption,
% 3.69/0.97                [status(thm)],
% 3.69/0.97                [c_12,c_24]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_1451,plain,
% 3.69/0.97      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
% 3.69/0.97      | ~ m1_pre_topc(X1,X0)
% 3.69/0.97      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 3.69/0.97      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
% 3.69/0.97      | ~ v2_pre_topc(X0)
% 3.69/0.97      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 3.69/0.97      | ~ l1_pre_topc(X0)
% 3.69/0.97      | sK3 != X0 ),
% 3.69/0.97      inference(resolution_lifted,[status(thm)],[c_342,c_47]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_1452,plain,
% 3.69/0.97      ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X0)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0))),k9_tmap_1(sK3,X0),k7_tmap_1(sK3,u1_struct_0(X0)))
% 3.69/0.97      | ~ m1_pre_topc(X0,sK3)
% 3.69/0.97      | ~ m1_subset_1(k9_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X0)))))
% 3.69/0.97      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.69/0.97      | ~ v2_pre_topc(sK3)
% 3.69/0.97      | ~ v1_funct_1(k9_tmap_1(sK3,X0))
% 3.69/0.97      | ~ l1_pre_topc(sK3) ),
% 3.69/0.97      inference(unflattening,[status(thm)],[c_1451]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_1456,plain,
% 3.69/0.97      ( ~ v1_funct_1(k9_tmap_1(sK3,X0))
% 3.69/0.97      | r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X0)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0))),k9_tmap_1(sK3,X0),k7_tmap_1(sK3,u1_struct_0(X0)))
% 3.69/0.97      | ~ m1_pre_topc(X0,sK3)
% 3.69/0.97      | ~ m1_subset_1(k9_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X0)))))
% 3.69/0.97      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.69/0.97      inference(global_propositional_subsumption,
% 3.69/0.97                [status(thm)],
% 3.69/0.97                [c_1452,c_46,c_45]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_1457,plain,
% 3.69/0.97      ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X0)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0))),k9_tmap_1(sK3,X0),k7_tmap_1(sK3,u1_struct_0(X0)))
% 3.69/0.97      | ~ m1_pre_topc(X0,sK3)
% 3.69/0.97      | ~ m1_subset_1(k9_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X0)))))
% 3.69/0.97      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.69/0.97      | ~ v1_funct_1(k9_tmap_1(sK3,X0)) ),
% 3.69/0.97      inference(renaming,[status(thm)],[c_1456]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_1615,plain,
% 3.69/0.97      ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X0)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0))),k9_tmap_1(sK3,X0),k7_tmap_1(sK3,u1_struct_0(X0)))
% 3.69/0.97      | ~ m1_pre_topc(X0,sK3)
% 3.69/0.97      | ~ m1_subset_1(k9_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X0)))))
% 3.69/0.97      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.69/0.97      inference(backward_subsumption_resolution,
% 3.69/0.97                [status(thm)],
% 3.69/0.97                [c_1604,c_1457]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_1637,plain,
% 3.69/0.97      ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X0)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0))),k9_tmap_1(sK3,X0),k7_tmap_1(sK3,u1_struct_0(X0)))
% 3.69/0.97      | ~ m1_pre_topc(X0,sK3)
% 3.69/0.97      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.69/0.97      inference(backward_subsumption_resolution,
% 3.69/0.97                [status(thm)],
% 3.69/0.97                [c_1625,c_1615]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_2381,plain,
% 3.69/0.97      ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X0)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0))),k9_tmap_1(sK3,X0),k7_tmap_1(sK3,u1_struct_0(X0)))
% 3.69/0.97      | ~ m1_pre_topc(X0,sK3) ),
% 3.69/0.97      inference(backward_subsumption_resolution,
% 3.69/0.97                [status(thm)],
% 3.69/0.97                [c_2256,c_1637]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_2444,plain,
% 3.69/0.97      ( ~ v1_funct_2(X0,X1,X2)
% 3.69/0.97      | ~ v1_funct_2(X3,X4,X5)
% 3.69/0.97      | ~ m1_pre_topc(X6,sK3)
% 3.69/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.69/0.97      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.69/0.97      | ~ v1_funct_1(X0)
% 3.69/0.97      | ~ v1_funct_1(X3)
% 3.69/0.97      | v1_xboole_0(X2)
% 3.69/0.97      | v1_xboole_0(X5)
% 3.69/0.97      | X3 = X0
% 3.69/0.97      | k9_tmap_1(sK3,X6) != X0
% 3.69/0.97      | k7_tmap_1(sK3,u1_struct_0(X6)) != X3
% 3.69/0.97      | u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X6))) != X5
% 3.69/0.97      | u1_struct_0(k8_tmap_1(sK3,X6)) != X2
% 3.69/0.97      | u1_struct_0(sK3) != X4
% 3.69/0.97      | u1_struct_0(sK3) != X1 ),
% 3.69/0.97      inference(resolution_lifted,[status(thm)],[c_3,c_2381]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_2445,plain,
% 3.69/0.97      ( ~ v1_funct_2(k9_tmap_1(sK3,X0),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X0)))
% 3.69/0.97      | ~ v1_funct_2(k7_tmap_1(sK3,u1_struct_0(X0)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0))))
% 3.69/0.97      | ~ m1_pre_topc(X0,sK3)
% 3.69/0.97      | ~ m1_subset_1(k9_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X0)))))
% 3.69/0.97      | ~ m1_subset_1(k7_tmap_1(sK3,u1_struct_0(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0))))))
% 3.69/0.97      | ~ v1_funct_1(k9_tmap_1(sK3,X0))
% 3.69/0.97      | ~ v1_funct_1(k7_tmap_1(sK3,u1_struct_0(X0)))
% 3.69/0.97      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0))))
% 3.69/0.97      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,X0)))
% 3.69/0.97      | k7_tmap_1(sK3,u1_struct_0(X0)) = k9_tmap_1(sK3,X0) ),
% 3.69/0.97      inference(unflattening,[status(thm)],[c_2444]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_1478,plain,
% 3.69/0.97      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 3.69/0.97      | ~ m1_pre_topc(X1,X0)
% 3.69/0.97      | ~ v2_pre_topc(X0)
% 3.69/0.97      | ~ l1_pre_topc(X0)
% 3.69/0.97      | sK3 != X0 ),
% 3.69/0.97      inference(resolution_lifted,[status(thm)],[c_24,c_47]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_1479,plain,
% 3.69/0.97      ( v1_funct_2(k9_tmap_1(sK3,X0),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X0)))
% 3.69/0.97      | ~ m1_pre_topc(X0,sK3)
% 3.69/0.97      | ~ v2_pre_topc(sK3)
% 3.69/0.97      | ~ l1_pre_topc(sK3) ),
% 3.69/0.97      inference(unflattening,[status(thm)],[c_1478]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_1483,plain,
% 3.69/0.97      ( v1_funct_2(k9_tmap_1(sK3,X0),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X0)))
% 3.69/0.97      | ~ m1_pre_topc(X0,sK3) ),
% 3.69/0.97      inference(global_propositional_subsumption,
% 3.69/0.97                [status(thm)],
% 3.69/0.97                [c_1479,c_46,c_45]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_2449,plain,
% 3.69/0.97      ( ~ m1_subset_1(k7_tmap_1(sK3,u1_struct_0(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0))))))
% 3.69/0.97      | ~ v1_funct_2(k7_tmap_1(sK3,u1_struct_0(X0)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0))))
% 3.69/0.97      | ~ m1_pre_topc(X0,sK3)
% 3.69/0.97      | ~ v1_funct_1(k7_tmap_1(sK3,u1_struct_0(X0)))
% 3.69/0.97      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0))))
% 3.69/0.97      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,X0)))
% 3.69/0.97      | k7_tmap_1(sK3,u1_struct_0(X0)) = k9_tmap_1(sK3,X0) ),
% 3.69/0.97      inference(global_propositional_subsumption,
% 3.69/0.97                [status(thm)],
% 3.69/0.97                [c_2445,c_46,c_45,c_1479,c_1599,c_1621]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_2450,plain,
% 3.69/0.97      ( ~ v1_funct_2(k7_tmap_1(sK3,u1_struct_0(X0)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0))))
% 3.69/0.97      | ~ m1_pre_topc(X0,sK3)
% 3.69/0.97      | ~ m1_subset_1(k7_tmap_1(sK3,u1_struct_0(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0))))))
% 3.69/0.97      | ~ v1_funct_1(k7_tmap_1(sK3,u1_struct_0(X0)))
% 3.69/0.97      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0))))
% 3.69/0.97      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,X0)))
% 3.69/0.97      | k7_tmap_1(sK3,u1_struct_0(X0)) = k9_tmap_1(sK3,X0) ),
% 3.69/0.97      inference(renaming,[status(thm)],[c_2449]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_4666,plain,
% 3.69/0.97      ( ~ v1_funct_2(k7_tmap_1(sK3,u1_struct_0(X0_58)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0_58))))
% 3.69/0.97      | ~ m1_pre_topc(X0_58,sK3)
% 3.69/0.97      | ~ m1_subset_1(k7_tmap_1(sK3,u1_struct_0(X0_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0_58))))))
% 3.69/0.97      | ~ v1_funct_1(k7_tmap_1(sK3,u1_struct_0(X0_58)))
% 3.69/0.97      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0_58))))
% 3.69/0.97      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,X0_58)))
% 3.69/0.97      | k7_tmap_1(sK3,u1_struct_0(X0_58)) = k9_tmap_1(sK3,X0_58) ),
% 3.69/0.97      inference(subtyping,[status(esa)],[c_2450]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_5422,plain,
% 3.69/0.97      ( k7_tmap_1(sK3,u1_struct_0(X0_58)) = k9_tmap_1(sK3,X0_58)
% 3.69/0.97      | v1_funct_2(k7_tmap_1(sK3,u1_struct_0(X0_58)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0_58)))) != iProver_top
% 3.69/0.97      | m1_pre_topc(X0_58,sK3) != iProver_top
% 3.69/0.97      | m1_subset_1(k7_tmap_1(sK3,u1_struct_0(X0_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0_58)))))) != iProver_top
% 3.69/0.97      | v1_funct_1(k7_tmap_1(sK3,u1_struct_0(X0_58))) != iProver_top
% 3.69/0.97      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0_58)))) = iProver_top
% 3.69/0.97      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,X0_58))) = iProver_top ),
% 3.69/0.97      inference(predicate_to_equality,[status(thm)],[c_4666]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_50,plain,
% 3.69/0.97      ( l1_pre_topc(sK3) = iProver_top ),
% 3.69/0.97      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_4775,plain,
% 3.69/0.97      ( k6_tmap_1(sK3,u1_struct_0(X0_58)) = k8_tmap_1(sK3,X0_58)
% 3.69/0.97      | m1_pre_topc(X0_58,sK3) != iProver_top ),
% 3.69/0.97      inference(predicate_to_equality,[status(thm)],[c_4682]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_4817,plain,
% 3.69/0.97      ( k7_tmap_1(sK3,u1_struct_0(X0_58)) = k9_tmap_1(sK3,X0_58)
% 3.69/0.97      | v1_funct_2(k7_tmap_1(sK3,u1_struct_0(X0_58)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0_58)))) != iProver_top
% 3.69/0.97      | m1_pre_topc(X0_58,sK3) != iProver_top
% 3.69/0.97      | m1_subset_1(k7_tmap_1(sK3,u1_struct_0(X0_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0_58)))))) != iProver_top
% 3.69/0.97      | v1_funct_1(k7_tmap_1(sK3,u1_struct_0(X0_58))) != iProver_top
% 3.69/0.97      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0_58)))) = iProver_top
% 3.69/0.97      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,X0_58))) = iProver_top ),
% 3.69/0.97      inference(predicate_to_equality,[status(thm)],[c_4666]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_4694,plain,
% 3.69/0.97      ( ~ m1_pre_topc(X0_58,X1_58)
% 3.69/0.97      | m1_subset_1(u1_struct_0(X0_58),k1_zfmisc_1(u1_struct_0(X1_58)))
% 3.69/0.97      | ~ l1_pre_topc(X1_58) ),
% 3.69/0.97      inference(subtyping,[status(esa)],[c_33]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_5766,plain,
% 3.69/0.97      ( ~ m1_pre_topc(X0_58,sK3)
% 3.69/0.97      | m1_subset_1(u1_struct_0(X0_58),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.69/0.97      | ~ l1_pre_topc(sK3) ),
% 3.69/0.97      inference(instantiation,[status(thm)],[c_4694]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_5772,plain,
% 3.69/0.97      ( m1_pre_topc(X0_58,sK3) != iProver_top
% 3.69/0.97      | m1_subset_1(u1_struct_0(X0_58),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 3.69/0.97      | l1_pre_topc(sK3) != iProver_top ),
% 3.69/0.97      inference(predicate_to_equality,[status(thm)],[c_5766]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_17,plain,
% 3.69/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/0.97      | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
% 3.69/0.97      | ~ v2_pre_topc(X1)
% 3.69/0.97      | v2_struct_0(X1)
% 3.69/0.97      | ~ l1_pre_topc(X1) ),
% 3.69/0.97      inference(cnf_transformation,[],[f83]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_1714,plain,
% 3.69/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/0.97      | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
% 3.69/0.97      | ~ v2_pre_topc(X1)
% 3.69/0.97      | ~ l1_pre_topc(X1)
% 3.69/0.97      | sK3 != X1 ),
% 3.69/0.97      inference(resolution_lifted,[status(thm)],[c_17,c_47]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_1715,plain,
% 3.69/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.69/0.97      | m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))))
% 3.69/0.97      | ~ v2_pre_topc(sK3)
% 3.69/0.97      | ~ l1_pre_topc(sK3) ),
% 3.69/0.97      inference(unflattening,[status(thm)],[c_1714]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_1719,plain,
% 3.69/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.69/0.97      | m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0))))) ),
% 3.69/0.97      inference(global_propositional_subsumption,
% 3.69/0.97                [status(thm)],
% 3.69/0.97                [c_1715,c_46,c_45]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_4675,plain,
% 3.69/0.97      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.69/0.97      | m1_subset_1(k7_tmap_1(sK3,X0_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0_57))))) ),
% 3.69/0.97      inference(subtyping,[status(esa)],[c_1719]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_5768,plain,
% 3.69/0.97      ( m1_subset_1(k7_tmap_1(sK3,u1_struct_0(X0_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0_58))))))
% 3.69/0.97      | ~ m1_subset_1(u1_struct_0(X0_58),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.69/0.97      inference(instantiation,[status(thm)],[c_4675]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_5786,plain,
% 3.69/0.97      ( m1_subset_1(k7_tmap_1(sK3,u1_struct_0(X0_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0_58)))))) = iProver_top
% 3.69/0.97      | m1_subset_1(u1_struct_0(X0_58),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 3.69/0.97      inference(predicate_to_equality,[status(thm)],[c_5768]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_18,plain,
% 3.69/0.97      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
% 3.69/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.69/0.97      | ~ v2_pre_topc(X0)
% 3.69/0.97      | v2_struct_0(X0)
% 3.69/0.97      | ~ l1_pre_topc(X0) ),
% 3.69/0.97      inference(cnf_transformation,[],[f82]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_1496,plain,
% 3.69/0.97      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
% 3.69/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.69/0.97      | ~ v2_pre_topc(X0)
% 3.69/0.97      | ~ l1_pre_topc(X0)
% 3.69/0.97      | sK3 != X0 ),
% 3.69/0.97      inference(resolution_lifted,[status(thm)],[c_18,c_47]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_1497,plain,
% 3.69/0.97      ( v1_funct_2(k7_tmap_1(sK3,X0),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))
% 3.69/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.69/0.97      | ~ v2_pre_topc(sK3)
% 3.69/0.97      | ~ l1_pre_topc(sK3) ),
% 3.69/0.97      inference(unflattening,[status(thm)],[c_1496]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_1501,plain,
% 3.69/0.97      ( v1_funct_2(k7_tmap_1(sK3,X0),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))
% 3.69/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.69/0.97      inference(global_propositional_subsumption,
% 3.69/0.97                [status(thm)],
% 3.69/0.97                [c_1497,c_46,c_45]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_4683,plain,
% 3.69/0.97      ( v1_funct_2(k7_tmap_1(sK3,X0_57),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0_57)))
% 3.69/0.97      | ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.69/0.97      inference(subtyping,[status(esa)],[c_1501]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_5767,plain,
% 3.69/0.97      ( v1_funct_2(k7_tmap_1(sK3,u1_struct_0(X0_58)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0_58))))
% 3.69/0.97      | ~ m1_subset_1(u1_struct_0(X0_58),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.69/0.97      inference(instantiation,[status(thm)],[c_4683]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_5790,plain,
% 3.69/0.97      ( v1_funct_2(k7_tmap_1(sK3,u1_struct_0(X0_58)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0_58)))) = iProver_top
% 3.69/0.97      | m1_subset_1(u1_struct_0(X0_58),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 3.69/0.97      inference(predicate_to_equality,[status(thm)],[c_5767]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_5393,plain,
% 3.69/0.97      ( m1_pre_topc(X0_58,X1_58) != iProver_top
% 3.69/0.97      | m1_subset_1(u1_struct_0(X0_58),k1_zfmisc_1(u1_struct_0(X1_58))) = iProver_top
% 3.69/0.97      | l1_pre_topc(X1_58) != iProver_top ),
% 3.69/0.97      inference(predicate_to_equality,[status(thm)],[c_4694]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_19,plain,
% 3.69/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/0.97      | ~ v2_pre_topc(X1)
% 3.69/0.97      | v1_funct_1(k7_tmap_1(X1,X0))
% 3.69/0.97      | v2_struct_0(X1)
% 3.69/0.97      | ~ l1_pre_topc(X1) ),
% 3.69/0.97      inference(cnf_transformation,[],[f81]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_1696,plain,
% 3.69/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/0.97      | ~ v2_pre_topc(X1)
% 3.69/0.97      | v1_funct_1(k7_tmap_1(X1,X0))
% 3.69/0.97      | ~ l1_pre_topc(X1)
% 3.69/0.97      | sK3 != X1 ),
% 3.69/0.97      inference(resolution_lifted,[status(thm)],[c_19,c_47]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_1697,plain,
% 3.69/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.69/0.97      | ~ v2_pre_topc(sK3)
% 3.69/0.97      | v1_funct_1(k7_tmap_1(sK3,X0))
% 3.69/0.97      | ~ l1_pre_topc(sK3) ),
% 3.69/0.97      inference(unflattening,[status(thm)],[c_1696]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_1701,plain,
% 3.69/0.97      ( v1_funct_1(k7_tmap_1(sK3,X0))
% 3.69/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.69/0.97      inference(global_propositional_subsumption,
% 3.69/0.97                [status(thm)],
% 3.69/0.97                [c_1697,c_46,c_45]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_1702,plain,
% 3.69/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.69/0.97      | v1_funct_1(k7_tmap_1(sK3,X0)) ),
% 3.69/0.97      inference(renaming,[status(thm)],[c_1701]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_4676,plain,
% 3.69/0.97      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.69/0.97      | v1_funct_1(k7_tmap_1(sK3,X0_57)) ),
% 3.69/0.97      inference(subtyping,[status(esa)],[c_1702]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_5412,plain,
% 3.69/0.97      ( m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.69/0.97      | v1_funct_1(k7_tmap_1(sK3,X0_57)) = iProver_top ),
% 3.69/0.97      inference(predicate_to_equality,[status(thm)],[c_4676]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_5998,plain,
% 3.69/0.97      ( m1_pre_topc(X0_58,sK3) != iProver_top
% 3.69/0.97      | v1_funct_1(k7_tmap_1(sK3,u1_struct_0(X0_58))) = iProver_top
% 3.69/0.97      | l1_pre_topc(sK3) != iProver_top ),
% 3.69/0.97      inference(superposition,[status(thm)],[c_5393,c_5412]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_4709,plain,
% 3.69/0.97      ( X0_58 != X1_58 | u1_struct_0(X0_58) = u1_struct_0(X1_58) ),
% 3.69/0.97      theory(equality) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_6079,plain,
% 3.69/0.97      ( X0_58 != k8_tmap_1(sK3,X1_58)
% 3.69/0.97      | u1_struct_0(X0_58) = u1_struct_0(k8_tmap_1(sK3,X1_58)) ),
% 3.69/0.97      inference(instantiation,[status(thm)],[c_4709]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_6332,plain,
% 3.69/0.97      ( k6_tmap_1(sK3,u1_struct_0(X0_58)) != k8_tmap_1(sK3,X0_58)
% 3.69/0.97      | u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0_58))) = u1_struct_0(k8_tmap_1(sK3,X0_58)) ),
% 3.69/0.97      inference(instantiation,[status(thm)],[c_6079]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_4710,plain,
% 3.69/0.97      ( ~ v1_xboole_0(X0_57) | v1_xboole_0(X1_57) | X1_57 != X0_57 ),
% 3.69/0.97      theory(equality) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_5962,plain,
% 3.69/0.97      ( v1_xboole_0(X0_57)
% 3.69/0.97      | ~ v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,X0_58)))
% 3.69/0.97      | X0_57 != u1_struct_0(k8_tmap_1(sK3,X0_58)) ),
% 3.69/0.97      inference(instantiation,[status(thm)],[c_4710]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_6078,plain,
% 3.69/0.97      ( v1_xboole_0(u1_struct_0(X0_58))
% 3.69/0.97      | ~ v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,X1_58)))
% 3.69/0.97      | u1_struct_0(X0_58) != u1_struct_0(k8_tmap_1(sK3,X1_58)) ),
% 3.69/0.97      inference(instantiation,[status(thm)],[c_5962]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_6408,plain,
% 3.69/0.97      ( v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0_58))))
% 3.69/0.97      | ~ v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,X0_58)))
% 3.69/0.97      | u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0_58))) != u1_struct_0(k8_tmap_1(sK3,X0_58)) ),
% 3.69/0.97      inference(instantiation,[status(thm)],[c_6078]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_6409,plain,
% 3.69/0.97      ( u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0_58))) != u1_struct_0(k8_tmap_1(sK3,X0_58))
% 3.69/0.97      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0_58)))) = iProver_top
% 3.69/0.97      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,X0_58))) != iProver_top ),
% 3.69/0.97      inference(predicate_to_equality,[status(thm)],[c_6408]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_11240,plain,
% 3.69/0.97      ( v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0_58)))) = iProver_top
% 3.69/0.97      | m1_pre_topc(X0_58,sK3) != iProver_top
% 3.69/0.97      | k7_tmap_1(sK3,u1_struct_0(X0_58)) = k9_tmap_1(sK3,X0_58) ),
% 3.69/0.97      inference(global_propositional_subsumption,
% 3.69/0.97                [status(thm)],
% 3.69/0.97                [c_5422,c_50,c_4775,c_4817,c_5772,c_5786,c_5790,c_5998,
% 3.69/0.97                 c_6332,c_6409]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_11241,plain,
% 3.69/0.97      ( k7_tmap_1(sK3,u1_struct_0(X0_58)) = k9_tmap_1(sK3,X0_58)
% 3.69/0.97      | m1_pre_topc(X0_58,sK3) != iProver_top
% 3.69/0.97      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0_58)))) = iProver_top ),
% 3.69/0.97      inference(renaming,[status(thm)],[c_11240]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_11250,plain,
% 3.69/0.97      ( k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4)
% 3.69/0.97      | m1_pre_topc(sK4,sK3) != iProver_top
% 3.69/0.97      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4))) = iProver_top ),
% 3.69/0.97      inference(superposition,[status(thm)],[c_5953,c_11241]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_27,plain,
% 3.69/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/0.97      | ~ v2_pre_topc(X1)
% 3.69/0.97      | v2_struct_0(X1)
% 3.69/0.97      | ~ l1_pre_topc(X1)
% 3.69/0.97      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
% 3.69/0.97      inference(cnf_transformation,[],[f90]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_1562,plain,
% 3.69/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/0.97      | ~ v2_pre_topc(X1)
% 3.69/0.97      | ~ l1_pre_topc(X1)
% 3.69/0.97      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1)
% 3.69/0.97      | sK3 != X1 ),
% 3.69/0.97      inference(resolution_lifted,[status(thm)],[c_27,c_47]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_1563,plain,
% 3.69/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.69/0.97      | ~ v2_pre_topc(sK3)
% 3.69/0.97      | ~ l1_pre_topc(sK3)
% 3.69/0.97      | u1_struct_0(k6_tmap_1(sK3,X0)) = u1_struct_0(sK3) ),
% 3.69/0.97      inference(unflattening,[status(thm)],[c_1562]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_1567,plain,
% 3.69/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.69/0.97      | u1_struct_0(k6_tmap_1(sK3,X0)) = u1_struct_0(sK3) ),
% 3.69/0.97      inference(global_propositional_subsumption,
% 3.69/0.97                [status(thm)],
% 3.69/0.97                [c_1563,c_46,c_45]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_4681,plain,
% 3.69/0.97      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.69/0.97      | u1_struct_0(k6_tmap_1(sK3,X0_57)) = u1_struct_0(sK3) ),
% 3.69/0.97      inference(subtyping,[status(esa)],[c_1567]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_5407,plain,
% 3.69/0.97      ( u1_struct_0(k6_tmap_1(sK3,X0_57)) = u1_struct_0(sK3)
% 3.69/0.97      | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 3.69/0.97      inference(predicate_to_equality,[status(thm)],[c_4681]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_6089,plain,
% 3.69/0.97      ( u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0_58))) = u1_struct_0(sK3)
% 3.69/0.97      | m1_pre_topc(X0_58,sK3) != iProver_top
% 3.69/0.97      | l1_pre_topc(sK3) != iProver_top ),
% 3.69/0.97      inference(superposition,[status(thm)],[c_5393,c_5407]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_6888,plain,
% 3.69/0.97      ( m1_pre_topc(X0_58,sK3) != iProver_top
% 3.69/0.97      | u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0_58))) = u1_struct_0(sK3) ),
% 3.69/0.97      inference(global_propositional_subsumption,
% 3.69/0.97                [status(thm)],
% 3.69/0.97                [c_6089,c_50]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_6889,plain,
% 3.69/0.97      ( u1_struct_0(k6_tmap_1(sK3,u1_struct_0(X0_58))) = u1_struct_0(sK3)
% 3.69/0.97      | m1_pre_topc(X0_58,sK3) != iProver_top ),
% 3.69/0.97      inference(renaming,[status(thm)],[c_6888]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_6896,plain,
% 3.69/0.97      ( u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))) = u1_struct_0(sK3) ),
% 3.69/0.97      inference(superposition,[status(thm)],[c_5398,c_6889]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_6904,plain,
% 3.69/0.97      ( u1_struct_0(k8_tmap_1(sK3,sK4)) = u1_struct_0(sK3) ),
% 3.69/0.97      inference(light_normalisation,[status(thm)],[c_6896,c_5953]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_4,plain,
% 3.69/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/0.97      | ~ v2_pre_topc(X1)
% 3.69/0.97      | v2_struct_0(X1)
% 3.69/0.97      | ~ l1_pre_topc(X1)
% 3.69/0.97      | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1)) ),
% 3.69/0.97      inference(cnf_transformation,[],[f68]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_1876,plain,
% 3.69/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/0.97      | ~ v2_pre_topc(X1)
% 3.69/0.97      | ~ l1_pre_topc(X1)
% 3.69/0.97      | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1))
% 3.69/0.97      | sK3 != X1 ),
% 3.69/0.97      inference(resolution_lifted,[status(thm)],[c_4,c_47]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_1877,plain,
% 3.69/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.69/0.97      | ~ v2_pre_topc(sK3)
% 3.69/0.97      | ~ l1_pre_topc(sK3)
% 3.69/0.97      | k7_tmap_1(sK3,X0) = k6_partfun1(u1_struct_0(sK3)) ),
% 3.69/0.97      inference(unflattening,[status(thm)],[c_1876]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_1881,plain,
% 3.69/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.69/0.97      | k7_tmap_1(sK3,X0) = k6_partfun1(u1_struct_0(sK3)) ),
% 3.69/0.97      inference(global_propositional_subsumption,
% 3.69/0.97                [status(thm)],
% 3.69/0.97                [c_1877,c_46,c_45]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_4672,plain,
% 3.69/0.97      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.69/0.97      | k7_tmap_1(sK3,X0_57) = k6_partfun1(u1_struct_0(sK3)) ),
% 3.69/0.97      inference(subtyping,[status(esa)],[c_1881]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_5416,plain,
% 3.69/0.97      ( k7_tmap_1(sK3,X0_57) = k6_partfun1(u1_struct_0(sK3))
% 3.69/0.97      | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 3.69/0.97      inference(predicate_to_equality,[status(thm)],[c_4672]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_6114,plain,
% 3.69/0.97      ( k7_tmap_1(sK3,u1_struct_0(X0_58)) = k6_partfun1(u1_struct_0(sK3))
% 3.69/0.97      | m1_pre_topc(X0_58,sK3) != iProver_top
% 3.69/0.97      | l1_pre_topc(sK3) != iProver_top ),
% 3.69/0.97      inference(superposition,[status(thm)],[c_5393,c_5416]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_7212,plain,
% 3.69/0.97      ( m1_pre_topc(X0_58,sK3) != iProver_top
% 3.69/0.97      | k7_tmap_1(sK3,u1_struct_0(X0_58)) = k6_partfun1(u1_struct_0(sK3)) ),
% 3.69/0.97      inference(global_propositional_subsumption,
% 3.69/0.97                [status(thm)],
% 3.69/0.97                [c_6114,c_50]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_7213,plain,
% 3.69/0.97      ( k7_tmap_1(sK3,u1_struct_0(X0_58)) = k6_partfun1(u1_struct_0(sK3))
% 3.69/0.97      | m1_pre_topc(X0_58,sK3) != iProver_top ),
% 3.69/0.97      inference(renaming,[status(thm)],[c_7212]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_7220,plain,
% 3.69/0.97      ( k7_tmap_1(sK3,u1_struct_0(sK4)) = k6_partfun1(u1_struct_0(sK3)) ),
% 3.69/0.97      inference(superposition,[status(thm)],[c_5398,c_7213]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_11272,plain,
% 3.69/0.97      ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
% 3.69/0.97      | m1_pre_topc(sK4,sK3) != iProver_top
% 3.69/0.97      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.69/0.97      inference(light_normalisation,
% 3.69/0.97                [status(thm)],
% 3.69/0.97                [c_11250,c_6904,c_7220]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_28,plain,
% 3.69/0.97      ( ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
% 3.69/0.97      | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
% 3.69/0.97      | v3_pre_topc(X1,X0)
% 3.69/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.69/0.97      | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
% 3.69/0.97      | ~ v2_pre_topc(X0)
% 3.69/0.97      | ~ v1_funct_1(k7_tmap_1(X0,X1))
% 3.69/0.97      | v2_struct_0(X0)
% 3.69/0.97      | ~ l1_pre_topc(X0) ),
% 3.69/0.97      inference(cnf_transformation,[],[f96]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_314,plain,
% 3.69/0.97      ( ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
% 3.69/0.97      | v3_pre_topc(X1,X0)
% 3.69/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.69/0.97      | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
% 3.69/0.97      | ~ v2_pre_topc(X0)
% 3.69/0.97      | ~ v1_funct_1(k7_tmap_1(X0,X1))
% 3.69/0.97      | v2_struct_0(X0)
% 3.69/0.97      | ~ l1_pre_topc(X0) ),
% 3.69/0.97      inference(global_propositional_subsumption,
% 3.69/0.97                [status(thm)],
% 3.69/0.97                [c_28,c_18]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_39,negated_conjecture,
% 3.69/0.97      ( v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4))
% 3.69/0.97      | v1_tsep_1(sK4,sK3) ),
% 3.69/0.97      inference(cnf_transformation,[],[f107]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_617,plain,
% 3.69/0.97      ( v3_pre_topc(X0,X1)
% 3.69/0.97      | v1_tsep_1(sK4,sK3)
% 3.69/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/0.97      | ~ m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
% 3.69/0.97      | ~ v2_pre_topc(X1)
% 3.69/0.97      | ~ v1_funct_1(k7_tmap_1(X1,X0))
% 3.69/0.97      | v2_struct_0(X1)
% 3.69/0.97      | ~ l1_pre_topc(X1)
% 3.69/0.97      | k6_tmap_1(X1,X0) != k8_tmap_1(sK3,sK4)
% 3.69/0.97      | k7_tmap_1(X1,X0) != k9_tmap_1(sK3,sK4)
% 3.69/0.97      | sK3 != X1 ),
% 3.69/0.97      inference(resolution_lifted,[status(thm)],[c_314,c_39]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_618,plain,
% 3.69/0.97      ( v3_pre_topc(X0,sK3)
% 3.69/0.97      | v1_tsep_1(sK4,sK3)
% 3.69/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.69/0.97      | ~ m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))))
% 3.69/0.97      | ~ v2_pre_topc(sK3)
% 3.69/0.97      | ~ v1_funct_1(k7_tmap_1(sK3,X0))
% 3.69/0.97      | v2_struct_0(sK3)
% 3.69/0.97      | ~ l1_pre_topc(sK3)
% 3.69/0.97      | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
% 3.69/0.97      | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4) ),
% 3.69/0.97      inference(unflattening,[status(thm)],[c_617]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_622,plain,
% 3.69/0.97      ( ~ m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))))
% 3.69/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.69/0.97      | v1_tsep_1(sK4,sK3)
% 3.69/0.97      | v3_pre_topc(X0,sK3)
% 3.69/0.97      | ~ v1_funct_1(k7_tmap_1(sK3,X0))
% 3.69/0.97      | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
% 3.69/0.97      | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4) ),
% 3.69/0.97      inference(global_propositional_subsumption,
% 3.69/0.97                [status(thm)],
% 3.69/0.97                [c_618,c_47,c_46,c_45]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_623,plain,
% 3.69/0.97      ( v3_pre_topc(X0,sK3)
% 3.69/0.97      | v1_tsep_1(sK4,sK3)
% 3.69/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.69/0.97      | ~ m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))))
% 3.69/0.97      | ~ v1_funct_1(k7_tmap_1(sK3,X0))
% 3.69/0.97      | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
% 3.69/0.97      | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4) ),
% 3.69/0.97      inference(renaming,[status(thm)],[c_622]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_1939,plain,
% 3.69/0.97      ( v3_pre_topc(X0,sK3)
% 3.69/0.97      | v1_tsep_1(sK4,sK3)
% 3.69/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.69/0.97      | ~ m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))))
% 3.69/0.97      | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
% 3.69/0.97      | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4) ),
% 3.69/0.97      inference(backward_subsumption_resolution,
% 3.69/0.97                [status(thm)],
% 3.69/0.97                [c_1702,c_623]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_1946,plain,
% 3.69/0.97      ( v3_pre_topc(X0,sK3)
% 3.69/0.97      | v1_tsep_1(sK4,sK3)
% 3.69/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.69/0.97      | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
% 3.69/0.97      | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4) ),
% 3.69/0.97      inference(backward_subsumption_resolution,
% 3.69/0.97                [status(thm)],
% 3.69/0.97                [c_1719,c_1939]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_4671,plain,
% 3.69/0.97      ( v3_pre_topc(X0_57,sK3)
% 3.69/0.97      | v1_tsep_1(sK4,sK3)
% 3.69/0.97      | ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.69/0.97      | k6_tmap_1(sK3,X0_57) != k8_tmap_1(sK3,sK4)
% 3.69/0.97      | k7_tmap_1(sK3,X0_57) != k9_tmap_1(sK3,sK4) ),
% 3.69/0.97      inference(subtyping,[status(esa)],[c_1946]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_5417,plain,
% 3.69/0.97      ( k6_tmap_1(sK3,X0_57) != k8_tmap_1(sK3,sK4)
% 3.69/0.97      | k7_tmap_1(sK3,X0_57) != k9_tmap_1(sK3,sK4)
% 3.69/0.97      | v3_pre_topc(X0_57,sK3) = iProver_top
% 3.69/0.97      | v1_tsep_1(sK4,sK3) = iProver_top
% 3.69/0.97      | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 3.69/0.97      inference(predicate_to_equality,[status(thm)],[c_4671]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_7102,plain,
% 3.69/0.97      ( k7_tmap_1(sK3,u1_struct_0(sK4)) != k9_tmap_1(sK3,sK4)
% 3.69/0.97      | v3_pre_topc(u1_struct_0(sK4),sK3) = iProver_top
% 3.69/0.97      | v1_tsep_1(sK4,sK3) = iProver_top
% 3.69/0.97      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 3.69/0.97      inference(superposition,[status(thm)],[c_5953,c_5417]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_51,plain,
% 3.69/0.97      ( m1_pre_topc(sK4,sK3) = iProver_top ),
% 3.69/0.97      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_4702,plain,( X0_58 = X0_58 ),theory(equality) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_4750,plain,
% 3.69/0.97      ( sK3 = sK3 ),
% 3.69/0.97      inference(instantiation,[status(thm)],[c_4702]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_6145,plain,
% 3.69/0.97      ( ~ m1_pre_topc(sK4,sK3)
% 3.69/0.97      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.69/0.97      | ~ l1_pre_topc(sK3) ),
% 3.69/0.97      inference(instantiation,[status(thm)],[c_5766]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_6146,plain,
% 3.69/0.97      ( m1_pre_topc(sK4,sK3) != iProver_top
% 3.69/0.97      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 3.69/0.97      | l1_pre_topc(sK3) != iProver_top ),
% 3.69/0.97      inference(predicate_to_equality,[status(thm)],[c_6145]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_30,plain,
% 3.69/0.97      ( v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
% 3.69/0.97      | ~ v3_pre_topc(X1,X0)
% 3.69/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.69/0.97      | ~ v2_pre_topc(X0)
% 3.69/0.97      | v2_struct_0(X0)
% 3.69/0.97      | ~ l1_pre_topc(X0) ),
% 3.69/0.97      inference(cnf_transformation,[],[f94]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_35,negated_conjecture,
% 3.69/0.97      ( ~ v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4))
% 3.69/0.97      | ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 3.69/0.97      | ~ v1_tsep_1(sK4,sK3)
% 3.69/0.97      | ~ m1_pre_topc(sK4,sK3)
% 3.69/0.97      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 3.69/0.97      | ~ v1_funct_1(k9_tmap_1(sK3,sK4)) ),
% 3.69/0.97      inference(cnf_transformation,[],[f111]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_291,plain,
% 3.69/0.97      ( ~ v1_tsep_1(sK4,sK3)
% 3.69/0.97      | ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 3.69/0.97      | ~ v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4))
% 3.69/0.97      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 3.69/0.97      | ~ v1_funct_1(k9_tmap_1(sK3,sK4)) ),
% 3.69/0.97      inference(global_propositional_subsumption,
% 3.69/0.97                [status(thm)],
% 3.69/0.97                [c_35,c_44]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_292,negated_conjecture,
% 3.69/0.97      ( ~ v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4))
% 3.69/0.97      | ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 3.69/0.97      | ~ v1_tsep_1(sK4,sK3)
% 3.69/0.97      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 3.69/0.97      | ~ v1_funct_1(k9_tmap_1(sK3,sK4)) ),
% 3.69/0.97      inference(renaming,[status(thm)],[c_291]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_581,plain,
% 3.69/0.97      ( ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 3.69/0.97      | ~ v3_pre_topc(X0,X1)
% 3.69/0.97      | ~ v1_tsep_1(sK4,sK3)
% 3.69/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/0.97      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 3.69/0.97      | ~ v2_pre_topc(X1)
% 3.69/0.97      | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
% 3.69/0.97      | v2_struct_0(X1)
% 3.69/0.97      | ~ l1_pre_topc(X1)
% 3.69/0.97      | k6_tmap_1(X1,X0) != k8_tmap_1(sK3,sK4)
% 3.69/0.97      | k7_tmap_1(X1,X0) != k9_tmap_1(sK3,sK4)
% 3.69/0.97      | sK3 != X1 ),
% 3.69/0.97      inference(resolution_lifted,[status(thm)],[c_30,c_292]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_582,plain,
% 3.69/0.97      ( ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 3.69/0.97      | ~ v3_pre_topc(X0,sK3)
% 3.69/0.97      | ~ v1_tsep_1(sK4,sK3)
% 3.69/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.69/0.97      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 3.69/0.97      | ~ v2_pre_topc(sK3)
% 3.69/0.97      | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
% 3.69/0.97      | v2_struct_0(sK3)
% 3.69/0.97      | ~ l1_pre_topc(sK3)
% 3.69/0.97      | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
% 3.69/0.97      | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4) ),
% 3.69/0.97      inference(unflattening,[status(thm)],[c_581]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_586,plain,
% 3.69/0.97      ( ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 3.69/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.69/0.97      | ~ v1_tsep_1(sK4,sK3)
% 3.69/0.97      | ~ v3_pre_topc(X0,sK3)
% 3.69/0.97      | ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 3.69/0.97      | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
% 3.69/0.97      | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
% 3.69/0.97      | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4) ),
% 3.69/0.97      inference(global_propositional_subsumption,
% 3.69/0.97                [status(thm)],
% 3.69/0.97                [c_582,c_47,c_46,c_45]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_587,plain,
% 3.69/0.97      ( ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 3.69/0.97      | ~ v3_pre_topc(X0,sK3)
% 3.69/0.97      | ~ v1_tsep_1(sK4,sK3)
% 3.69/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.69/0.97      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 3.69/0.97      | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
% 3.69/0.97      | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
% 3.69/0.97      | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4) ),
% 3.69/0.97      inference(renaming,[status(thm)],[c_586]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_4686,plain,
% 3.69/0.97      ( ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 3.69/0.97      | ~ v3_pre_topc(X0_57,sK3)
% 3.69/0.97      | ~ v1_tsep_1(sK4,sK3)
% 3.69/0.97      | ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.69/0.97      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 3.69/0.97      | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
% 3.69/0.97      | k6_tmap_1(sK3,X0_57) != k8_tmap_1(sK3,sK4)
% 3.69/0.97      | k7_tmap_1(sK3,X0_57) != k9_tmap_1(sK3,sK4) ),
% 3.69/0.97      inference(subtyping,[status(esa)],[c_587]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_4698,plain,
% 3.69/0.97      ( ~ v3_pre_topc(X0_57,sK3)
% 3.69/0.97      | ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.69/0.97      | k6_tmap_1(sK3,X0_57) != k8_tmap_1(sK3,sK4)
% 3.69/0.97      | k7_tmap_1(sK3,X0_57) != k9_tmap_1(sK3,sK4)
% 3.69/0.97      | ~ sP0_iProver_split ),
% 3.69/0.97      inference(splitting,
% 3.69/0.97                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.69/0.97                [c_4686]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_5402,plain,
% 3.69/0.97      ( k6_tmap_1(sK3,X0_57) != k8_tmap_1(sK3,sK4)
% 3.69/0.97      | k7_tmap_1(sK3,X0_57) != k9_tmap_1(sK3,sK4)
% 3.69/0.97      | v3_pre_topc(X0_57,sK3) != iProver_top
% 3.69/0.97      | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.69/0.97      | sP0_iProver_split != iProver_top ),
% 3.69/0.97      inference(predicate_to_equality,[status(thm)],[c_4698]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_6651,plain,
% 3.69/0.97      ( k7_tmap_1(sK3,u1_struct_0(sK4)) != k9_tmap_1(sK3,sK4)
% 3.69/0.97      | v3_pre_topc(u1_struct_0(sK4),sK3) != iProver_top
% 3.69/0.97      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.69/0.97      | sP0_iProver_split != iProver_top ),
% 3.69/0.97      inference(superposition,[status(thm)],[c_5953,c_5402]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_5795,plain,
% 3.69/0.97      ( ~ v3_pre_topc(u1_struct_0(X0_58),sK3)
% 3.69/0.97      | ~ m1_subset_1(u1_struct_0(X0_58),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.69/0.97      | ~ sP0_iProver_split
% 3.69/0.97      | k6_tmap_1(sK3,u1_struct_0(X0_58)) != k8_tmap_1(sK3,sK4)
% 3.69/0.97      | k7_tmap_1(sK3,u1_struct_0(X0_58)) != k9_tmap_1(sK3,sK4) ),
% 3.69/0.97      inference(instantiation,[status(thm)],[c_4698]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_5911,plain,
% 3.69/0.97      ( ~ v3_pre_topc(u1_struct_0(sK4),sK3)
% 3.69/0.97      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.69/0.97      | ~ sP0_iProver_split
% 3.69/0.97      | k6_tmap_1(sK3,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4)
% 3.69/0.97      | k7_tmap_1(sK3,u1_struct_0(sK4)) != k9_tmap_1(sK3,sK4) ),
% 3.69/0.97      inference(instantiation,[status(thm)],[c_5795]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_5913,plain,
% 3.69/0.97      ( k6_tmap_1(sK3,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4)
% 3.69/0.97      | k7_tmap_1(sK3,u1_struct_0(sK4)) != k9_tmap_1(sK3,sK4)
% 3.69/0.97      | v3_pre_topc(u1_struct_0(sK4),sK3) != iProver_top
% 3.69/0.97      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.69/0.97      | sP0_iProver_split != iProver_top ),
% 3.69/0.97      inference(predicate_to_equality,[status(thm)],[c_5911]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_5912,plain,
% 3.69/0.97      ( ~ m1_pre_topc(sK4,sK3)
% 3.69/0.97      | k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4) ),
% 3.69/0.97      inference(instantiation,[status(thm)],[c_4682]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_16,plain,
% 3.69/0.97      ( v3_pre_topc(u1_struct_0(X0),X1)
% 3.69/0.97      | ~ v1_tsep_1(X0,X1)
% 3.69/0.97      | ~ m1_pre_topc(X0,X1)
% 3.69/0.97      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/0.97      | ~ l1_pre_topc(X1) ),
% 3.69/0.97      inference(cnf_transformation,[],[f117]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_332,plain,
% 3.69/0.97      ( ~ m1_pre_topc(X0,X1)
% 3.69/0.97      | ~ v1_tsep_1(X0,X1)
% 3.69/0.97      | v3_pre_topc(u1_struct_0(X0),X1)
% 3.69/0.97      | ~ l1_pre_topc(X1) ),
% 3.69/0.97      inference(global_propositional_subsumption,
% 3.69/0.97                [status(thm)],
% 3.69/0.97                [c_16,c_33]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_333,plain,
% 3.69/0.97      ( v3_pre_topc(u1_struct_0(X0),X1)
% 3.69/0.97      | ~ v1_tsep_1(X0,X1)
% 3.69/0.97      | ~ m1_pre_topc(X0,X1)
% 3.69/0.97      | ~ l1_pre_topc(X1) ),
% 3.69/0.97      inference(renaming,[status(thm)],[c_332]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_4687,plain,
% 3.69/0.97      ( v3_pre_topc(u1_struct_0(X0_58),X1_58)
% 3.69/0.97      | ~ v1_tsep_1(X0_58,X1_58)
% 3.69/0.97      | ~ m1_pre_topc(X0_58,X1_58)
% 3.69/0.97      | ~ l1_pre_topc(X1_58) ),
% 3.69/0.97      inference(subtyping,[status(esa)],[c_333]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_5794,plain,
% 3.69/0.97      ( v3_pre_topc(u1_struct_0(X0_58),sK3)
% 3.69/0.97      | ~ v1_tsep_1(X0_58,sK3)
% 3.69/0.97      | ~ m1_pre_topc(X0_58,sK3)
% 3.69/0.97      | ~ l1_pre_topc(sK3) ),
% 3.69/0.97      inference(instantiation,[status(thm)],[c_4687]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_5987,plain,
% 3.69/0.97      ( v3_pre_topc(u1_struct_0(sK4),sK3)
% 3.69/0.97      | ~ v1_tsep_1(sK4,sK3)
% 3.69/0.97      | ~ m1_pre_topc(sK4,sK3)
% 3.69/0.97      | ~ l1_pre_topc(sK3) ),
% 3.69/0.97      inference(instantiation,[status(thm)],[c_5794]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_5988,plain,
% 3.69/0.97      ( v3_pre_topc(u1_struct_0(sK4),sK3) = iProver_top
% 3.69/0.97      | v1_tsep_1(sK4,sK3) != iProver_top
% 3.69/0.97      | m1_pre_topc(sK4,sK3) != iProver_top
% 3.69/0.97      | l1_pre_topc(sK3) != iProver_top ),
% 3.69/0.97      inference(predicate_to_equality,[status(thm)],[c_5987]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_8306,plain,
% 3.69/0.97      ( k7_tmap_1(sK3,u1_struct_0(sK4)) != k9_tmap_1(sK3,sK4)
% 3.69/0.97      | sP0_iProver_split != iProver_top ),
% 3.69/0.97      inference(global_propositional_subsumption,
% 3.69/0.97                [status(thm)],
% 3.69/0.97                [c_6651,c_50,c_44,c_51,c_5913,c_5912,c_5988,c_6146,
% 3.69/0.97                 c_7102]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_13,plain,
% 3.69/0.97      ( ~ v3_pre_topc(sK2(X0,X1),X0)
% 3.69/0.97      | v1_tsep_1(X1,X0)
% 3.69/0.97      | ~ m1_pre_topc(X1,X0)
% 3.69/0.97      | ~ l1_pre_topc(X0) ),
% 3.69/0.97      inference(cnf_transformation,[],[f80]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_4697,plain,
% 3.69/0.97      ( ~ v3_pre_topc(sK2(X0_58,X1_58),X0_58)
% 3.69/0.97      | v1_tsep_1(X1_58,X0_58)
% 3.69/0.97      | ~ m1_pre_topc(X1_58,X0_58)
% 3.69/0.97      | ~ l1_pre_topc(X0_58) ),
% 3.69/0.97      inference(subtyping,[status(esa)],[c_13]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_8634,plain,
% 3.69/0.97      ( ~ v3_pre_topc(sK2(sK3,sK4),sK3)
% 3.69/0.97      | v1_tsep_1(sK4,sK3)
% 3.69/0.97      | ~ m1_pre_topc(sK4,sK3)
% 3.69/0.97      | ~ l1_pre_topc(sK3) ),
% 3.69/0.97      inference(instantiation,[status(thm)],[c_4697]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_8635,plain,
% 3.69/0.97      ( v3_pre_topc(sK2(sK3,sK4),sK3) != iProver_top
% 3.69/0.97      | v1_tsep_1(sK4,sK3) = iProver_top
% 3.69/0.97      | m1_pre_topc(sK4,sK3) != iProver_top
% 3.69/0.97      | l1_pre_topc(sK3) != iProver_top ),
% 3.69/0.97      inference(predicate_to_equality,[status(thm)],[c_8634]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_4679,plain,
% 3.69/0.97      ( ~ m1_pre_topc(X0_58,sK3) | v1_funct_1(k9_tmap_1(sK3,X0_58)) ),
% 3.69/0.97      inference(subtyping,[status(esa)],[c_1604]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_5409,plain,
% 3.69/0.97      ( m1_pre_topc(X0_58,sK3) != iProver_top
% 3.69/0.97      | v1_funct_1(k9_tmap_1(sK3,X0_58)) = iProver_top ),
% 3.69/0.97      inference(predicate_to_equality,[status(thm)],[c_4679]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_4678,plain,
% 3.69/0.97      ( ~ m1_pre_topc(X0_58,sK3)
% 3.69/0.97      | m1_subset_1(k9_tmap_1(sK3,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X0_58))))) ),
% 3.69/0.97      inference(subtyping,[status(esa)],[c_1625]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_5410,plain,
% 3.69/0.97      ( m1_pre_topc(X0_58,sK3) != iProver_top
% 3.69/0.97      | m1_subset_1(k9_tmap_1(sK3,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X0_58))))) = iProver_top ),
% 3.69/0.97      inference(predicate_to_equality,[status(thm)],[c_4678]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_4699,plain,
% 3.69/0.97      ( ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 3.69/0.97      | ~ v1_tsep_1(sK4,sK3)
% 3.69/0.97      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 3.69/0.97      | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
% 3.69/0.97      | sP0_iProver_split ),
% 3.69/0.97      inference(splitting,
% 3.69/0.97                [splitting(split),new_symbols(definition,[])],
% 3.69/0.97                [c_4686]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_5401,plain,
% 3.69/0.97      ( v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
% 3.69/0.97      | v1_tsep_1(sK4,sK3) != iProver_top
% 3.69/0.97      | m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) != iProver_top
% 3.69/0.97      | v1_funct_1(k9_tmap_1(sK3,sK4)) != iProver_top
% 3.69/0.97      | sP0_iProver_split = iProver_top ),
% 3.69/0.97      inference(predicate_to_equality,[status(thm)],[c_4699]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_6679,plain,
% 3.69/0.97      ( v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
% 3.69/0.97      | v1_tsep_1(sK4,sK3) != iProver_top
% 3.69/0.97      | m1_pre_topc(sK4,sK3) != iProver_top
% 3.69/0.97      | v1_funct_1(k9_tmap_1(sK3,sK4)) != iProver_top
% 3.69/0.97      | sP0_iProver_split = iProver_top ),
% 3.69/0.97      inference(superposition,[status(thm)],[c_5410,c_5401]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_6908,plain,
% 3.69/0.97      ( v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
% 3.69/0.97      | v1_tsep_1(sK4,sK3) != iProver_top
% 3.69/0.97      | m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) != iProver_top
% 3.69/0.97      | v1_funct_1(k9_tmap_1(sK3,sK4)) != iProver_top
% 3.69/0.97      | sP0_iProver_split = iProver_top ),
% 3.69/0.97      inference(demodulation,[status(thm)],[c_6904,c_5401]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_6937,plain,
% 3.69/0.97      ( m1_pre_topc(sK4,sK3) != iProver_top
% 3.69/0.97      | m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) = iProver_top ),
% 3.69/0.97      inference(superposition,[status(thm)],[c_6904,c_5410]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_4684,plain,
% 3.69/0.97      ( v1_funct_2(k9_tmap_1(sK3,X0_58),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X0_58)))
% 3.69/0.97      | ~ m1_pre_topc(X0_58,sK3) ),
% 3.69/0.97      inference(subtyping,[status(esa)],[c_1483]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_5404,plain,
% 3.69/0.97      ( v1_funct_2(k9_tmap_1(sK3,X0_58),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X0_58))) = iProver_top
% 3.69/0.97      | m1_pre_topc(X0_58,sK3) != iProver_top ),
% 3.69/0.97      inference(predicate_to_equality,[status(thm)],[c_4684]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_6938,plain,
% 3.69/0.97      ( v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK3)) = iProver_top
% 3.69/0.97      | m1_pre_topc(sK4,sK3) != iProver_top ),
% 3.69/0.97      inference(superposition,[status(thm)],[c_6904,c_5404]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_8673,plain,
% 3.69/0.97      ( v1_tsep_1(sK4,sK3) != iProver_top
% 3.69/0.97      | v1_funct_1(k9_tmap_1(sK3,sK4)) != iProver_top
% 3.69/0.97      | sP0_iProver_split = iProver_top ),
% 3.69/0.97      inference(global_propositional_subsumption,
% 3.69/0.97                [status(thm)],
% 3.69/0.97                [c_6679,c_51,c_6908,c_6937,c_6938]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_8681,plain,
% 3.69/0.97      ( v1_tsep_1(sK4,sK3) != iProver_top
% 3.69/0.97      | m1_pre_topc(sK4,sK3) != iProver_top
% 3.69/0.97      | sP0_iProver_split = iProver_top ),
% 3.69/0.97      inference(superposition,[status(thm)],[c_5409,c_8673]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_8818,plain,
% 3.69/0.97      ( v1_tsep_1(sK4,sK3) != iProver_top
% 3.69/0.97      | sP0_iProver_split = iProver_top ),
% 3.69/0.97      inference(global_propositional_subsumption,
% 3.69/0.97                [status(thm)],
% 3.69/0.97                [c_8681,c_51]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_14,plain,
% 3.69/0.97      ( v1_tsep_1(X0,X1)
% 3.69/0.97      | ~ m1_pre_topc(X0,X1)
% 3.69/0.97      | ~ l1_pre_topc(X1)
% 3.69/0.97      | sK2(X1,X0) = u1_struct_0(X0) ),
% 3.69/0.97      inference(cnf_transformation,[],[f79]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_4696,plain,
% 3.69/0.97      ( v1_tsep_1(X0_58,X1_58)
% 3.69/0.97      | ~ m1_pre_topc(X0_58,X1_58)
% 3.69/0.97      | ~ l1_pre_topc(X1_58)
% 3.69/0.97      | sK2(X1_58,X0_58) = u1_struct_0(X0_58) ),
% 3.69/0.97      inference(subtyping,[status(esa)],[c_14]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_5391,plain,
% 3.69/0.97      ( sK2(X0_58,X1_58) = u1_struct_0(X1_58)
% 3.69/0.97      | v1_tsep_1(X1_58,X0_58) = iProver_top
% 3.69/0.97      | m1_pre_topc(X1_58,X0_58) != iProver_top
% 3.69/0.97      | l1_pre_topc(X0_58) != iProver_top ),
% 3.69/0.97      inference(predicate_to_equality,[status(thm)],[c_4696]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_5871,plain,
% 3.69/0.97      ( sK2(sK3,sK4) = u1_struct_0(sK4)
% 3.69/0.97      | v1_tsep_1(sK4,sK3) = iProver_top
% 3.69/0.97      | l1_pre_topc(sK3) != iProver_top ),
% 3.69/0.97      inference(superposition,[status(thm)],[c_5398,c_5391]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_6391,plain,
% 3.69/0.97      ( v1_tsep_1(sK4,sK3) = iProver_top
% 3.69/0.97      | sK2(sK3,sK4) = u1_struct_0(sK4) ),
% 3.69/0.97      inference(global_propositional_subsumption,
% 3.69/0.97                [status(thm)],
% 3.69/0.97                [c_5871,c_50]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_6392,plain,
% 3.69/0.97      ( sK2(sK3,sK4) = u1_struct_0(sK4)
% 3.69/0.97      | v1_tsep_1(sK4,sK3) = iProver_top ),
% 3.69/0.97      inference(renaming,[status(thm)],[c_6391]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_8825,plain,
% 3.69/0.97      ( sK2(sK3,sK4) = u1_struct_0(sK4)
% 3.69/0.97      | sP0_iProver_split = iProver_top ),
% 3.69/0.97      inference(superposition,[status(thm)],[c_6392,c_8818]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_4725,plain,
% 3.69/0.97      ( ~ v3_pre_topc(X0_57,X0_58)
% 3.69/0.97      | v3_pre_topc(X1_57,X1_58)
% 3.69/0.97      | X1_58 != X0_58
% 3.69/0.97      | X1_57 != X0_57 ),
% 3.69/0.97      theory(equality) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_5831,plain,
% 3.69/0.97      ( v3_pre_topc(X0_57,X0_58)
% 3.69/0.97      | ~ v3_pre_topc(u1_struct_0(X1_58),X2_58)
% 3.69/0.97      | X0_58 != X2_58
% 3.69/0.97      | X0_57 != u1_struct_0(X1_58) ),
% 3.69/0.97      inference(instantiation,[status(thm)],[c_4725]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_9538,plain,
% 3.69/0.97      ( v3_pre_topc(sK2(sK3,sK4),X0_58)
% 3.69/0.97      | ~ v3_pre_topc(u1_struct_0(sK4),X1_58)
% 3.69/0.97      | X0_58 != X1_58
% 3.69/0.97      | sK2(sK3,sK4) != u1_struct_0(sK4) ),
% 3.69/0.97      inference(instantiation,[status(thm)],[c_5831]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_9539,plain,
% 3.69/0.97      ( X0_58 != X1_58
% 3.69/0.97      | sK2(sK3,sK4) != u1_struct_0(sK4)
% 3.69/0.97      | v3_pre_topc(sK2(sK3,sK4),X0_58) = iProver_top
% 3.69/0.97      | v3_pre_topc(u1_struct_0(sK4),X1_58) != iProver_top ),
% 3.69/0.97      inference(predicate_to_equality,[status(thm)],[c_9538]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_9541,plain,
% 3.69/0.97      ( sK3 != sK3
% 3.69/0.97      | sK2(sK3,sK4) != u1_struct_0(sK4)
% 3.69/0.97      | v3_pre_topc(sK2(sK3,sK4),sK3) = iProver_top
% 3.69/0.97      | v3_pre_topc(u1_struct_0(sK4),sK3) != iProver_top ),
% 3.69/0.97      inference(instantiation,[status(thm)],[c_9539]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_10076,plain,
% 3.69/0.97      ( k7_tmap_1(sK3,u1_struct_0(sK4)) != k9_tmap_1(sK3,sK4) ),
% 3.69/0.97      inference(global_propositional_subsumption,
% 3.69/0.97                [status(thm)],
% 3.69/0.97                [c_7102,c_50,c_51,c_4750,c_6146,c_8306,c_8635,c_8818,
% 3.69/0.97                 c_8825,c_9541]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_10078,plain,
% 3.69/0.97      ( k9_tmap_1(sK3,sK4) != k6_partfun1(u1_struct_0(sK3)) ),
% 3.69/0.97      inference(light_normalisation,[status(thm)],[c_10076,c_7220]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_0,plain,
% 3.69/0.97      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.69/0.97      inference(cnf_transformation,[],[f64]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_163,plain,
% 3.69/0.97      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 3.69/0.97      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_165,plain,
% 3.69/0.97      ( l1_pre_topc(sK3) != iProver_top
% 3.69/0.97      | l1_struct_0(sK3) = iProver_top ),
% 3.69/0.97      inference(instantiation,[status(thm)],[c_163]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_1,plain,
% 3.69/0.97      ( v2_struct_0(X0)
% 3.69/0.97      | ~ v1_xboole_0(u1_struct_0(X0))
% 3.69/0.97      | ~ l1_struct_0(X0) ),
% 3.69/0.97      inference(cnf_transformation,[],[f65]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_160,plain,
% 3.69/0.97      ( v2_struct_0(X0) = iProver_top
% 3.69/0.97      | v1_xboole_0(u1_struct_0(X0)) != iProver_top
% 3.69/0.97      | l1_struct_0(X0) != iProver_top ),
% 3.69/0.97      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_162,plain,
% 3.69/0.97      ( v2_struct_0(sK3) = iProver_top
% 3.69/0.97      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top
% 3.69/0.97      | l1_struct_0(sK3) != iProver_top ),
% 3.69/0.97      inference(instantiation,[status(thm)],[c_160]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_48,plain,
% 3.69/0.97      ( v2_struct_0(sK3) != iProver_top ),
% 3.69/0.97      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(contradiction,plain,
% 3.69/0.97      ( $false ),
% 3.69/0.97      inference(minisat,
% 3.69/0.97                [status(thm)],
% 3.69/0.97                [c_11272,c_10078,c_165,c_162,c_51,c_50,c_48]) ).
% 3.69/0.97  
% 3.69/0.97  
% 3.69/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 3.69/0.97  
% 3.69/0.97  ------                               Statistics
% 3.69/0.97  
% 3.69/0.97  ------ General
% 3.69/0.97  
% 3.69/0.97  abstr_ref_over_cycles:                  0
% 3.69/0.97  abstr_ref_under_cycles:                 0
% 3.69/0.97  gc_basic_clause_elim:                   0
% 3.69/0.97  forced_gc_time:                         0
% 3.69/0.97  parsing_time:                           0.012
% 3.69/0.97  unif_index_cands_time:                  0.
% 3.69/0.97  unif_index_add_time:                    0.
% 3.69/0.97  orderings_time:                         0.
% 3.69/0.97  out_proof_time:                         0.02
% 3.69/0.97  total_time:                             0.32
% 3.69/0.97  num_of_symbols:                         68
% 3.69/0.97  num_of_terms:                           9108
% 3.69/0.97  
% 3.69/0.97  ------ Preprocessing
% 3.69/0.97  
% 3.69/0.97  num_of_splits:                          1
% 3.69/0.97  num_of_split_atoms:                     1
% 3.69/0.97  num_of_reused_defs:                     0
% 3.69/0.97  num_eq_ax_congr_red:                    24
% 3.69/0.97  num_of_sem_filtered_clauses:            6
% 3.69/0.97  num_of_subtypes:                        4
% 3.69/0.97  monotx_restored_types:                  0
% 3.69/0.97  sat_num_of_epr_types:                   0
% 3.69/0.97  sat_num_of_non_cyclic_types:            0
% 3.69/0.97  sat_guarded_non_collapsed_types:        1
% 3.69/0.97  num_pure_diseq_elim:                    0
% 3.69/0.97  simp_replaced_by:                       0
% 3.69/0.97  res_preprocessed:                       192
% 3.69/0.97  prep_upred:                             0
% 3.69/0.97  prep_unflattend:                        170
% 3.69/0.97  smt_new_axioms:                         0
% 3.69/0.97  pred_elim_cands:                        8
% 3.69/0.97  pred_elim:                              6
% 3.69/0.97  pred_elim_cl:                           8
% 3.69/0.97  pred_elim_cycles:                       18
% 3.69/0.97  merged_defs:                            0
% 3.69/0.97  merged_defs_ncl:                        0
% 3.69/0.97  bin_hyper_res:                          0
% 3.69/0.97  prep_cycles:                            4
% 3.69/0.97  pred_elim_time:                         0.08
% 3.69/0.97  splitting_time:                         0.
% 3.69/0.97  sem_filter_time:                        0.
% 3.69/0.97  monotx_time:                            0.
% 3.69/0.97  subtype_inf_time:                       0.
% 3.69/0.97  
% 3.69/0.97  ------ Problem properties
% 3.69/0.97  
% 3.69/0.97  clauses:                                34
% 3.69/0.97  conjectures:                            5
% 3.69/0.97  epr:                                    3
% 3.69/0.97  horn:                                   22
% 3.69/0.97  ground:                                 7
% 3.69/0.97  unary:                                  3
% 3.69/0.97  binary:                                 15
% 3.69/0.97  lits:                                   116
% 3.69/0.97  lits_eq:                                24
% 3.69/0.97  fd_pure:                                0
% 3.69/0.97  fd_pseudo:                              0
% 3.69/0.97  fd_cond:                                0
% 3.69/0.97  fd_pseudo_cond:                         3
% 3.69/0.97  ac_symbols:                             0
% 3.69/0.97  
% 3.69/0.97  ------ Propositional Solver
% 3.69/0.97  
% 3.69/0.97  prop_solver_calls:                      29
% 3.69/0.97  prop_fast_solver_calls:                 2939
% 3.69/0.97  smt_solver_calls:                       0
% 3.69/0.97  smt_fast_solver_calls:                  0
% 3.69/0.97  prop_num_of_clauses:                    2824
% 3.69/0.97  prop_preprocess_simplified:             9477
% 3.69/0.97  prop_fo_subsumed:                       165
% 3.69/0.97  prop_solver_time:                       0.
% 3.69/0.97  smt_solver_time:                        0.
% 3.69/0.97  smt_fast_solver_time:                   0.
% 3.69/0.97  prop_fast_solver_time:                  0.
% 3.69/0.97  prop_unsat_core_time:                   0.
% 3.69/0.97  
% 3.69/0.97  ------ QBF
% 3.69/0.97  
% 3.69/0.97  qbf_q_res:                              0
% 3.69/0.97  qbf_num_tautologies:                    0
% 3.69/0.97  qbf_prep_cycles:                        0
% 3.69/0.97  
% 3.69/0.97  ------ BMC1
% 3.69/0.97  
% 3.69/0.97  bmc1_current_bound:                     -1
% 3.69/0.97  bmc1_last_solved_bound:                 -1
% 3.69/0.97  bmc1_unsat_core_size:                   -1
% 3.69/0.97  bmc1_unsat_core_parents_size:           -1
% 3.69/0.97  bmc1_merge_next_fun:                    0
% 3.69/0.97  bmc1_unsat_core_clauses_time:           0.
% 3.69/0.97  
% 3.69/0.97  ------ Instantiation
% 3.69/0.97  
% 3.69/0.97  inst_num_of_clauses:                    773
% 3.69/0.97  inst_num_in_passive:                    73
% 3.69/0.97  inst_num_in_active:                     391
% 3.69/0.97  inst_num_in_unprocessed:                310
% 3.69/0.97  inst_num_of_loops:                      460
% 3.69/0.97  inst_num_of_learning_restarts:          0
% 3.69/0.97  inst_num_moves_active_passive:          65
% 3.69/0.97  inst_lit_activity:                      0
% 3.69/0.97  inst_lit_activity_moves:                0
% 3.69/0.97  inst_num_tautologies:                   0
% 3.69/0.97  inst_num_prop_implied:                  0
% 3.69/0.97  inst_num_existing_simplified:           0
% 3.69/0.97  inst_num_eq_res_simplified:             0
% 3.69/0.97  inst_num_child_elim:                    0
% 3.69/0.97  inst_num_of_dismatching_blockings:      566
% 3.69/0.97  inst_num_of_non_proper_insts:           947
% 3.69/0.97  inst_num_of_duplicates:                 0
% 3.69/0.97  inst_inst_num_from_inst_to_res:         0
% 3.69/0.97  inst_dismatching_checking_time:         0.
% 3.69/0.97  
% 3.69/0.97  ------ Resolution
% 3.69/0.97  
% 3.69/0.97  res_num_of_clauses:                     0
% 3.69/0.97  res_num_in_passive:                     0
% 3.69/0.97  res_num_in_active:                      0
% 3.69/0.97  res_num_of_loops:                       196
% 3.69/0.97  res_forward_subset_subsumed:            53
% 3.69/0.97  res_backward_subset_subsumed:           2
% 3.69/0.97  res_forward_subsumed:                   0
% 3.69/0.97  res_backward_subsumed:                  0
% 3.69/0.97  res_forward_subsumption_resolution:     20
% 3.69/0.97  res_backward_subsumption_resolution:    5
% 3.69/0.97  res_clause_to_clause_subsumption:       513
% 3.69/0.97  res_orphan_elimination:                 0
% 3.69/0.97  res_tautology_del:                      137
% 3.69/0.97  res_num_eq_res_simplified:              0
% 3.69/0.97  res_num_sel_changes:                    0
% 3.69/0.97  res_moves_from_active_to_pass:          0
% 3.69/0.97  
% 3.69/0.97  ------ Superposition
% 3.69/0.97  
% 3.69/0.97  sup_time_total:                         0.
% 3.69/0.97  sup_time_generating:                    0.
% 3.69/0.97  sup_time_sim_full:                      0.
% 3.69/0.97  sup_time_sim_immed:                     0.
% 3.69/0.97  
% 3.69/0.97  sup_num_of_clauses:                     116
% 3.69/0.97  sup_num_in_active:                      88
% 3.69/0.97  sup_num_in_passive:                     28
% 3.69/0.97  sup_num_of_loops:                       91
% 3.69/0.97  sup_fw_superposition:                   71
% 3.69/0.97  sup_bw_superposition:                   55
% 3.69/0.97  sup_immediate_simplified:               36
% 3.69/0.97  sup_given_eliminated:                   0
% 3.69/0.97  comparisons_done:                       0
% 3.69/0.97  comparisons_avoided:                    11
% 3.69/0.97  
% 3.69/0.97  ------ Simplifications
% 3.69/0.97  
% 3.69/0.97  
% 3.69/0.97  sim_fw_subset_subsumed:                 7
% 3.69/0.97  sim_bw_subset_subsumed:                 10
% 3.69/0.97  sim_fw_subsumed:                        5
% 3.69/0.97  sim_bw_subsumed:                        0
% 3.69/0.97  sim_fw_subsumption_res:                 0
% 3.69/0.97  sim_bw_subsumption_res:                 0
% 3.69/0.97  sim_tautology_del:                      4
% 3.69/0.97  sim_eq_tautology_del:                   10
% 3.69/0.97  sim_eq_res_simp:                        0
% 3.69/0.97  sim_fw_demodulated:                     0
% 3.69/0.97  sim_bw_demodulated:                     3
% 3.69/0.97  sim_light_normalised:                   36
% 3.69/0.97  sim_joinable_taut:                      0
% 3.69/0.97  sim_joinable_simp:                      0
% 3.69/0.97  sim_ac_normalised:                      0
% 3.69/0.97  sim_smt_subsumption:                    0
% 3.69/0.97  
%------------------------------------------------------------------------------
