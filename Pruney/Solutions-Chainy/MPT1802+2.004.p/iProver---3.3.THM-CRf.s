%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:07 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :  218 (1471 expanded)
%              Number of clauses        :  129 ( 325 expanded)
%              Number of leaves         :   23 ( 503 expanded)
%              Depth                    :   25
%              Number of atoms          : 1081 (11465 expanded)
%              Number of equality atoms :  205 ( 535 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   20 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f61,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f7])).

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

fof(f47,plain,(
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

fof(f48,plain,(
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
    inference(rectify,[],[f47])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2)))
        & u1_struct_0(X1) = sK1(X0,X1,X2)
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f48,f49])).

fof(f67,plain,(
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
    inference(cnf_transformation,[],[f50])).

fof(f99,plain,(
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
    inference(equality_resolution,[],[f67])).

fof(f100,plain,(
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
    inference(equality_resolution,[],[f99])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
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
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X2))
                     => r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
              & r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
              & r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
          & m1_subset_1(X3,u1_struct_0(X2)) )
     => ( ~ r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),sK5)
        & m1_subset_1(sK5,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
              & m1_subset_1(X3,u1_struct_0(X2)) )
          & r1_tsep_1(X1,X2)
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ~ r1_tmap_1(sK4,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),sK4),X3)
            & m1_subset_1(X3,u1_struct_0(sK4)) )
        & r1_tsep_1(X1,sK4)
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
              & r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_tmap_1(X2,k8_tmap_1(X0,sK3),k2_tmap_1(X0,k8_tmap_1(X0,sK3),k9_tmap_1(X0,sK3),X2),X3)
                & m1_subset_1(X3,u1_struct_0(X2)) )
            & r1_tsep_1(sK3,X2)
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
                    & m1_subset_1(X3,u1_struct_0(X2)) )
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
              ( ? [X3] :
                  ( ~ r1_tmap_1(X2,k8_tmap_1(sK2,X1),k2_tmap_1(sK2,k8_tmap_1(sK2,X1),k9_tmap_1(sK2,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
              & r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,sK2)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK2)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ~ r1_tmap_1(sK4,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),sK5)
    & m1_subset_1(sK5,u1_struct_0(sK4))
    & r1_tsep_1(sK3,sK4)
    & m1_pre_topc(sK4,sK2)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f41,f55,f54,f53,f52])).

fof(f90,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f86,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f87,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f88,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k9_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f6])).

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

fof(f43,plain,(
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

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k6_tmap_1(X0,X3) != X2
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k6_tmap_1(X0,sK0(X0,X1,X2)) != X2
        & u1_struct_0(X1) = sK0(X0,X1,X2)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f44,f45])).

fof(f63,plain,(
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
    inference(cnf_transformation,[],[f46])).

fof(f97,plain,(
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
    inference(equality_resolution,[],[f63])).

fof(f98,plain,(
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
    inference(equality_resolution,[],[f97])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f78,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f93,plain,(
    r1_tsep_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f56])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f58,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f59,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f92,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | ~ r1_xboole_0(u1_struct_0(X2),X1)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | ~ r1_xboole_0(u1_struct_0(X2),X1)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f95,plain,(
    ~ r1_tmap_1(sK4,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),sK5) ),
    inference(cnf_transformation,[],[f56])).

fof(f91,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f56])).

fof(f94,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f56])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f82,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_5,plain,
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
    inference(cnf_transformation,[],[f61])).

cnf(c_13,plain,
    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
    | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_23,plain,
    ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_22,plain,
    ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_236,plain,
    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_23,c_22])).

cnf(c_34,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1169,plain,
    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_236,c_34])).

cnf(c_1170,plain,
    ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))),k9_tmap_1(sK2,sK3),k7_tmap_1(sK2,u1_struct_0(sK3)))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(k9_tmap_1(sK2,sK3))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1169])).

cnf(c_38,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_37,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_36,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_28,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_962,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_34])).

cnf(c_963,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_962])).

cnf(c_24,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k9_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_973,plain,
    ( ~ v2_pre_topc(X0)
    | v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_34])).

cnf(c_974,plain,
    ( ~ v2_pre_topc(sK2)
    | v1_funct_1(k9_tmap_1(sK2,sK3))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_973])).

cnf(c_1172,plain,
    ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))),k9_tmap_1(sK2,sK3),k7_tmap_1(sK2,u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1170,c_38,c_37,c_36,c_963,c_974])).

cnf(c_2747,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_xboole_0(X5)
    | v1_xboole_0(X2)
    | X3 = X0
    | k7_tmap_1(sK2,u1_struct_0(sK3)) != X3
    | k9_tmap_1(sK2,sK3) != X0
    | u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))) != X5
    | u1_struct_0(k8_tmap_1(sK2,sK3)) != X2
    | u1_struct_0(sK2) != X4
    | u1_struct_0(sK2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_1172])).

cnf(c_2748,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
    | ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))))
    | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3)))
    | ~ v1_funct_1(k9_tmap_1(sK2,sK3))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
    | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_2747])).

cnf(c_1180,plain,
    ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_34])).

cnf(c_1181,plain,
    ( v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1180])).

cnf(c_1191,plain,
    ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_34])).

cnf(c_1192,plain,
    ( m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1191])).

cnf(c_2750,plain,
    ( ~ v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3)))
    | ~ v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
    | ~ m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
    | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2748,c_38,c_37,c_36,c_974,c_1181,c_1192])).

cnf(c_2751,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
    | ~ m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))))
    | ~ v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3)))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
    | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3) ),
    inference(renaming,[status(thm)],[c_2750])).

cnf(c_3933,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
    | ~ m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))))
    | ~ v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3)))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
    | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_2751])).

cnf(c_4853,plain,
    ( k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3)
    | v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3))) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))) = iProver_top
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3933])).

cnf(c_9,plain,
    ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(k8_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(k8_tmap_1(X1,X0))
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_21,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_20,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k8_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_19,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_246,plain,
    ( ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_28,c_21,c_20,c_19])).

cnf(c_247,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(renaming,[status(thm)],[c_246])).

cnf(c_954,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k6_tmap_1(X0,u1_struct_0(X1)) = k8_tmap_1(X0,X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_247,c_34])).

cnf(c_955,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_954])).

cnf(c_957,plain,
    ( k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_955,c_38,c_37,c_36])).

cnf(c_3975,plain,
    ( k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_957])).

cnf(c_5067,plain,
    ( k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3)
    | v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3))) != iProver_top
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4853,c_3975])).

cnf(c_41,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_15,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_31,negated_conjecture,
    ( r1_tsep_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_490,plain,
    ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0)
    | sK3 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_31])).

cnf(c_491,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_490])).

cnf(c_964,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_963])).

cnf(c_1,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_32,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_943,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK2 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_32])).

cnf(c_944,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_943])).

cnf(c_946,plain,
    ( l1_pre_topc(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_944,c_36])).

cnf(c_1977,plain,
    ( l1_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_946])).

cnf(c_1978,plain,
    ( l1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1977])).

cnf(c_1071,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_34])).

cnf(c_1072,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1071])).

cnf(c_1074,plain,
    ( l1_pre_topc(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1072,c_36])).

cnf(c_1991,plain,
    ( l1_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_1074])).

cnf(c_1992,plain,
    ( l1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_1991])).

cnf(c_3986,plain,
    ( X0_59 = X0_59 ),
    theory(equality)).

cnf(c_4031,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_3986])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k7_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1644,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_funct_1(k7_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_37])).

cnf(c_1645,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_funct_1(k7_tmap_1(sK2,X0))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1644])).

cnf(c_1649,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_funct_1(k7_tmap_1(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1645,c_38,c_36])).

cnf(c_3955,plain,
    ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_funct_1(k7_tmap_1(sK2,X0_58)) ),
    inference(subtyping,[status(esa)],[c_1649])).

cnf(c_5244,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_3955])).

cnf(c_5245,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5244])).

cnf(c_0,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_3983,plain,
    ( ~ r1_xboole_0(X0_58,X1_58)
    | r1_xboole_0(X1_58,X0_58) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_5341,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4))
    | r1_xboole_0(u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_3983])).

cnf(c_5908,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_3986])).

cnf(c_27,plain,
    ( r1_tmap_1(X0,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X0),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X1)
    | ~ r1_xboole_0(u1_struct_0(X0),X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_29,negated_conjecture,
    ( ~ r1_tmap_1(sK4,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),sK5) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_444,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_pre_topc(X3,X1)
    | ~ r1_xboole_0(u1_struct_0(X3),X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),X3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(X1,X0) != k8_tmap_1(sK2,sK3)
    | sK5 != X2
    | sK4 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_29])).

cnf(c_445,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_pre_topc(sK4,X1)
    | ~ r1_xboole_0(u1_struct_0(sK4),X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(X1,X0) != k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_444])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_449,plain,
    ( v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ r1_xboole_0(u1_struct_0(sK4),X0)
    | ~ m1_pre_topc(sK4,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(X1,X0) != k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_445,c_33,c_30])).

cnf(c_450,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(sK4,X1)
    | ~ r1_xboole_0(u1_struct_0(sK4),X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(X1,X0) != k8_tmap_1(sK2,sK3) ),
    inference(renaming,[status(thm)],[c_449])).

cnf(c_1364,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(u1_struct_0(sK4),X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(X1,X0) != k8_tmap_1(sK2,sK3)
    | sK2 != X1
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_450])).

cnf(c_1365,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_xboole_0(u1_struct_0(sK4),X0)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k2_tmap_1(sK2,k6_tmap_1(sK2,X0),k7_tmap_1(sK2,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(sK2,X0) != k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_1364])).

cnf(c_1369,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK4),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k2_tmap_1(sK2,k6_tmap_1(sK2,X0),k7_tmap_1(sK2,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(sK2,X0) != k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1365,c_38,c_37,c_36])).

cnf(c_1370,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_xboole_0(u1_struct_0(sK4),X0)
    | k2_tmap_1(sK2,k6_tmap_1(sK2,X0),k7_tmap_1(sK2,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(sK2,X0) != k8_tmap_1(sK2,sK3) ),
    inference(renaming,[status(thm)],[c_1369])).

cnf(c_3964,plain,
    ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_xboole_0(u1_struct_0(sK4),X0_58)
    | k2_tmap_1(sK2,k6_tmap_1(sK2,X0_58),k7_tmap_1(sK2,X0_58),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(sK2,X0_58) != k8_tmap_1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_1370])).

cnf(c_6023,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_xboole_0(u1_struct_0(sK4),u1_struct_0(sK3))
    | k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(sK3)),k7_tmap_1(sK2,u1_struct_0(sK3)),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(sK2,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_3964])).

cnf(c_4010,plain,
    ( k2_tmap_1(X0_59,X1_59,X0_58,X2_59) = k2_tmap_1(X3_59,X4_59,X1_58,X5_59)
    | X0_59 != X3_59
    | X1_59 != X4_59
    | X2_59 != X5_59
    | X0_58 != X1_58 ),
    theory(equality)).

cnf(c_6054,plain,
    ( k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(sK3)),k7_tmap_1(sK2,u1_struct_0(sK3)),sK4) = k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(sK2,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3)
    | sK2 != sK2
    | sK4 != sK4
    | k7_tmap_1(sK2,u1_struct_0(sK3)) != k9_tmap_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_4010])).

cnf(c_6301,plain,
    ( m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top
    | v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5067,c_36,c_41,c_491,c_963,c_964,c_1978,c_1992,c_4031,c_3975,c_5245,c_5341,c_5908,c_6023,c_6054])).

cnf(c_6302,plain,
    ( v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3))) = iProver_top ),
    inference(renaming,[status(thm)],[c_6301])).

cnf(c_965,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_963,c_36])).

cnf(c_3974,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subtyping,[status(esa)],[c_965])).

cnf(c_4816,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3974])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1608,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_37])).

cnf(c_1609,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(k6_tmap_1(sK2,X0)) = u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1608])).

cnf(c_1613,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | u1_struct_0(k6_tmap_1(sK2,X0)) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1609,c_38,c_36])).

cnf(c_3957,plain,
    ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK2)))
    | u1_struct_0(k6_tmap_1(sK2,X0_58)) = u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_1613])).

cnf(c_4829,plain,
    ( u1_struct_0(k6_tmap_1(sK2,X0_58)) = u1_struct_0(sK2)
    | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3957])).

cnf(c_5639,plain,
    ( u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))) = u1_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_4816,c_4829])).

cnf(c_5641,plain,
    ( u1_struct_0(k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2) ),
    inference(light_normalisation,[status(thm)],[c_5639,c_3975])).

cnf(c_6305,plain,
    ( v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6302,c_5641])).

cnf(c_3,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1963,plain,
    ( l1_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_36])).

cnf(c_1964,plain,
    ( l1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1963])).

cnf(c_2012,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_1964])).

cnf(c_2013,plain,
    ( v2_struct_0(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_2012])).

cnf(c_125,plain,
    ( v2_struct_0(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK2))
    | ~ l1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_129,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2015,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2013,c_38,c_36,c_125,c_129])).

cnf(c_3941,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_2015])).

cnf(c_4845,plain,
    ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3941])).

cnf(c_6309,plain,
    ( v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6305,c_4845])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1662,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_37])).

cnf(c_1663,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(k7_tmap_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0)))))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1662])).

cnf(c_1667,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(k7_tmap_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1663,c_38,c_36])).

cnf(c_3954,plain,
    ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(k7_tmap_1(sK2,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0_58))))) ),
    inference(subtyping,[status(esa)],[c_1667])).

cnf(c_4832,plain,
    ( m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK2,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0_58))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3954])).

cnf(c_6092,plain,
    ( m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) = iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3975,c_4832])).

cnf(c_6095,plain,
    ( m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) = iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6092,c_5641])).

cnf(c_17,plain,
    ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1848,plain,
    ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_37])).

cnf(c_1849,plain,
    ( v1_funct_2(k7_tmap_1(sK2,X0),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1848])).

cnf(c_1853,plain,
    ( v1_funct_2(k7_tmap_1(sK2,X0),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1849,c_38,c_36])).

cnf(c_3945,plain,
    ( v1_funct_2(k7_tmap_1(sK2,X0_58),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0_58)))
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subtyping,[status(esa)],[c_1853])).

cnf(c_4841,plain,
    ( v1_funct_2(k7_tmap_1(sK2,X0_58),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0_58))) = iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3945])).

cnf(c_6075,plain,
    ( v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) = iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3975,c_4841])).

cnf(c_6078,plain,
    ( v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6075,c_5641])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6309,c_6095,c_6078,c_964,c_41])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:27:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.81/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/0.98  
% 2.81/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.81/0.98  
% 2.81/0.98  ------  iProver source info
% 2.81/0.98  
% 2.81/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.81/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.81/0.98  git: non_committed_changes: false
% 2.81/0.98  git: last_make_outside_of_git: false
% 2.81/0.98  
% 2.81/0.98  ------ 
% 2.81/0.98  
% 2.81/0.98  ------ Input Options
% 2.81/0.98  
% 2.81/0.98  --out_options                           all
% 2.81/0.98  --tptp_safe_out                         true
% 2.81/0.98  --problem_path                          ""
% 2.81/0.98  --include_path                          ""
% 2.81/0.98  --clausifier                            res/vclausify_rel
% 2.81/0.98  --clausifier_options                    --mode clausify
% 2.81/0.98  --stdin                                 false
% 2.81/0.98  --stats_out                             all
% 2.81/0.98  
% 2.81/0.98  ------ General Options
% 2.81/0.98  
% 2.81/0.98  --fof                                   false
% 2.81/0.98  --time_out_real                         305.
% 2.81/0.98  --time_out_virtual                      -1.
% 2.81/0.98  --symbol_type_check                     false
% 2.81/0.98  --clausify_out                          false
% 2.81/0.98  --sig_cnt_out                           false
% 2.81/0.98  --trig_cnt_out                          false
% 2.81/0.98  --trig_cnt_out_tolerance                1.
% 2.81/0.98  --trig_cnt_out_sk_spl                   false
% 2.81/0.98  --abstr_cl_out                          false
% 2.81/0.98  
% 2.81/0.98  ------ Global Options
% 2.81/0.98  
% 2.81/0.98  --schedule                              default
% 2.81/0.98  --add_important_lit                     false
% 2.81/0.98  --prop_solver_per_cl                    1000
% 2.81/0.98  --min_unsat_core                        false
% 2.81/0.98  --soft_assumptions                      false
% 2.81/0.98  --soft_lemma_size                       3
% 2.81/0.98  --prop_impl_unit_size                   0
% 2.81/0.98  --prop_impl_unit                        []
% 2.81/0.98  --share_sel_clauses                     true
% 2.81/0.98  --reset_solvers                         false
% 2.81/0.98  --bc_imp_inh                            [conj_cone]
% 2.81/0.98  --conj_cone_tolerance                   3.
% 2.81/0.98  --extra_neg_conj                        none
% 2.81/0.98  --large_theory_mode                     true
% 2.81/0.98  --prolific_symb_bound                   200
% 2.81/0.98  --lt_threshold                          2000
% 2.81/0.98  --clause_weak_htbl                      true
% 2.81/0.98  --gc_record_bc_elim                     false
% 2.81/0.98  
% 2.81/0.98  ------ Preprocessing Options
% 2.81/0.98  
% 2.81/0.98  --preprocessing_flag                    true
% 2.81/0.98  --time_out_prep_mult                    0.1
% 2.81/0.98  --splitting_mode                        input
% 2.81/0.98  --splitting_grd                         true
% 2.81/0.98  --splitting_cvd                         false
% 2.81/0.98  --splitting_cvd_svl                     false
% 2.81/0.98  --splitting_nvd                         32
% 2.81/0.98  --sub_typing                            true
% 2.81/0.98  --prep_gs_sim                           true
% 2.81/0.98  --prep_unflatten                        true
% 2.81/0.98  --prep_res_sim                          true
% 2.81/0.98  --prep_upred                            true
% 2.81/0.98  --prep_sem_filter                       exhaustive
% 2.81/0.98  --prep_sem_filter_out                   false
% 2.81/0.98  --pred_elim                             true
% 2.81/0.98  --res_sim_input                         true
% 2.81/0.98  --eq_ax_congr_red                       true
% 2.81/0.98  --pure_diseq_elim                       true
% 2.81/0.98  --brand_transform                       false
% 2.81/0.98  --non_eq_to_eq                          false
% 2.81/0.98  --prep_def_merge                        true
% 2.81/0.98  --prep_def_merge_prop_impl              false
% 2.81/0.98  --prep_def_merge_mbd                    true
% 2.81/0.98  --prep_def_merge_tr_red                 false
% 2.81/0.98  --prep_def_merge_tr_cl                  false
% 2.81/0.98  --smt_preprocessing                     true
% 2.81/0.98  --smt_ac_axioms                         fast
% 2.81/0.98  --preprocessed_out                      false
% 2.81/0.98  --preprocessed_stats                    false
% 2.81/0.98  
% 2.81/0.98  ------ Abstraction refinement Options
% 2.81/0.98  
% 2.81/0.98  --abstr_ref                             []
% 2.81/0.98  --abstr_ref_prep                        false
% 2.81/0.98  --abstr_ref_until_sat                   false
% 2.81/0.98  --abstr_ref_sig_restrict                funpre
% 2.81/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.81/0.98  --abstr_ref_under                       []
% 2.81/0.98  
% 2.81/0.98  ------ SAT Options
% 2.81/0.98  
% 2.81/0.98  --sat_mode                              false
% 2.81/0.98  --sat_fm_restart_options                ""
% 2.81/0.98  --sat_gr_def                            false
% 2.81/0.98  --sat_epr_types                         true
% 2.81/0.98  --sat_non_cyclic_types                  false
% 2.81/0.98  --sat_finite_models                     false
% 2.81/0.98  --sat_fm_lemmas                         false
% 2.81/0.98  --sat_fm_prep                           false
% 2.81/0.98  --sat_fm_uc_incr                        true
% 2.81/0.98  --sat_out_model                         small
% 2.81/0.98  --sat_out_clauses                       false
% 2.81/0.98  
% 2.81/0.98  ------ QBF Options
% 2.81/0.98  
% 2.81/0.98  --qbf_mode                              false
% 2.81/0.98  --qbf_elim_univ                         false
% 2.81/0.98  --qbf_dom_inst                          none
% 2.81/0.98  --qbf_dom_pre_inst                      false
% 2.81/0.98  --qbf_sk_in                             false
% 2.81/0.98  --qbf_pred_elim                         true
% 2.81/0.98  --qbf_split                             512
% 2.81/0.98  
% 2.81/0.98  ------ BMC1 Options
% 2.81/0.98  
% 2.81/0.98  --bmc1_incremental                      false
% 2.81/0.98  --bmc1_axioms                           reachable_all
% 2.81/0.98  --bmc1_min_bound                        0
% 2.81/0.98  --bmc1_max_bound                        -1
% 2.81/0.98  --bmc1_max_bound_default                -1
% 2.81/0.98  --bmc1_symbol_reachability              true
% 2.81/0.98  --bmc1_property_lemmas                  false
% 2.81/0.98  --bmc1_k_induction                      false
% 2.81/0.98  --bmc1_non_equiv_states                 false
% 2.81/0.98  --bmc1_deadlock                         false
% 2.81/0.98  --bmc1_ucm                              false
% 2.81/0.98  --bmc1_add_unsat_core                   none
% 2.81/0.98  --bmc1_unsat_core_children              false
% 2.81/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.81/0.98  --bmc1_out_stat                         full
% 2.81/0.98  --bmc1_ground_init                      false
% 2.81/0.98  --bmc1_pre_inst_next_state              false
% 2.81/0.98  --bmc1_pre_inst_state                   false
% 2.81/0.98  --bmc1_pre_inst_reach_state             false
% 2.81/0.98  --bmc1_out_unsat_core                   false
% 2.81/0.98  --bmc1_aig_witness_out                  false
% 2.81/0.98  --bmc1_verbose                          false
% 2.81/0.98  --bmc1_dump_clauses_tptp                false
% 2.81/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.81/0.98  --bmc1_dump_file                        -
% 2.81/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.81/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.81/0.98  --bmc1_ucm_extend_mode                  1
% 2.81/0.98  --bmc1_ucm_init_mode                    2
% 2.81/0.98  --bmc1_ucm_cone_mode                    none
% 2.81/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.81/0.98  --bmc1_ucm_relax_model                  4
% 2.81/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.81/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.81/0.98  --bmc1_ucm_layered_model                none
% 2.81/0.98  --bmc1_ucm_max_lemma_size               10
% 2.81/0.98  
% 2.81/0.98  ------ AIG Options
% 2.81/0.98  
% 2.81/0.98  --aig_mode                              false
% 2.81/0.98  
% 2.81/0.98  ------ Instantiation Options
% 2.81/0.98  
% 2.81/0.98  --instantiation_flag                    true
% 2.81/0.98  --inst_sos_flag                         false
% 2.81/0.98  --inst_sos_phase                        true
% 2.81/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.81/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.81/0.98  --inst_lit_sel_side                     num_symb
% 2.81/0.98  --inst_solver_per_active                1400
% 2.81/0.98  --inst_solver_calls_frac                1.
% 2.81/0.98  --inst_passive_queue_type               priority_queues
% 2.81/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.81/0.98  --inst_passive_queues_freq              [25;2]
% 2.81/0.98  --inst_dismatching                      true
% 2.81/0.98  --inst_eager_unprocessed_to_passive     true
% 2.81/0.98  --inst_prop_sim_given                   true
% 2.81/0.98  --inst_prop_sim_new                     false
% 2.81/0.98  --inst_subs_new                         false
% 2.81/0.98  --inst_eq_res_simp                      false
% 2.81/0.98  --inst_subs_given                       false
% 2.81/0.98  --inst_orphan_elimination               true
% 2.81/0.98  --inst_learning_loop_flag               true
% 2.81/0.98  --inst_learning_start                   3000
% 2.81/0.98  --inst_learning_factor                  2
% 2.81/0.98  --inst_start_prop_sim_after_learn       3
% 2.81/0.98  --inst_sel_renew                        solver
% 2.81/0.98  --inst_lit_activity_flag                true
% 2.81/0.98  --inst_restr_to_given                   false
% 2.81/0.98  --inst_activity_threshold               500
% 2.81/0.98  --inst_out_proof                        true
% 2.81/0.98  
% 2.81/0.98  ------ Resolution Options
% 2.81/0.98  
% 2.81/0.98  --resolution_flag                       true
% 2.81/0.98  --res_lit_sel                           adaptive
% 2.81/0.98  --res_lit_sel_side                      none
% 2.81/0.98  --res_ordering                          kbo
% 2.81/0.98  --res_to_prop_solver                    active
% 2.81/0.98  --res_prop_simpl_new                    false
% 2.81/0.98  --res_prop_simpl_given                  true
% 2.81/0.98  --res_passive_queue_type                priority_queues
% 2.81/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.81/0.98  --res_passive_queues_freq               [15;5]
% 2.81/0.98  --res_forward_subs                      full
% 2.81/0.98  --res_backward_subs                     full
% 2.81/0.98  --res_forward_subs_resolution           true
% 2.81/0.98  --res_backward_subs_resolution          true
% 2.81/0.98  --res_orphan_elimination                true
% 2.81/0.98  --res_time_limit                        2.
% 2.81/0.98  --res_out_proof                         true
% 2.81/0.98  
% 2.81/0.98  ------ Superposition Options
% 2.81/0.98  
% 2.81/0.98  --superposition_flag                    true
% 2.81/0.98  --sup_passive_queue_type                priority_queues
% 2.81/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.81/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.81/0.98  --demod_completeness_check              fast
% 2.81/0.98  --demod_use_ground                      true
% 2.81/0.98  --sup_to_prop_solver                    passive
% 2.81/0.98  --sup_prop_simpl_new                    true
% 2.81/0.98  --sup_prop_simpl_given                  true
% 2.81/0.98  --sup_fun_splitting                     false
% 2.81/0.98  --sup_smt_interval                      50000
% 2.81/0.98  
% 2.81/0.98  ------ Superposition Simplification Setup
% 2.81/0.98  
% 2.81/0.98  --sup_indices_passive                   []
% 2.81/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.81/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.81/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.81/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.81/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.81/0.98  --sup_full_bw                           [BwDemod]
% 2.81/0.98  --sup_immed_triv                        [TrivRules]
% 2.81/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.81/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.81/0.98  --sup_immed_bw_main                     []
% 2.81/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.81/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.81/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.81/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.81/0.99  
% 2.81/0.99  ------ Combination Options
% 2.81/0.99  
% 2.81/0.99  --comb_res_mult                         3
% 2.81/0.99  --comb_sup_mult                         2
% 2.81/0.99  --comb_inst_mult                        10
% 2.81/0.99  
% 2.81/0.99  ------ Debug Options
% 2.81/0.99  
% 2.81/0.99  --dbg_backtrace                         false
% 2.81/0.99  --dbg_dump_prop_clauses                 false
% 2.81/0.99  --dbg_dump_prop_clauses_file            -
% 2.81/0.99  --dbg_out_stat                          false
% 2.81/0.99  ------ Parsing...
% 2.81/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.81/0.99  
% 2.81/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e 
% 2.81/0.99  
% 2.81/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.81/0.99  
% 2.81/0.99  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.81/0.99  ------ Proving...
% 2.81/0.99  ------ Problem Properties 
% 2.81/0.99  
% 2.81/0.99  
% 2.81/0.99  clauses                                 53
% 2.81/0.99  conjectures                             4
% 2.81/0.99  EPR                                     4
% 2.81/0.99  Horn                                    31
% 2.81/0.99  unary                                   18
% 2.81/0.99  binary                                  14
% 2.81/0.99  lits                                    142
% 2.81/0.99  lits eq                                 40
% 2.81/0.99  fd_pure                                 0
% 2.81/0.99  fd_pseudo                               0
% 2.81/0.99  fd_cond                                 6
% 2.81/0.99  fd_pseudo_cond                          0
% 2.81/0.99  AC symbols                              0
% 2.81/0.99  
% 2.81/0.99  ------ Schedule dynamic 5 is on 
% 2.81/0.99  
% 2.81/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.81/0.99  
% 2.81/0.99  
% 2.81/0.99  ------ 
% 2.81/0.99  Current options:
% 2.81/0.99  ------ 
% 2.81/0.99  
% 2.81/0.99  ------ Input Options
% 2.81/0.99  
% 2.81/0.99  --out_options                           all
% 2.81/0.99  --tptp_safe_out                         true
% 2.81/0.99  --problem_path                          ""
% 2.81/0.99  --include_path                          ""
% 2.81/0.99  --clausifier                            res/vclausify_rel
% 2.81/0.99  --clausifier_options                    --mode clausify
% 2.81/0.99  --stdin                                 false
% 2.81/0.99  --stats_out                             all
% 2.81/0.99  
% 2.81/0.99  ------ General Options
% 2.81/0.99  
% 2.81/0.99  --fof                                   false
% 2.81/0.99  --time_out_real                         305.
% 2.81/0.99  --time_out_virtual                      -1.
% 2.81/0.99  --symbol_type_check                     false
% 2.81/0.99  --clausify_out                          false
% 2.81/0.99  --sig_cnt_out                           false
% 2.81/0.99  --trig_cnt_out                          false
% 2.81/0.99  --trig_cnt_out_tolerance                1.
% 2.81/0.99  --trig_cnt_out_sk_spl                   false
% 2.81/0.99  --abstr_cl_out                          false
% 2.81/0.99  
% 2.81/0.99  ------ Global Options
% 2.81/0.99  
% 2.81/0.99  --schedule                              default
% 2.81/0.99  --add_important_lit                     false
% 2.81/0.99  --prop_solver_per_cl                    1000
% 2.81/0.99  --min_unsat_core                        false
% 2.81/0.99  --soft_assumptions                      false
% 2.81/0.99  --soft_lemma_size                       3
% 2.81/0.99  --prop_impl_unit_size                   0
% 2.81/0.99  --prop_impl_unit                        []
% 2.81/0.99  --share_sel_clauses                     true
% 2.81/0.99  --reset_solvers                         false
% 2.81/0.99  --bc_imp_inh                            [conj_cone]
% 2.81/0.99  --conj_cone_tolerance                   3.
% 2.81/0.99  --extra_neg_conj                        none
% 2.81/0.99  --large_theory_mode                     true
% 2.81/0.99  --prolific_symb_bound                   200
% 2.81/0.99  --lt_threshold                          2000
% 2.81/0.99  --clause_weak_htbl                      true
% 2.81/0.99  --gc_record_bc_elim                     false
% 2.81/0.99  
% 2.81/0.99  ------ Preprocessing Options
% 2.81/0.99  
% 2.81/0.99  --preprocessing_flag                    true
% 2.81/0.99  --time_out_prep_mult                    0.1
% 2.81/0.99  --splitting_mode                        input
% 2.81/0.99  --splitting_grd                         true
% 2.81/0.99  --splitting_cvd                         false
% 2.81/0.99  --splitting_cvd_svl                     false
% 2.81/0.99  --splitting_nvd                         32
% 2.81/0.99  --sub_typing                            true
% 2.81/0.99  --prep_gs_sim                           true
% 2.81/0.99  --prep_unflatten                        true
% 2.81/0.99  --prep_res_sim                          true
% 2.81/0.99  --prep_upred                            true
% 2.81/0.99  --prep_sem_filter                       exhaustive
% 2.81/0.99  --prep_sem_filter_out                   false
% 2.81/0.99  --pred_elim                             true
% 2.81/0.99  --res_sim_input                         true
% 2.81/0.99  --eq_ax_congr_red                       true
% 2.81/0.99  --pure_diseq_elim                       true
% 2.81/0.99  --brand_transform                       false
% 2.81/0.99  --non_eq_to_eq                          false
% 2.81/0.99  --prep_def_merge                        true
% 2.81/0.99  --prep_def_merge_prop_impl              false
% 2.81/0.99  --prep_def_merge_mbd                    true
% 2.81/0.99  --prep_def_merge_tr_red                 false
% 2.81/0.99  --prep_def_merge_tr_cl                  false
% 2.81/0.99  --smt_preprocessing                     true
% 2.81/0.99  --smt_ac_axioms                         fast
% 2.81/0.99  --preprocessed_out                      false
% 2.81/0.99  --preprocessed_stats                    false
% 2.81/0.99  
% 2.81/0.99  ------ Abstraction refinement Options
% 2.81/0.99  
% 2.81/0.99  --abstr_ref                             []
% 2.81/0.99  --abstr_ref_prep                        false
% 2.81/0.99  --abstr_ref_until_sat                   false
% 2.81/0.99  --abstr_ref_sig_restrict                funpre
% 2.81/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.81/0.99  --abstr_ref_under                       []
% 2.81/0.99  
% 2.81/0.99  ------ SAT Options
% 2.81/0.99  
% 2.81/0.99  --sat_mode                              false
% 2.81/0.99  --sat_fm_restart_options                ""
% 2.81/0.99  --sat_gr_def                            false
% 2.81/0.99  --sat_epr_types                         true
% 2.81/0.99  --sat_non_cyclic_types                  false
% 2.81/0.99  --sat_finite_models                     false
% 2.81/0.99  --sat_fm_lemmas                         false
% 2.81/0.99  --sat_fm_prep                           false
% 2.81/0.99  --sat_fm_uc_incr                        true
% 2.81/0.99  --sat_out_model                         small
% 2.81/0.99  --sat_out_clauses                       false
% 2.81/0.99  
% 2.81/0.99  ------ QBF Options
% 2.81/0.99  
% 2.81/0.99  --qbf_mode                              false
% 2.81/0.99  --qbf_elim_univ                         false
% 2.81/0.99  --qbf_dom_inst                          none
% 2.81/0.99  --qbf_dom_pre_inst                      false
% 2.81/0.99  --qbf_sk_in                             false
% 2.81/0.99  --qbf_pred_elim                         true
% 2.81/0.99  --qbf_split                             512
% 2.81/0.99  
% 2.81/0.99  ------ BMC1 Options
% 2.81/0.99  
% 2.81/0.99  --bmc1_incremental                      false
% 2.81/0.99  --bmc1_axioms                           reachable_all
% 2.81/0.99  --bmc1_min_bound                        0
% 2.81/0.99  --bmc1_max_bound                        -1
% 2.81/0.99  --bmc1_max_bound_default                -1
% 2.81/0.99  --bmc1_symbol_reachability              true
% 2.81/0.99  --bmc1_property_lemmas                  false
% 2.81/0.99  --bmc1_k_induction                      false
% 2.81/0.99  --bmc1_non_equiv_states                 false
% 2.81/0.99  --bmc1_deadlock                         false
% 2.81/0.99  --bmc1_ucm                              false
% 2.81/0.99  --bmc1_add_unsat_core                   none
% 2.81/0.99  --bmc1_unsat_core_children              false
% 2.81/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.81/0.99  --bmc1_out_stat                         full
% 2.81/0.99  --bmc1_ground_init                      false
% 2.81/0.99  --bmc1_pre_inst_next_state              false
% 2.81/0.99  --bmc1_pre_inst_state                   false
% 2.81/0.99  --bmc1_pre_inst_reach_state             false
% 2.81/0.99  --bmc1_out_unsat_core                   false
% 2.81/0.99  --bmc1_aig_witness_out                  false
% 2.81/0.99  --bmc1_verbose                          false
% 2.81/0.99  --bmc1_dump_clauses_tptp                false
% 2.81/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.81/0.99  --bmc1_dump_file                        -
% 2.81/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.81/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.81/0.99  --bmc1_ucm_extend_mode                  1
% 2.81/0.99  --bmc1_ucm_init_mode                    2
% 2.81/0.99  --bmc1_ucm_cone_mode                    none
% 2.81/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.81/0.99  --bmc1_ucm_relax_model                  4
% 2.81/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.81/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.81/0.99  --bmc1_ucm_layered_model                none
% 2.81/0.99  --bmc1_ucm_max_lemma_size               10
% 2.81/0.99  
% 2.81/0.99  ------ AIG Options
% 2.81/0.99  
% 2.81/0.99  --aig_mode                              false
% 2.81/0.99  
% 2.81/0.99  ------ Instantiation Options
% 2.81/0.99  
% 2.81/0.99  --instantiation_flag                    true
% 2.81/0.99  --inst_sos_flag                         false
% 2.81/0.99  --inst_sos_phase                        true
% 2.81/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.81/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.81/0.99  --inst_lit_sel_side                     none
% 2.81/0.99  --inst_solver_per_active                1400
% 2.81/0.99  --inst_solver_calls_frac                1.
% 2.81/0.99  --inst_passive_queue_type               priority_queues
% 2.81/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.81/0.99  --inst_passive_queues_freq              [25;2]
% 2.81/0.99  --inst_dismatching                      true
% 2.81/0.99  --inst_eager_unprocessed_to_passive     true
% 2.81/0.99  --inst_prop_sim_given                   true
% 2.81/0.99  --inst_prop_sim_new                     false
% 2.81/0.99  --inst_subs_new                         false
% 2.81/0.99  --inst_eq_res_simp                      false
% 2.81/0.99  --inst_subs_given                       false
% 2.81/0.99  --inst_orphan_elimination               true
% 2.81/0.99  --inst_learning_loop_flag               true
% 2.81/0.99  --inst_learning_start                   3000
% 2.81/0.99  --inst_learning_factor                  2
% 2.81/0.99  --inst_start_prop_sim_after_learn       3
% 2.81/0.99  --inst_sel_renew                        solver
% 2.81/0.99  --inst_lit_activity_flag                true
% 2.81/0.99  --inst_restr_to_given                   false
% 2.81/0.99  --inst_activity_threshold               500
% 2.81/0.99  --inst_out_proof                        true
% 2.81/0.99  
% 2.81/0.99  ------ Resolution Options
% 2.81/0.99  
% 2.81/0.99  --resolution_flag                       false
% 2.81/0.99  --res_lit_sel                           adaptive
% 2.81/0.99  --res_lit_sel_side                      none
% 2.81/0.99  --res_ordering                          kbo
% 2.81/0.99  --res_to_prop_solver                    active
% 2.81/0.99  --res_prop_simpl_new                    false
% 2.81/0.99  --res_prop_simpl_given                  true
% 2.81/0.99  --res_passive_queue_type                priority_queues
% 2.81/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.81/0.99  --res_passive_queues_freq               [15;5]
% 2.81/0.99  --res_forward_subs                      full
% 2.81/0.99  --res_backward_subs                     full
% 2.81/0.99  --res_forward_subs_resolution           true
% 2.81/0.99  --res_backward_subs_resolution          true
% 2.81/0.99  --res_orphan_elimination                true
% 2.81/0.99  --res_time_limit                        2.
% 2.81/0.99  --res_out_proof                         true
% 2.81/0.99  
% 2.81/0.99  ------ Superposition Options
% 2.81/0.99  
% 2.81/0.99  --superposition_flag                    true
% 2.81/0.99  --sup_passive_queue_type                priority_queues
% 2.81/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.81/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.81/0.99  --demod_completeness_check              fast
% 2.81/0.99  --demod_use_ground                      true
% 2.81/0.99  --sup_to_prop_solver                    passive
% 2.81/0.99  --sup_prop_simpl_new                    true
% 2.81/0.99  --sup_prop_simpl_given                  true
% 2.81/0.99  --sup_fun_splitting                     false
% 2.81/0.99  --sup_smt_interval                      50000
% 2.81/0.99  
% 2.81/0.99  ------ Superposition Simplification Setup
% 2.81/0.99  
% 2.81/0.99  --sup_indices_passive                   []
% 2.81/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.81/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.81/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.81/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.81/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.81/0.99  --sup_full_bw                           [BwDemod]
% 2.81/0.99  --sup_immed_triv                        [TrivRules]
% 2.81/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.81/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.81/0.99  --sup_immed_bw_main                     []
% 2.81/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.81/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.81/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.81/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.81/0.99  
% 2.81/0.99  ------ Combination Options
% 2.81/0.99  
% 2.81/0.99  --comb_res_mult                         3
% 2.81/0.99  --comb_sup_mult                         2
% 2.81/0.99  --comb_inst_mult                        10
% 2.81/0.99  
% 2.81/0.99  ------ Debug Options
% 2.81/0.99  
% 2.81/0.99  --dbg_backtrace                         false
% 2.81/0.99  --dbg_dump_prop_clauses                 false
% 2.81/0.99  --dbg_dump_prop_clauses_file            -
% 2.81/0.99  --dbg_out_stat                          false
% 2.81/0.99  
% 2.81/0.99  
% 2.81/0.99  
% 2.81/0.99  
% 2.81/0.99  ------ Proving...
% 2.81/0.99  
% 2.81/0.99  
% 2.81/0.99  % SZS status Theorem for theBenchmark.p
% 2.81/0.99  
% 2.81/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.81/0.99  
% 2.81/0.99  fof(f5,axiom,(
% 2.81/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 2.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/0.99  
% 2.81/0.99  fof(f22,plain,(
% 2.81/0.99    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 2.81/0.99    inference(ennf_transformation,[],[f5])).
% 2.81/0.99  
% 2.81/0.99  fof(f23,plain,(
% 2.81/0.99    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 2.81/0.99    inference(flattening,[],[f22])).
% 2.81/0.99  
% 2.81/0.99  fof(f42,plain,(
% 2.81/0.99    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 2.81/0.99    inference(nnf_transformation,[],[f23])).
% 2.81/0.99  
% 2.81/0.99  fof(f61,plain,(
% 2.81/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 2.81/0.99    inference(cnf_transformation,[],[f42])).
% 2.81/0.99  
% 2.81/0.99  fof(f7,axiom,(
% 2.81/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(X2)) => (k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))))))))),
% 2.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/0.99  
% 2.81/0.99  fof(f26,plain,(
% 2.81/0.99    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : ((r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.81/0.99    inference(ennf_transformation,[],[f7])).
% 2.81/0.99  
% 2.81/0.99  fof(f27,plain,(
% 2.81/0.99    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.81/0.99    inference(flattening,[],[f26])).
% 2.81/0.99  
% 2.81/0.99  fof(f47,plain,(
% 2.81/0.99    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | ? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.81/0.99    inference(nnf_transformation,[],[f27])).
% 2.81/0.99  
% 2.81/0.99  fof(f48,plain,(
% 2.81/0.99    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | ? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.81/0.99    inference(rectify,[],[f47])).
% 2.81/0.99  
% 2.81/0.99  fof(f49,plain,(
% 2.81/0.99    ! [X2,X1,X0] : (? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2))) & u1_struct_0(X1) = sK1(X0,X1,X2) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.81/0.99    introduced(choice_axiom,[])).
% 2.81/0.99  
% 2.81/0.99  fof(f50,plain,(
% 2.81/0.99    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2))) & u1_struct_0(X1) = sK1(X0,X1,X2) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.81/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f48,f49])).
% 2.81/0.99  
% 2.81/0.99  fof(f67,plain,(
% 2.81/0.99    ( ! [X4,X2,X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k9_tmap_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.81/0.99    inference(cnf_transformation,[],[f50])).
% 2.81/0.99  
% 2.81/0.99  fof(f99,plain,(
% 2.81/0.99    ( ! [X2,X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),X2,k7_tmap_1(X0,u1_struct_0(X1))) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k9_tmap_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.81/0.99    inference(equality_resolution,[],[f67])).
% 2.81/0.99  
% 2.81/0.99  fof(f100,plain,(
% 2.81/0.99    ( ! [X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1))) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.81/0.99    inference(equality_resolution,[],[f99])).
% 2.81/0.99  
% 2.81/0.99  fof(f11,axiom,(
% 2.81/0.99    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))))),
% 2.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/0.99  
% 2.81/0.99  fof(f33,plain,(
% 2.81/0.99    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.81/0.99    inference(ennf_transformation,[],[f11])).
% 2.81/0.99  
% 2.81/0.99  fof(f34,plain,(
% 2.81/0.99    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.81/0.99    inference(flattening,[],[f33])).
% 2.81/0.99  
% 2.81/0.99  fof(f80,plain,(
% 2.81/0.99    ( ! [X0,X1] : (v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.81/0.99    inference(cnf_transformation,[],[f34])).
% 2.81/0.99  
% 2.81/0.99  fof(f81,plain,(
% 2.81/0.99    ( ! [X0,X1] : (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.81/0.99    inference(cnf_transformation,[],[f34])).
% 2.81/0.99  
% 2.81/0.99  fof(f15,conjecture,(
% 2.81/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3))))))),
% 2.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/0.99  
% 2.81/0.99  fof(f16,negated_conjecture,(
% 2.81/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3))))))),
% 2.81/0.99    inference(negated_conjecture,[],[f15])).
% 2.81/0.99  
% 2.81/0.99  fof(f40,plain,(
% 2.81/0.99    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (~r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_tsep_1(X1,X2)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.81/0.99    inference(ennf_transformation,[],[f16])).
% 2.81/0.99  
% 2.81/0.99  fof(f41,plain,(
% 2.81/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.81/0.99    inference(flattening,[],[f40])).
% 2.81/0.99  
% 2.81/0.99  fof(f55,plain,(
% 2.81/0.99    ( ! [X2,X0,X1] : (? [X3] : (~r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) => (~r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),sK5) & m1_subset_1(sK5,u1_struct_0(X2)))) )),
% 2.81/0.99    introduced(choice_axiom,[])).
% 2.81/0.99  
% 2.81/0.99  fof(f54,plain,(
% 2.81/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (~r1_tmap_1(sK4,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),sK4),X3) & m1_subset_1(X3,u1_struct_0(sK4))) & r1_tsep_1(X1,sK4) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 2.81/0.99    introduced(choice_axiom,[])).
% 2.81/0.99  
% 2.81/0.99  fof(f53,plain,(
% 2.81/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~r1_tmap_1(X2,k8_tmap_1(X0,sK3),k2_tmap_1(X0,k8_tmap_1(X0,sK3),k9_tmap_1(X0,sK3),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_tsep_1(sK3,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 2.81/0.99    introduced(choice_axiom,[])).
% 2.81/0.99  
% 2.81/0.99  fof(f52,plain,(
% 2.81/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k8_tmap_1(sK2,X1),k2_tmap_1(sK2,k8_tmap_1(sK2,X1),k9_tmap_1(sK2,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_tsep_1(X1,X2) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK2) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 2.81/0.99    introduced(choice_axiom,[])).
% 2.81/0.99  
% 2.81/0.99  fof(f56,plain,(
% 2.81/0.99    (((~r1_tmap_1(sK4,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),sK5) & m1_subset_1(sK5,u1_struct_0(sK4))) & r1_tsep_1(sK3,sK4) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK2) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 2.81/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f41,f55,f54,f53,f52])).
% 2.81/0.99  
% 2.81/0.99  fof(f90,plain,(
% 2.81/0.99    m1_pre_topc(sK3,sK2)),
% 2.81/0.99    inference(cnf_transformation,[],[f56])).
% 2.81/0.99  
% 2.81/0.99  fof(f86,plain,(
% 2.81/0.99    ~v2_struct_0(sK2)),
% 2.81/0.99    inference(cnf_transformation,[],[f56])).
% 2.81/0.99  
% 2.81/0.99  fof(f87,plain,(
% 2.81/0.99    v2_pre_topc(sK2)),
% 2.81/0.99    inference(cnf_transformation,[],[f56])).
% 2.81/0.99  
% 2.81/0.99  fof(f88,plain,(
% 2.81/0.99    l1_pre_topc(sK2)),
% 2.81/0.99    inference(cnf_transformation,[],[f56])).
% 2.81/0.99  
% 2.81/0.99  fof(f14,axiom,(
% 2.81/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/0.99  
% 2.81/0.99  fof(f39,plain,(
% 2.81/0.99    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.81/0.99    inference(ennf_transformation,[],[f14])).
% 2.81/0.99  
% 2.81/0.99  fof(f85,plain,(
% 2.81/0.99    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.81/0.99    inference(cnf_transformation,[],[f39])).
% 2.81/0.99  
% 2.81/0.99  fof(f79,plain,(
% 2.81/0.99    ( ! [X0,X1] : (v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.81/0.99    inference(cnf_transformation,[],[f34])).
% 2.81/0.99  
% 2.81/0.99  fof(f6,axiom,(
% 2.81/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & v1_pre_topc(X2)) => (k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => k6_tmap_1(X0,X3) = X2))))))),
% 2.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/0.99  
% 2.81/0.99  fof(f24,plain,(
% 2.81/0.99    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : ((k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.81/0.99    inference(ennf_transformation,[],[f6])).
% 2.81/0.99  
% 2.81/0.99  fof(f25,plain,(
% 2.81/0.99    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.81/0.99    inference(flattening,[],[f24])).
% 2.81/0.99  
% 2.81/0.99  fof(f43,plain,(
% 2.81/0.99    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.81/0.99    inference(nnf_transformation,[],[f25])).
% 2.81/0.99  
% 2.81/0.99  fof(f44,plain,(
% 2.81/0.99    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.81/0.99    inference(rectify,[],[f43])).
% 2.81/0.99  
% 2.81/0.99  fof(f45,plain,(
% 2.81/0.99    ! [X2,X1,X0] : (? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (k6_tmap_1(X0,sK0(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK0(X0,X1,X2) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.81/0.99    introduced(choice_axiom,[])).
% 2.81/0.99  
% 2.81/0.99  fof(f46,plain,(
% 2.81/0.99    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | (k6_tmap_1(X0,sK0(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK0(X0,X1,X2) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.81/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f44,f45])).
% 2.81/0.99  
% 2.81/0.99  fof(f63,plain,(
% 2.81/0.99    ( ! [X4,X2,X0,X1] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.81/0.99    inference(cnf_transformation,[],[f46])).
% 2.81/0.99  
% 2.81/0.99  fof(f97,plain,(
% 2.81/0.99    ( ! [X2,X0,X1] : (k6_tmap_1(X0,u1_struct_0(X1)) = X2 | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.81/0.99    inference(equality_resolution,[],[f63])).
% 2.81/0.99  
% 2.81/0.99  fof(f98,plain,(
% 2.81/0.99    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.81/0.99    inference(equality_resolution,[],[f97])).
% 2.81/0.99  
% 2.81/0.99  fof(f10,axiom,(
% 2.81/0.99    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 2.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/0.99  
% 2.81/0.99  fof(f31,plain,(
% 2.81/0.99    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.81/0.99    inference(ennf_transformation,[],[f10])).
% 2.81/0.99  
% 2.81/0.99  fof(f32,plain,(
% 2.81/0.99    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.81/0.99    inference(flattening,[],[f31])).
% 2.81/0.99  
% 2.81/0.99  fof(f76,plain,(
% 2.81/0.99    ( ! [X0,X1] : (v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.81/0.99    inference(cnf_transformation,[],[f32])).
% 2.81/0.99  
% 2.81/0.99  fof(f77,plain,(
% 2.81/0.99    ( ! [X0,X1] : (v2_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.81/0.99    inference(cnf_transformation,[],[f32])).
% 2.81/0.99  
% 2.81/0.99  fof(f78,plain,(
% 2.81/0.99    ( ! [X0,X1] : (l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.81/0.99    inference(cnf_transformation,[],[f32])).
% 2.81/0.99  
% 2.81/0.99  fof(f8,axiom,(
% 2.81/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 2.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/0.99  
% 2.81/0.99  fof(f28,plain,(
% 2.81/0.99    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 2.81/0.99    inference(ennf_transformation,[],[f8])).
% 2.81/0.99  
% 2.81/0.99  fof(f51,plain,(
% 2.81/0.99    ! [X0] : (! [X1] : (((r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) & (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 2.81/0.99    inference(nnf_transformation,[],[f28])).
% 2.81/0.99  
% 2.81/0.99  fof(f71,plain,(
% 2.81/0.99    ( ! [X0,X1] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 2.81/0.99    inference(cnf_transformation,[],[f51])).
% 2.81/0.99  
% 2.81/0.99  fof(f93,plain,(
% 2.81/0.99    r1_tsep_1(sK3,sK4)),
% 2.81/0.99    inference(cnf_transformation,[],[f56])).
% 2.81/0.99  
% 2.81/0.99  fof(f2,axiom,(
% 2.81/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/0.99  
% 2.81/0.99  fof(f18,plain,(
% 2.81/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.81/0.99    inference(ennf_transformation,[],[f2])).
% 2.81/0.99  
% 2.81/0.99  fof(f58,plain,(
% 2.81/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.81/0.99    inference(cnf_transformation,[],[f18])).
% 2.81/0.99  
% 2.81/0.99  fof(f3,axiom,(
% 2.81/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/0.99  
% 2.81/0.99  fof(f19,plain,(
% 2.81/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.81/0.99    inference(ennf_transformation,[],[f3])).
% 2.81/0.99  
% 2.81/0.99  fof(f59,plain,(
% 2.81/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.81/0.99    inference(cnf_transformation,[],[f19])).
% 2.81/0.99  
% 2.81/0.99  fof(f92,plain,(
% 2.81/0.99    m1_pre_topc(sK4,sK2)),
% 2.81/0.99    inference(cnf_transformation,[],[f56])).
% 2.81/0.99  
% 2.81/0.99  fof(f9,axiom,(
% 2.81/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 2.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/0.99  
% 2.81/0.99  fof(f29,plain,(
% 2.81/0.99    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.81/0.99    inference(ennf_transformation,[],[f9])).
% 2.81/0.99  
% 2.81/0.99  fof(f30,plain,(
% 2.81/0.99    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.81/0.99    inference(flattening,[],[f29])).
% 2.81/0.99  
% 2.81/0.99  fof(f73,plain,(
% 2.81/0.99    ( ! [X0,X1] : (v1_funct_1(k7_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.81/0.99    inference(cnf_transformation,[],[f30])).
% 2.81/0.99  
% 2.81/0.99  fof(f1,axiom,(
% 2.81/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 2.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/0.99  
% 2.81/0.99  fof(f17,plain,(
% 2.81/0.99    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 2.81/0.99    inference(ennf_transformation,[],[f1])).
% 2.81/0.99  
% 2.81/0.99  fof(f57,plain,(
% 2.81/0.99    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 2.81/0.99    inference(cnf_transformation,[],[f17])).
% 2.81/0.99  
% 2.81/0.99  fof(f13,axiom,(
% 2.81/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_xboole_0(u1_struct_0(X2),X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3))))))),
% 2.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/0.99  
% 2.81/0.99  fof(f37,plain,(
% 2.81/0.99    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : (r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2))) | ~r1_xboole_0(u1_struct_0(X2),X1)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.81/0.99    inference(ennf_transformation,[],[f13])).
% 2.81/0.99  
% 2.81/0.99  fof(f38,plain,(
% 2.81/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2))) | ~r1_xboole_0(u1_struct_0(X2),X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.81/0.99    inference(flattening,[],[f37])).
% 2.81/0.99  
% 2.81/0.99  fof(f84,plain,(
% 2.81/0.99    ( ! [X2,X0,X3,X1] : (r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~r1_xboole_0(u1_struct_0(X2),X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.81/0.99    inference(cnf_transformation,[],[f38])).
% 2.81/0.99  
% 2.81/0.99  fof(f95,plain,(
% 2.81/0.99    ~r1_tmap_1(sK4,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),sK5)),
% 2.81/0.99    inference(cnf_transformation,[],[f56])).
% 2.81/0.99  
% 2.81/0.99  fof(f91,plain,(
% 2.81/0.99    ~v2_struct_0(sK4)),
% 2.81/0.99    inference(cnf_transformation,[],[f56])).
% 2.81/0.99  
% 2.81/0.99  fof(f94,plain,(
% 2.81/0.99    m1_subset_1(sK5,u1_struct_0(sK4))),
% 2.81/0.99    inference(cnf_transformation,[],[f56])).
% 2.81/0.99  
% 2.81/0.99  fof(f12,axiom,(
% 2.81/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 2.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/0.99  
% 2.81/0.99  fof(f35,plain,(
% 2.81/0.99    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.81/0.99    inference(ennf_transformation,[],[f12])).
% 2.81/0.99  
% 2.81/0.99  fof(f36,plain,(
% 2.81/0.99    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.81/0.99    inference(flattening,[],[f35])).
% 2.81/0.99  
% 2.81/0.99  fof(f82,plain,(
% 2.81/0.99    ( ! [X0,X1] : (u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.81/0.99    inference(cnf_transformation,[],[f36])).
% 2.81/0.99  
% 2.81/0.99  fof(f4,axiom,(
% 2.81/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/0.99  
% 2.81/0.99  fof(f20,plain,(
% 2.81/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.81/0.99    inference(ennf_transformation,[],[f4])).
% 2.81/0.99  
% 2.81/0.99  fof(f21,plain,(
% 2.81/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.81/0.99    inference(flattening,[],[f20])).
% 2.81/0.99  
% 2.81/0.99  fof(f60,plain,(
% 2.81/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.81/0.99    inference(cnf_transformation,[],[f21])).
% 2.81/0.99  
% 2.81/0.99  fof(f75,plain,(
% 2.81/0.99    ( ! [X0,X1] : (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.81/0.99    inference(cnf_transformation,[],[f30])).
% 2.81/0.99  
% 2.81/0.99  fof(f74,plain,(
% 2.81/0.99    ( ! [X0,X1] : (v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.81/0.99    inference(cnf_transformation,[],[f30])).
% 2.81/0.99  
% 2.81/0.99  cnf(c_5,plain,
% 2.81/0.99      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
% 2.81/0.99      | ~ v1_funct_2(X5,X2,X3)
% 2.81/0.99      | ~ v1_funct_2(X4,X0,X1)
% 2.81/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.81/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.81/0.99      | ~ v1_funct_1(X5)
% 2.81/0.99      | ~ v1_funct_1(X4)
% 2.81/0.99      | v1_xboole_0(X1)
% 2.81/0.99      | v1_xboole_0(X3)
% 2.81/0.99      | X4 = X5 ),
% 2.81/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_13,plain,
% 2.81/0.99      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
% 2.81/0.99      | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 2.81/0.99      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 2.81/0.99      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
% 2.81/0.99      | ~ m1_pre_topc(X1,X0)
% 2.81/0.99      | ~ v2_pre_topc(X0)
% 2.81/0.99      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 2.81/0.99      | v2_struct_0(X0)
% 2.81/0.99      | ~ l1_pre_topc(X0) ),
% 2.81/0.99      inference(cnf_transformation,[],[f100]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_23,plain,
% 2.81/0.99      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 2.81/0.99      | ~ m1_pre_topc(X1,X0)
% 2.81/0.99      | ~ v2_pre_topc(X0)
% 2.81/0.99      | v2_struct_0(X0)
% 2.81/0.99      | ~ l1_pre_topc(X0) ),
% 2.81/0.99      inference(cnf_transformation,[],[f80]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_22,plain,
% 2.81/0.99      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 2.81/0.99      | ~ m1_pre_topc(X1,X0)
% 2.81/0.99      | ~ v2_pre_topc(X0)
% 2.81/0.99      | v2_struct_0(X0)
% 2.81/0.99      | ~ l1_pre_topc(X0) ),
% 2.81/0.99      inference(cnf_transformation,[],[f81]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_236,plain,
% 2.81/0.99      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
% 2.81/0.99      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
% 2.81/0.99      | ~ m1_pre_topc(X1,X0)
% 2.81/0.99      | ~ v2_pre_topc(X0)
% 2.81/0.99      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 2.81/0.99      | v2_struct_0(X0)
% 2.81/0.99      | ~ l1_pre_topc(X0) ),
% 2.81/0.99      inference(global_propositional_subsumption,
% 2.81/0.99                [status(thm)],
% 2.81/0.99                [c_13,c_23,c_22]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_34,negated_conjecture,
% 2.81/0.99      ( m1_pre_topc(sK3,sK2) ),
% 2.81/0.99      inference(cnf_transformation,[],[f90]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1169,plain,
% 2.81/0.99      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
% 2.81/0.99      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
% 2.81/0.99      | ~ v2_pre_topc(X0)
% 2.81/0.99      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 2.81/0.99      | v2_struct_0(X0)
% 2.81/0.99      | ~ l1_pre_topc(X0)
% 2.81/0.99      | sK3 != X1
% 2.81/0.99      | sK2 != X0 ),
% 2.81/0.99      inference(resolution_lifted,[status(thm)],[c_236,c_34]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1170,plain,
% 2.81/0.99      ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))),k9_tmap_1(sK2,sK3),k7_tmap_1(sK2,u1_struct_0(sK3)))
% 2.81/0.99      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.81/0.99      | ~ v2_pre_topc(sK2)
% 2.81/0.99      | ~ v1_funct_1(k9_tmap_1(sK2,sK3))
% 2.81/0.99      | v2_struct_0(sK2)
% 2.81/0.99      | ~ l1_pre_topc(sK2) ),
% 2.81/0.99      inference(unflattening,[status(thm)],[c_1169]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_38,negated_conjecture,
% 2.81/0.99      ( ~ v2_struct_0(sK2) ),
% 2.81/0.99      inference(cnf_transformation,[],[f86]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_37,negated_conjecture,
% 2.81/0.99      ( v2_pre_topc(sK2) ),
% 2.81/0.99      inference(cnf_transformation,[],[f87]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_36,negated_conjecture,
% 2.81/0.99      ( l1_pre_topc(sK2) ),
% 2.81/0.99      inference(cnf_transformation,[],[f88]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_28,plain,
% 2.81/0.99      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.81/0.99      | ~ m1_pre_topc(X0,X1)
% 2.81/0.99      | ~ l1_pre_topc(X1) ),
% 2.81/0.99      inference(cnf_transformation,[],[f85]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_962,plain,
% 2.81/0.99      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.81/0.99      | ~ l1_pre_topc(X1)
% 2.81/0.99      | sK3 != X0
% 2.81/0.99      | sK2 != X1 ),
% 2.81/0.99      inference(resolution_lifted,[status(thm)],[c_28,c_34]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_963,plain,
% 2.81/0.99      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.81/0.99      | ~ l1_pre_topc(sK2) ),
% 2.81/0.99      inference(unflattening,[status(thm)],[c_962]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_24,plain,
% 2.81/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.81/0.99      | ~ v2_pre_topc(X1)
% 2.81/0.99      | v1_funct_1(k9_tmap_1(X1,X0))
% 2.81/0.99      | v2_struct_0(X1)
% 2.81/0.99      | ~ l1_pre_topc(X1) ),
% 2.81/0.99      inference(cnf_transformation,[],[f79]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_973,plain,
% 2.81/0.99      ( ~ v2_pre_topc(X0)
% 2.81/0.99      | v1_funct_1(k9_tmap_1(X0,X1))
% 2.81/0.99      | v2_struct_0(X0)
% 2.81/0.99      | ~ l1_pre_topc(X0)
% 2.81/0.99      | sK3 != X1
% 2.81/0.99      | sK2 != X0 ),
% 2.81/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_34]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_974,plain,
% 2.81/0.99      ( ~ v2_pre_topc(sK2)
% 2.81/0.99      | v1_funct_1(k9_tmap_1(sK2,sK3))
% 2.81/0.99      | v2_struct_0(sK2)
% 2.81/0.99      | ~ l1_pre_topc(sK2) ),
% 2.81/0.99      inference(unflattening,[status(thm)],[c_973]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1172,plain,
% 2.81/0.99      ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))),k9_tmap_1(sK2,sK3),k7_tmap_1(sK2,u1_struct_0(sK3))) ),
% 2.81/0.99      inference(global_propositional_subsumption,
% 2.81/0.99                [status(thm)],
% 2.81/0.99                [c_1170,c_38,c_37,c_36,c_963,c_974]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_2747,plain,
% 2.81/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.81/0.99      | ~ v1_funct_2(X3,X4,X5)
% 2.81/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.81/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.81/0.99      | ~ v1_funct_1(X0)
% 2.81/0.99      | ~ v1_funct_1(X3)
% 2.81/0.99      | v1_xboole_0(X5)
% 2.81/0.99      | v1_xboole_0(X2)
% 2.81/0.99      | X3 = X0
% 2.81/0.99      | k7_tmap_1(sK2,u1_struct_0(sK3)) != X3
% 2.81/0.99      | k9_tmap_1(sK2,sK3) != X0
% 2.81/0.99      | u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))) != X5
% 2.81/0.99      | u1_struct_0(k8_tmap_1(sK2,sK3)) != X2
% 2.81/0.99      | u1_struct_0(sK2) != X4
% 2.81/0.99      | u1_struct_0(sK2) != X1 ),
% 2.81/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_1172]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_2748,plain,
% 2.81/0.99      ( ~ v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
% 2.81/0.99      | ~ v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 2.81/0.99      | ~ m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))))
% 2.81/0.99      | ~ m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 2.81/0.99      | ~ v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3)))
% 2.81/0.99      | ~ v1_funct_1(k9_tmap_1(sK2,sK3))
% 2.81/0.99      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
% 2.81/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
% 2.81/0.99      | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3) ),
% 2.81/0.99      inference(unflattening,[status(thm)],[c_2747]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1180,plain,
% 2.81/0.99      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 2.81/0.99      | ~ v2_pre_topc(X0)
% 2.81/0.99      | v2_struct_0(X0)
% 2.81/0.99      | ~ l1_pre_topc(X0)
% 2.81/0.99      | sK3 != X1
% 2.81/0.99      | sK2 != X0 ),
% 2.81/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_34]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1181,plain,
% 2.81/0.99      ( v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 2.81/0.99      | ~ v2_pre_topc(sK2)
% 2.81/0.99      | v2_struct_0(sK2)
% 2.81/0.99      | ~ l1_pre_topc(sK2) ),
% 2.81/0.99      inference(unflattening,[status(thm)],[c_1180]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1191,plain,
% 2.81/0.99      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 2.81/0.99      | ~ v2_pre_topc(X0)
% 2.81/0.99      | v2_struct_0(X0)
% 2.81/0.99      | ~ l1_pre_topc(X0)
% 2.81/0.99      | sK3 != X1
% 2.81/0.99      | sK2 != X0 ),
% 2.81/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_34]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1192,plain,
% 2.81/0.99      ( m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 2.81/0.99      | ~ v2_pre_topc(sK2)
% 2.81/0.99      | v2_struct_0(sK2)
% 2.81/0.99      | ~ l1_pre_topc(sK2) ),
% 2.81/0.99      inference(unflattening,[status(thm)],[c_1191]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_2750,plain,
% 2.81/0.99      ( ~ v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3)))
% 2.81/0.99      | ~ v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
% 2.81/0.99      | ~ m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))))
% 2.81/0.99      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
% 2.81/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
% 2.81/0.99      | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3) ),
% 2.81/0.99      inference(global_propositional_subsumption,
% 2.81/0.99                [status(thm)],
% 2.81/0.99                [c_2748,c_38,c_37,c_36,c_974,c_1181,c_1192]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_2751,plain,
% 2.81/0.99      ( ~ v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
% 2.81/0.99      | ~ m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))))
% 2.81/0.99      | ~ v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3)))
% 2.81/0.99      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
% 2.81/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
% 2.81/0.99      | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3) ),
% 2.81/0.99      inference(renaming,[status(thm)],[c_2750]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_3933,plain,
% 2.81/0.99      ( ~ v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
% 2.81/0.99      | ~ m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))))
% 2.81/0.99      | ~ v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3)))
% 2.81/0.99      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))))
% 2.81/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
% 2.81/0.99      | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3) ),
% 2.81/0.99      inference(subtyping,[status(esa)],[c_2751]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_4853,plain,
% 2.81/0.99      ( k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3)
% 2.81/0.99      | v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))) != iProver_top
% 2.81/0.99      | m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))))) != iProver_top
% 2.81/0.99      | v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3))) != iProver_top
% 2.81/0.99      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))) = iProver_top
% 2.81/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3))) = iProver_top ),
% 2.81/0.99      inference(predicate_to_equality,[status(thm)],[c_3933]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_9,plain,
% 2.81/0.99      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.81/0.99      | ~ m1_pre_topc(X0,X1)
% 2.81/0.99      | ~ v1_pre_topc(k8_tmap_1(X1,X0))
% 2.81/0.99      | ~ v2_pre_topc(X1)
% 2.81/0.99      | ~ v2_pre_topc(k8_tmap_1(X1,X0))
% 2.81/0.99      | v2_struct_0(X1)
% 2.81/0.99      | ~ l1_pre_topc(X1)
% 2.81/0.99      | ~ l1_pre_topc(k8_tmap_1(X1,X0))
% 2.81/0.99      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 2.81/0.99      inference(cnf_transformation,[],[f98]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_21,plain,
% 2.81/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.81/0.99      | v1_pre_topc(k8_tmap_1(X1,X0))
% 2.81/0.99      | ~ v2_pre_topc(X1)
% 2.81/0.99      | v2_struct_0(X1)
% 2.81/0.99      | ~ l1_pre_topc(X1) ),
% 2.81/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_20,plain,
% 2.81/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.81/0.99      | ~ v2_pre_topc(X1)
% 2.81/0.99      | v2_pre_topc(k8_tmap_1(X1,X0))
% 2.81/0.99      | v2_struct_0(X1)
% 2.81/0.99      | ~ l1_pre_topc(X1) ),
% 2.81/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_19,plain,
% 2.81/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.81/0.99      | ~ v2_pre_topc(X1)
% 2.81/0.99      | v2_struct_0(X1)
% 2.81/0.99      | ~ l1_pre_topc(X1)
% 2.81/0.99      | l1_pre_topc(k8_tmap_1(X1,X0)) ),
% 2.81/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_246,plain,
% 2.81/0.99      ( ~ l1_pre_topc(X1)
% 2.81/0.99      | v2_struct_0(X1)
% 2.81/0.99      | ~ m1_pre_topc(X0,X1)
% 2.81/0.99      | ~ v2_pre_topc(X1)
% 2.81/0.99      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 2.81/0.99      inference(global_propositional_subsumption,
% 2.81/0.99                [status(thm)],
% 2.81/0.99                [c_9,c_28,c_21,c_20,c_19]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_247,plain,
% 2.81/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.81/0.99      | ~ v2_pre_topc(X1)
% 2.81/0.99      | v2_struct_0(X1)
% 2.81/0.99      | ~ l1_pre_topc(X1)
% 2.81/0.99      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 2.81/0.99      inference(renaming,[status(thm)],[c_246]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_954,plain,
% 2.81/0.99      ( ~ v2_pre_topc(X0)
% 2.81/0.99      | v2_struct_0(X0)
% 2.81/0.99      | ~ l1_pre_topc(X0)
% 2.81/0.99      | k6_tmap_1(X0,u1_struct_0(X1)) = k8_tmap_1(X0,X1)
% 2.81/0.99      | sK3 != X1
% 2.81/0.99      | sK2 != X0 ),
% 2.81/0.99      inference(resolution_lifted,[status(thm)],[c_247,c_34]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_955,plain,
% 2.81/0.99      ( ~ v2_pre_topc(sK2)
% 2.81/0.99      | v2_struct_0(sK2)
% 2.81/0.99      | ~ l1_pre_topc(sK2)
% 2.81/0.99      | k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
% 2.81/0.99      inference(unflattening,[status(thm)],[c_954]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_957,plain,
% 2.81/0.99      ( k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
% 2.81/0.99      inference(global_propositional_subsumption,
% 2.81/0.99                [status(thm)],
% 2.81/0.99                [c_955,c_38,c_37,c_36]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_3975,plain,
% 2.81/0.99      ( k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
% 2.81/0.99      inference(subtyping,[status(esa)],[c_957]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_5067,plain,
% 2.81/0.99      ( k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3)
% 2.81/0.99      | v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
% 2.81/0.99      | m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top
% 2.81/0.99      | v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3))) != iProver_top
% 2.81/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3))) = iProver_top ),
% 2.81/0.99      inference(light_normalisation,[status(thm)],[c_4853,c_3975]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_41,plain,
% 2.81/0.99      ( l1_pre_topc(sK2) = iProver_top ),
% 2.81/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_15,plain,
% 2.81/0.99      ( ~ r1_tsep_1(X0,X1)
% 2.81/0.99      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
% 2.81/0.99      | ~ l1_struct_0(X0)
% 2.81/0.99      | ~ l1_struct_0(X1) ),
% 2.81/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_31,negated_conjecture,
% 2.81/0.99      ( r1_tsep_1(sK3,sK4) ),
% 2.81/0.99      inference(cnf_transformation,[],[f93]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_490,plain,
% 2.81/0.99      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
% 2.81/0.99      | ~ l1_struct_0(X1)
% 2.81/0.99      | ~ l1_struct_0(X0)
% 2.81/0.99      | sK3 != X0
% 2.81/0.99      | sK4 != X1 ),
% 2.81/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_31]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_491,plain,
% 2.81/0.99      ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4))
% 2.81/0.99      | ~ l1_struct_0(sK3)
% 2.81/0.99      | ~ l1_struct_0(sK4) ),
% 2.81/0.99      inference(unflattening,[status(thm)],[c_490]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_964,plain,
% 2.81/0.99      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 2.81/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 2.81/0.99      inference(predicate_to_equality,[status(thm)],[c_963]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1,plain,
% 2.81/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.81/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_2,plain,
% 2.81/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.81/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_32,negated_conjecture,
% 2.81/0.99      ( m1_pre_topc(sK4,sK2) ),
% 2.81/0.99      inference(cnf_transformation,[],[f92]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_943,plain,
% 2.81/0.99      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK2 != X0 | sK4 != X1 ),
% 2.81/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_32]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_944,plain,
% 2.81/0.99      ( ~ l1_pre_topc(sK2) | l1_pre_topc(sK4) ),
% 2.81/0.99      inference(unflattening,[status(thm)],[c_943]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_946,plain,
% 2.81/0.99      ( l1_pre_topc(sK4) ),
% 2.81/0.99      inference(global_propositional_subsumption,
% 2.81/0.99                [status(thm)],
% 2.81/0.99                [c_944,c_36]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1977,plain,
% 2.81/0.99      ( l1_struct_0(X0) | sK4 != X0 ),
% 2.81/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_946]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1978,plain,
% 2.81/0.99      ( l1_struct_0(sK4) ),
% 2.81/0.99      inference(unflattening,[status(thm)],[c_1977]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1071,plain,
% 2.81/0.99      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK3 != X1 | sK2 != X0 ),
% 2.81/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_34]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1072,plain,
% 2.81/0.99      ( l1_pre_topc(sK3) | ~ l1_pre_topc(sK2) ),
% 2.81/0.99      inference(unflattening,[status(thm)],[c_1071]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1074,plain,
% 2.81/0.99      ( l1_pre_topc(sK3) ),
% 2.81/0.99      inference(global_propositional_subsumption,
% 2.81/0.99                [status(thm)],
% 2.81/0.99                [c_1072,c_36]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1991,plain,
% 2.81/0.99      ( l1_struct_0(X0) | sK3 != X0 ),
% 2.81/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_1074]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1992,plain,
% 2.81/0.99      ( l1_struct_0(sK3) ),
% 2.81/0.99      inference(unflattening,[status(thm)],[c_1991]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_3986,plain,( X0_59 = X0_59 ),theory(equality) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_4031,plain,
% 2.81/0.99      ( sK2 = sK2 ),
% 2.81/0.99      inference(instantiation,[status(thm)],[c_3986]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_18,plain,
% 2.81/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.81/0.99      | ~ v2_pre_topc(X1)
% 2.81/0.99      | v1_funct_1(k7_tmap_1(X1,X0))
% 2.81/0.99      | v2_struct_0(X1)
% 2.81/0.99      | ~ l1_pre_topc(X1) ),
% 2.81/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1644,plain,
% 2.81/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.81/0.99      | v1_funct_1(k7_tmap_1(X1,X0))
% 2.81/0.99      | v2_struct_0(X1)
% 2.81/0.99      | ~ l1_pre_topc(X1)
% 2.81/0.99      | sK2 != X1 ),
% 2.81/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_37]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1645,plain,
% 2.81/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.81/0.99      | v1_funct_1(k7_tmap_1(sK2,X0))
% 2.81/0.99      | v2_struct_0(sK2)
% 2.81/0.99      | ~ l1_pre_topc(sK2) ),
% 2.81/0.99      inference(unflattening,[status(thm)],[c_1644]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1649,plain,
% 2.81/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.81/0.99      | v1_funct_1(k7_tmap_1(sK2,X0)) ),
% 2.81/0.99      inference(global_propositional_subsumption,
% 2.81/0.99                [status(thm)],
% 2.81/0.99                [c_1645,c_38,c_36]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_3955,plain,
% 2.81/0.99      ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.81/0.99      | v1_funct_1(k7_tmap_1(sK2,X0_58)) ),
% 2.81/0.99      inference(subtyping,[status(esa)],[c_1649]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_5244,plain,
% 2.81/0.99      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.81/0.99      | v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3))) ),
% 2.81/0.99      inference(instantiation,[status(thm)],[c_3955]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_5245,plain,
% 2.81/0.99      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.81/0.99      | v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3))) = iProver_top ),
% 2.81/0.99      inference(predicate_to_equality,[status(thm)],[c_5244]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_0,plain,
% 2.81/0.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 2.81/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_3983,plain,
% 2.81/0.99      ( ~ r1_xboole_0(X0_58,X1_58) | r1_xboole_0(X1_58,X0_58) ),
% 2.81/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_5341,plain,
% 2.81/0.99      ( ~ r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4))
% 2.81/0.99      | r1_xboole_0(u1_struct_0(sK4),u1_struct_0(sK3)) ),
% 2.81/0.99      inference(instantiation,[status(thm)],[c_3983]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_5908,plain,
% 2.81/0.99      ( sK4 = sK4 ),
% 2.81/0.99      inference(instantiation,[status(thm)],[c_3986]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_27,plain,
% 2.81/0.99      ( r1_tmap_1(X0,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X0),X3)
% 2.81/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.81/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.81/0.99      | ~ m1_pre_topc(X0,X1)
% 2.81/0.99      | ~ r1_xboole_0(u1_struct_0(X0),X2)
% 2.81/0.99      | ~ v2_pre_topc(X1)
% 2.81/0.99      | v2_struct_0(X1)
% 2.81/0.99      | v2_struct_0(X0)
% 2.81/0.99      | ~ l1_pre_topc(X1) ),
% 2.81/0.99      inference(cnf_transformation,[],[f84]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_29,negated_conjecture,
% 2.81/0.99      ( ~ r1_tmap_1(sK4,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),sK5) ),
% 2.81/0.99      inference(cnf_transformation,[],[f95]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_444,plain,
% 2.81/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.81/0.99      | ~ m1_subset_1(X2,u1_struct_0(X3))
% 2.81/0.99      | ~ m1_pre_topc(X3,X1)
% 2.81/0.99      | ~ r1_xboole_0(u1_struct_0(X3),X0)
% 2.81/0.99      | ~ v2_pre_topc(X1)
% 2.81/0.99      | v2_struct_0(X1)
% 2.81/0.99      | v2_struct_0(X3)
% 2.81/0.99      | ~ l1_pre_topc(X1)
% 2.81/0.99      | k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),X3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
% 2.81/0.99      | k6_tmap_1(X1,X0) != k8_tmap_1(sK2,sK3)
% 2.81/0.99      | sK5 != X2
% 2.81/0.99      | sK4 != X3 ),
% 2.81/0.99      inference(resolution_lifted,[status(thm)],[c_27,c_29]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_445,plain,
% 2.81/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.81/0.99      | ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 2.81/0.99      | ~ m1_pre_topc(sK4,X1)
% 2.81/0.99      | ~ r1_xboole_0(u1_struct_0(sK4),X0)
% 2.81/0.99      | ~ v2_pre_topc(X1)
% 2.81/0.99      | v2_struct_0(X1)
% 2.81/0.99      | v2_struct_0(sK4)
% 2.81/0.99      | ~ l1_pre_topc(X1)
% 2.81/0.99      | k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
% 2.81/0.99      | k6_tmap_1(X1,X0) != k8_tmap_1(sK2,sK3) ),
% 2.81/0.99      inference(unflattening,[status(thm)],[c_444]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_33,negated_conjecture,
% 2.81/0.99      ( ~ v2_struct_0(sK4) ),
% 2.81/0.99      inference(cnf_transformation,[],[f91]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_30,negated_conjecture,
% 2.81/0.99      ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 2.81/0.99      inference(cnf_transformation,[],[f94]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_449,plain,
% 2.81/0.99      ( v2_struct_0(X1)
% 2.81/0.99      | ~ v2_pre_topc(X1)
% 2.81/0.99      | ~ r1_xboole_0(u1_struct_0(sK4),X0)
% 2.81/0.99      | ~ m1_pre_topc(sK4,X1)
% 2.81/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.81/0.99      | ~ l1_pre_topc(X1)
% 2.81/0.99      | k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
% 2.81/0.99      | k6_tmap_1(X1,X0) != k8_tmap_1(sK2,sK3) ),
% 2.81/0.99      inference(global_propositional_subsumption,
% 2.81/0.99                [status(thm)],
% 2.81/0.99                [c_445,c_33,c_30]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_450,plain,
% 2.81/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.81/0.99      | ~ m1_pre_topc(sK4,X1)
% 2.81/0.99      | ~ r1_xboole_0(u1_struct_0(sK4),X0)
% 2.81/0.99      | ~ v2_pre_topc(X1)
% 2.81/0.99      | v2_struct_0(X1)
% 2.81/0.99      | ~ l1_pre_topc(X1)
% 2.81/0.99      | k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
% 2.81/0.99      | k6_tmap_1(X1,X0) != k8_tmap_1(sK2,sK3) ),
% 2.81/0.99      inference(renaming,[status(thm)],[c_449]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1364,plain,
% 2.81/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.81/0.99      | ~ r1_xboole_0(u1_struct_0(sK4),X0)
% 2.81/0.99      | ~ v2_pre_topc(X1)
% 2.81/0.99      | v2_struct_0(X1)
% 2.81/0.99      | ~ l1_pre_topc(X1)
% 2.81/0.99      | k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
% 2.81/0.99      | k6_tmap_1(X1,X0) != k8_tmap_1(sK2,sK3)
% 2.81/0.99      | sK2 != X1
% 2.81/0.99      | sK4 != sK4 ),
% 2.81/0.99      inference(resolution_lifted,[status(thm)],[c_32,c_450]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1365,plain,
% 2.81/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.81/0.99      | ~ r1_xboole_0(u1_struct_0(sK4),X0)
% 2.81/0.99      | ~ v2_pre_topc(sK2)
% 2.81/0.99      | v2_struct_0(sK2)
% 2.81/0.99      | ~ l1_pre_topc(sK2)
% 2.81/0.99      | k2_tmap_1(sK2,k6_tmap_1(sK2,X0),k7_tmap_1(sK2,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
% 2.81/0.99      | k6_tmap_1(sK2,X0) != k8_tmap_1(sK2,sK3) ),
% 2.81/0.99      inference(unflattening,[status(thm)],[c_1364]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1369,plain,
% 2.81/0.99      ( ~ r1_xboole_0(u1_struct_0(sK4),X0)
% 2.81/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.81/0.99      | k2_tmap_1(sK2,k6_tmap_1(sK2,X0),k7_tmap_1(sK2,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
% 2.81/0.99      | k6_tmap_1(sK2,X0) != k8_tmap_1(sK2,sK3) ),
% 2.81/0.99      inference(global_propositional_subsumption,
% 2.81/0.99                [status(thm)],
% 2.81/0.99                [c_1365,c_38,c_37,c_36]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1370,plain,
% 2.81/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.81/0.99      | ~ r1_xboole_0(u1_struct_0(sK4),X0)
% 2.81/0.99      | k2_tmap_1(sK2,k6_tmap_1(sK2,X0),k7_tmap_1(sK2,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
% 2.81/0.99      | k6_tmap_1(sK2,X0) != k8_tmap_1(sK2,sK3) ),
% 2.81/0.99      inference(renaming,[status(thm)],[c_1369]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_3964,plain,
% 2.81/0.99      ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.81/0.99      | ~ r1_xboole_0(u1_struct_0(sK4),X0_58)
% 2.81/0.99      | k2_tmap_1(sK2,k6_tmap_1(sK2,X0_58),k7_tmap_1(sK2,X0_58),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
% 2.81/0.99      | k6_tmap_1(sK2,X0_58) != k8_tmap_1(sK2,sK3) ),
% 2.81/0.99      inference(subtyping,[status(esa)],[c_1370]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_6023,plain,
% 2.81/0.99      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.81/0.99      | ~ r1_xboole_0(u1_struct_0(sK4),u1_struct_0(sK3))
% 2.81/0.99      | k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(sK3)),k7_tmap_1(sK2,u1_struct_0(sK3)),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
% 2.81/0.99      | k6_tmap_1(sK2,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3) ),
% 2.81/0.99      inference(instantiation,[status(thm)],[c_3964]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_4010,plain,
% 2.81/0.99      ( k2_tmap_1(X0_59,X1_59,X0_58,X2_59) = k2_tmap_1(X3_59,X4_59,X1_58,X5_59)
% 2.81/0.99      | X0_59 != X3_59
% 2.81/0.99      | X1_59 != X4_59
% 2.81/0.99      | X2_59 != X5_59
% 2.81/0.99      | X0_58 != X1_58 ),
% 2.81/0.99      theory(equality) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_6054,plain,
% 2.81/0.99      ( k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(sK3)),k7_tmap_1(sK2,u1_struct_0(sK3)),sK4) = k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
% 2.81/0.99      | k6_tmap_1(sK2,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3)
% 2.81/0.99      | sK2 != sK2
% 2.81/0.99      | sK4 != sK4
% 2.81/0.99      | k7_tmap_1(sK2,u1_struct_0(sK3)) != k9_tmap_1(sK2,sK3) ),
% 2.81/0.99      inference(instantiation,[status(thm)],[c_4010]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_6301,plain,
% 2.81/0.99      ( m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top
% 2.81/0.99      | v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
% 2.81/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3))) = iProver_top ),
% 2.81/0.99      inference(global_propositional_subsumption,
% 2.81/0.99                [status(thm)],
% 2.81/0.99                [c_5067,c_36,c_41,c_491,c_963,c_964,c_1978,c_1992,c_4031,
% 2.81/0.99                 c_3975,c_5245,c_5341,c_5908,c_6023,c_6054]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_6302,plain,
% 2.81/0.99      ( v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
% 2.81/0.99      | m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top
% 2.81/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3))) = iProver_top ),
% 2.81/0.99      inference(renaming,[status(thm)],[c_6301]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_965,plain,
% 2.81/0.99      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.81/0.99      inference(global_propositional_subsumption,
% 2.81/0.99                [status(thm)],
% 2.81/0.99                [c_963,c_36]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_3974,plain,
% 2.81/0.99      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.81/0.99      inference(subtyping,[status(esa)],[c_965]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_4816,plain,
% 2.81/0.99      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.81/0.99      inference(predicate_to_equality,[status(thm)],[c_3974]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_26,plain,
% 2.81/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.81/0.99      | ~ v2_pre_topc(X1)
% 2.81/0.99      | v2_struct_0(X1)
% 2.81/0.99      | ~ l1_pre_topc(X1)
% 2.81/0.99      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
% 2.81/0.99      inference(cnf_transformation,[],[f82]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1608,plain,
% 2.81/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.81/0.99      | v2_struct_0(X1)
% 2.81/0.99      | ~ l1_pre_topc(X1)
% 2.81/0.99      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1)
% 2.81/0.99      | sK2 != X1 ),
% 2.81/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_37]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1609,plain,
% 2.81/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.81/0.99      | v2_struct_0(sK2)
% 2.81/0.99      | ~ l1_pre_topc(sK2)
% 2.81/0.99      | u1_struct_0(k6_tmap_1(sK2,X0)) = u1_struct_0(sK2) ),
% 2.81/0.99      inference(unflattening,[status(thm)],[c_1608]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1613,plain,
% 2.81/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.81/0.99      | u1_struct_0(k6_tmap_1(sK2,X0)) = u1_struct_0(sK2) ),
% 2.81/0.99      inference(global_propositional_subsumption,
% 2.81/0.99                [status(thm)],
% 2.81/0.99                [c_1609,c_38,c_36]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_3957,plain,
% 2.81/0.99      ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.81/0.99      | u1_struct_0(k6_tmap_1(sK2,X0_58)) = u1_struct_0(sK2) ),
% 2.81/0.99      inference(subtyping,[status(esa)],[c_1613]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_4829,plain,
% 2.81/0.99      ( u1_struct_0(k6_tmap_1(sK2,X0_58)) = u1_struct_0(sK2)
% 2.81/0.99      | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.81/0.99      inference(predicate_to_equality,[status(thm)],[c_3957]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_5639,plain,
% 2.81/0.99      ( u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))) = u1_struct_0(sK2) ),
% 2.81/0.99      inference(superposition,[status(thm)],[c_4816,c_4829]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_5641,plain,
% 2.81/0.99      ( u1_struct_0(k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2) ),
% 2.81/0.99      inference(light_normalisation,[status(thm)],[c_5639,c_3975]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_6305,plain,
% 2.81/0.99      ( v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 2.81/0.99      | m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 2.81/0.99      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 2.81/0.99      inference(light_normalisation,[status(thm)],[c_6302,c_5641]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_3,plain,
% 2.81/0.99      ( v2_struct_0(X0)
% 2.81/0.99      | ~ v1_xboole_0(u1_struct_0(X0))
% 2.81/0.99      | ~ l1_struct_0(X0) ),
% 2.81/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1963,plain,
% 2.81/0.99      ( l1_struct_0(X0) | sK2 != X0 ),
% 2.81/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_36]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1964,plain,
% 2.81/0.99      ( l1_struct_0(sK2) ),
% 2.81/0.99      inference(unflattening,[status(thm)],[c_1963]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_2012,plain,
% 2.81/0.99      ( v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK2 != X0 ),
% 2.81/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_1964]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_2013,plain,
% 2.81/0.99      ( v2_struct_0(sK2) | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 2.81/0.99      inference(unflattening,[status(thm)],[c_2012]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_125,plain,
% 2.81/0.99      ( v2_struct_0(sK2)
% 2.81/0.99      | ~ v1_xboole_0(u1_struct_0(sK2))
% 2.81/0.99      | ~ l1_struct_0(sK2) ),
% 2.81/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_129,plain,
% 2.81/0.99      ( ~ l1_pre_topc(sK2) | l1_struct_0(sK2) ),
% 2.81/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_2015,plain,
% 2.81/0.99      ( ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 2.81/0.99      inference(global_propositional_subsumption,
% 2.81/0.99                [status(thm)],
% 2.81/0.99                [c_2013,c_38,c_36,c_125,c_129]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_3941,plain,
% 2.81/0.99      ( ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 2.81/0.99      inference(subtyping,[status(esa)],[c_2015]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_4845,plain,
% 2.81/0.99      ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 2.81/0.99      inference(predicate_to_equality,[status(thm)],[c_3941]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_6309,plain,
% 2.81/0.99      ( v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 2.81/0.99      | m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top ),
% 2.81/0.99      inference(forward_subsumption_resolution,
% 2.81/0.99                [status(thm)],
% 2.81/0.99                [c_6305,c_4845]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_16,plain,
% 2.81/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.81/0.99      | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
% 2.81/0.99      | ~ v2_pre_topc(X1)
% 2.81/0.99      | v2_struct_0(X1)
% 2.81/0.99      | ~ l1_pre_topc(X1) ),
% 2.81/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1662,plain,
% 2.81/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.81/0.99      | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
% 2.81/0.99      | v2_struct_0(X1)
% 2.81/0.99      | ~ l1_pre_topc(X1)
% 2.81/0.99      | sK2 != X1 ),
% 2.81/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_37]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1663,plain,
% 2.81/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.81/0.99      | m1_subset_1(k7_tmap_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0)))))
% 2.81/0.99      | v2_struct_0(sK2)
% 2.81/0.99      | ~ l1_pre_topc(sK2) ),
% 2.81/0.99      inference(unflattening,[status(thm)],[c_1662]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1667,plain,
% 2.81/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.81/0.99      | m1_subset_1(k7_tmap_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0))))) ),
% 2.81/0.99      inference(global_propositional_subsumption,
% 2.81/0.99                [status(thm)],
% 2.81/0.99                [c_1663,c_38,c_36]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_3954,plain,
% 2.81/0.99      ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.81/0.99      | m1_subset_1(k7_tmap_1(sK2,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0_58))))) ),
% 2.81/0.99      inference(subtyping,[status(esa)],[c_1667]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_4832,plain,
% 2.81/0.99      ( m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.81/0.99      | m1_subset_1(k7_tmap_1(sK2,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0_58))))) = iProver_top ),
% 2.81/0.99      inference(predicate_to_equality,[status(thm)],[c_3954]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_6092,plain,
% 2.81/0.99      ( m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) = iProver_top
% 2.81/0.99      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.81/0.99      inference(superposition,[status(thm)],[c_3975,c_4832]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_6095,plain,
% 2.81/0.99      ( m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) = iProver_top
% 2.81/0.99      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.81/0.99      inference(light_normalisation,[status(thm)],[c_6092,c_5641]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_17,plain,
% 2.81/0.99      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
% 2.81/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.81/0.99      | ~ v2_pre_topc(X0)
% 2.81/0.99      | v2_struct_0(X0)
% 2.81/0.99      | ~ l1_pre_topc(X0) ),
% 2.81/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1848,plain,
% 2.81/0.99      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
% 2.81/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.81/0.99      | v2_struct_0(X0)
% 2.81/0.99      | ~ l1_pre_topc(X0)
% 2.81/0.99      | sK2 != X0 ),
% 2.81/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_37]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1849,plain,
% 2.81/0.99      ( v1_funct_2(k7_tmap_1(sK2,X0),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0)))
% 2.81/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.81/0.99      | v2_struct_0(sK2)
% 2.81/0.99      | ~ l1_pre_topc(sK2) ),
% 2.81/0.99      inference(unflattening,[status(thm)],[c_1848]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1853,plain,
% 2.81/0.99      ( v1_funct_2(k7_tmap_1(sK2,X0),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0)))
% 2.81/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.81/0.99      inference(global_propositional_subsumption,
% 2.81/0.99                [status(thm)],
% 2.81/0.99                [c_1849,c_38,c_36]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_3945,plain,
% 2.81/0.99      ( v1_funct_2(k7_tmap_1(sK2,X0_58),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0_58)))
% 2.81/0.99      | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.81/0.99      inference(subtyping,[status(esa)],[c_1853]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_4841,plain,
% 2.81/0.99      ( v1_funct_2(k7_tmap_1(sK2,X0_58),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0_58))) = iProver_top
% 2.81/0.99      | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.81/0.99      inference(predicate_to_equality,[status(thm)],[c_3945]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_6075,plain,
% 2.81/0.99      ( v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) = iProver_top
% 2.81/0.99      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.81/0.99      inference(superposition,[status(thm)],[c_3975,c_4841]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_6078,plain,
% 2.81/0.99      ( v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(sK2)) = iProver_top
% 2.81/0.99      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.81/0.99      inference(light_normalisation,[status(thm)],[c_6075,c_5641]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(contradiction,plain,
% 2.81/0.99      ( $false ),
% 2.81/0.99      inference(minisat,[status(thm)],[c_6309,c_6095,c_6078,c_964,c_41]) ).
% 2.81/0.99  
% 2.81/0.99  
% 2.81/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.81/0.99  
% 2.81/0.99  ------                               Statistics
% 2.81/0.99  
% 2.81/0.99  ------ General
% 2.81/0.99  
% 2.81/0.99  abstr_ref_over_cycles:                  0
% 2.81/0.99  abstr_ref_under_cycles:                 0
% 2.81/0.99  gc_basic_clause_elim:                   0
% 2.81/0.99  forced_gc_time:                         0
% 2.81/0.99  parsing_time:                           0.015
% 2.81/0.99  unif_index_cands_time:                  0.
% 2.81/0.99  unif_index_add_time:                    0.
% 2.81/0.99  orderings_time:                         0.
% 2.81/0.99  out_proof_time:                         0.013
% 2.81/0.99  total_time:                             0.22
% 2.81/0.99  num_of_symbols:                         68
% 2.81/0.99  num_of_terms:                           5538
% 2.81/0.99  
% 2.81/0.99  ------ Preprocessing
% 2.81/0.99  
% 2.81/0.99  num_of_splits:                          0
% 2.81/0.99  num_of_split_atoms:                     0
% 2.81/0.99  num_of_reused_defs:                     0
% 2.81/0.99  num_eq_ax_congr_red:                    12
% 2.81/0.99  num_of_sem_filtered_clauses:            8
% 2.81/0.99  num_of_subtypes:                        4
% 2.81/0.99  monotx_restored_types:                  0
% 2.81/0.99  sat_num_of_epr_types:                   0
% 2.81/0.99  sat_num_of_non_cyclic_types:            0
% 2.81/0.99  sat_guarded_non_collapsed_types:        1
% 2.81/0.99  num_pure_diseq_elim:                    0
% 2.81/0.99  simp_replaced_by:                       0
% 2.81/0.99  res_preprocessed:                       191
% 2.81/0.99  prep_upred:                             0
% 2.81/0.99  prep_unflattend:                        190
% 2.81/0.99  smt_new_axioms:                         0
% 2.81/0.99  pred_elim_cands:                        14
% 2.81/0.99  pred_elim:                              8
% 2.81/0.99  pred_elim_cl:                           -14
% 2.81/0.99  pred_elim_cycles:                       12
% 2.81/0.99  merged_defs:                            0
% 2.81/0.99  merged_defs_ncl:                        0
% 2.81/0.99  bin_hyper_res:                          0
% 2.81/0.99  prep_cycles:                            3
% 2.81/0.99  pred_elim_time:                         0.094
% 2.81/0.99  splitting_time:                         0.
% 2.81/0.99  sem_filter_time:                        0.
% 2.81/0.99  monotx_time:                            0.
% 2.81/0.99  subtype_inf_time:                       0.
% 2.81/0.99  
% 2.81/0.99  ------ Problem properties
% 2.81/0.99  
% 2.81/0.99  clauses:                                53
% 2.81/0.99  conjectures:                            4
% 2.81/0.99  epr:                                    4
% 2.81/0.99  horn:                                   31
% 2.81/0.99  ground:                                 30
% 2.81/0.99  unary:                                  18
% 2.81/0.99  binary:                                 14
% 2.81/0.99  lits:                                   142
% 2.81/0.99  lits_eq:                                40
% 2.81/0.99  fd_pure:                                0
% 2.81/0.99  fd_pseudo:                              0
% 2.81/0.99  fd_cond:                                6
% 2.81/0.99  fd_pseudo_cond:                         0
% 2.81/0.99  ac_symbols:                             0
% 2.81/0.99  
% 2.81/0.99  ------ Propositional Solver
% 2.81/0.99  
% 2.81/0.99  prop_solver_calls:                      21
% 2.81/0.99  prop_fast_solver_calls:                 2262
% 2.81/0.99  smt_solver_calls:                       0
% 2.81/0.99  smt_fast_solver_calls:                  0
% 2.81/0.99  prop_num_of_clauses:                    1509
% 2.81/0.99  prop_preprocess_simplified:             5622
% 2.81/0.99  prop_fo_subsumed:                       161
% 2.81/0.99  prop_solver_time:                       0.
% 2.81/0.99  smt_solver_time:                        0.
% 2.81/0.99  smt_fast_solver_time:                   0.
% 2.81/0.99  prop_fast_solver_time:                  0.
% 2.81/0.99  prop_unsat_core_time:                   0.
% 2.81/0.99  
% 2.81/0.99  ------ QBF
% 2.81/0.99  
% 2.81/0.99  qbf_q_res:                              0
% 2.81/0.99  qbf_num_tautologies:                    0
% 2.81/0.99  qbf_prep_cycles:                        0
% 2.81/0.99  
% 2.81/0.99  ------ BMC1
% 2.81/0.99  
% 2.81/0.99  bmc1_current_bound:                     -1
% 2.81/0.99  bmc1_last_solved_bound:                 -1
% 2.81/0.99  bmc1_unsat_core_size:                   -1
% 2.81/0.99  bmc1_unsat_core_parents_size:           -1
% 2.81/0.99  bmc1_merge_next_fun:                    0
% 2.81/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.81/0.99  
% 2.81/0.99  ------ Instantiation
% 2.81/0.99  
% 2.81/0.99  inst_num_of_clauses:                    258
% 2.81/0.99  inst_num_in_passive:                    45
% 2.81/0.99  inst_num_in_active:                     182
% 2.81/0.99  inst_num_in_unprocessed:                31
% 2.81/0.99  inst_num_of_loops:                      200
% 2.81/0.99  inst_num_of_learning_restarts:          0
% 2.81/0.99  inst_num_moves_active_passive:          16
% 2.81/0.99  inst_lit_activity:                      0
% 2.81/0.99  inst_lit_activity_moves:                0
% 2.81/0.99  inst_num_tautologies:                   0
% 2.81/0.99  inst_num_prop_implied:                  0
% 2.81/0.99  inst_num_existing_simplified:           0
% 2.81/0.99  inst_num_eq_res_simplified:             0
% 2.81/0.99  inst_num_child_elim:                    0
% 2.81/0.99  inst_num_of_dismatching_blockings:      8
% 2.81/0.99  inst_num_of_non_proper_insts:           168
% 2.81/0.99  inst_num_of_duplicates:                 0
% 2.81/0.99  inst_inst_num_from_inst_to_res:         0
% 2.81/0.99  inst_dismatching_checking_time:         0.
% 2.81/0.99  
% 2.81/0.99  ------ Resolution
% 2.81/0.99  
% 2.81/0.99  res_num_of_clauses:                     0
% 2.81/0.99  res_num_in_passive:                     0
% 2.81/0.99  res_num_in_active:                      0
% 2.81/0.99  res_num_of_loops:                       194
% 2.81/0.99  res_forward_subset_subsumed:            29
% 2.81/0.99  res_backward_subset_subsumed:           0
% 2.81/0.99  res_forward_subsumed:                   1
% 2.81/0.99  res_backward_subsumed:                  0
% 2.81/0.99  res_forward_subsumption_resolution:     12
% 2.81/0.99  res_backward_subsumption_resolution:    2
% 2.81/0.99  res_clause_to_clause_subsumption:       504
% 2.81/0.99  res_orphan_elimination:                 0
% 2.81/0.99  res_tautology_del:                      45
% 2.81/0.99  res_num_eq_res_simplified:              0
% 2.81/0.99  res_num_sel_changes:                    0
% 2.81/0.99  res_moves_from_active_to_pass:          0
% 2.81/0.99  
% 2.81/0.99  ------ Superposition
% 2.81/0.99  
% 2.81/0.99  sup_time_total:                         0.
% 2.81/0.99  sup_time_generating:                    0.
% 2.81/0.99  sup_time_sim_full:                      0.
% 2.81/0.99  sup_time_sim_immed:                     0.
% 2.81/0.99  
% 2.81/0.99  sup_num_of_clauses:                     61
% 2.81/0.99  sup_num_in_active:                      30
% 2.81/0.99  sup_num_in_passive:                     31
% 2.81/0.99  sup_num_of_loops:                       38
% 2.81/0.99  sup_fw_superposition:                   11
% 2.81/0.99  sup_bw_superposition:                   5
% 2.81/0.99  sup_immediate_simplified:               16
% 2.81/0.99  sup_given_eliminated:                   0
% 2.81/0.99  comparisons_done:                       0
% 2.81/0.99  comparisons_avoided:                    4
% 2.81/0.99  
% 2.81/0.99  ------ Simplifications
% 2.81/0.99  
% 2.81/0.99  
% 2.81/0.99  sim_fw_subset_subsumed:                 4
% 2.81/0.99  sim_bw_subset_subsumed:                 0
% 2.81/0.99  sim_fw_subsumed:                        0
% 2.81/0.99  sim_bw_subsumed:                        0
% 2.81/0.99  sim_fw_subsumption_res:                 2
% 2.81/0.99  sim_bw_subsumption_res:                 0
% 2.81/0.99  sim_tautology_del:                      2
% 2.81/0.99  sim_eq_tautology_del:                   0
% 2.81/0.99  sim_eq_res_simp:                        0
% 2.81/0.99  sim_fw_demodulated:                     0
% 2.81/0.99  sim_bw_demodulated:                     8
% 2.81/0.99  sim_light_normalised:                   18
% 2.81/0.99  sim_joinable_taut:                      0
% 2.81/0.99  sim_joinable_simp:                      0
% 2.81/0.99  sim_ac_normalised:                      0
% 2.81/0.99  sim_smt_subsumption:                    0
% 2.81/0.99  
%------------------------------------------------------------------------------
