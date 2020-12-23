%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:57 EST 2020

% Result     : Theorem 1.10s
% Output     : CNFRefutation 1.10s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 350 expanded)
%              Number of clauses        :   63 (  76 expanded)
%              Number of leaves         :   19 ( 117 expanded)
%              Depth                    :   13
%              Number of atoms          :  694 (2478 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal clause size      :   18 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f44])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

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

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_hidden(X1,k1_connsp_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_connsp_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

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

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

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

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

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

fof(f69,plain,(
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

fof(f79,plain,(
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
    inference(equality_resolution,[],[f69])).

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

fof(f18,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f62,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f6,axiom,(
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

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

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
    inference(ennf_transformation,[],[f15])).

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

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
          & m1_subset_1(X3,u1_struct_0(X2)) )
     => ( ~ r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),sK4)
        & m1_subset_1(sK4,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
              & m1_subset_1(X3,u1_struct_0(X2)) )
          & r1_xboole_0(u1_struct_0(X2),X1)
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ~ r1_tmap_1(sK3,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),sK3),X3)
            & m1_subset_1(X3,u1_struct_0(sK3)) )
        & r1_xboole_0(u1_struct_0(sK3),X1)
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
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
                ( ~ r1_tmap_1(X2,k6_tmap_1(X0,sK2),k2_tmap_1(X0,k6_tmap_1(X0,sK2),k7_tmap_1(X0,sK2),X2),X3)
                & m1_subset_1(X3,u1_struct_0(X2)) )
            & r1_xboole_0(u1_struct_0(X2),sK2)
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
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
                  ( ~ r1_tmap_1(X2,k6_tmap_1(sK1,X1),k2_tmap_1(sK1,k6_tmap_1(sK1,X1),k7_tmap_1(sK1,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
              & r1_xboole_0(u1_struct_0(X2),X1)
              & m1_pre_topc(X2,sK1)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ~ r1_tmap_1(sK3,k6_tmap_1(sK1,sK2),k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),sK4)
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & r1_xboole_0(u1_struct_0(sK3),sK2)
    & m1_pre_topc(sK3,sK1)
    & ~ v2_struct_0(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f43,f49,f48,f47,f46])).

fof(f75,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f70,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f71,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f72,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f74,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f57,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f78,plain,(
    ~ r1_tmap_1(sK3,k6_tmap_1(sK1,sK2),k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f77,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f50])).

fof(f76,plain,(
    r1_xboole_0(u1_struct_0(sK3),sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f73,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_700,plain,
    ( r2_hidden(sK0(X0_52,X1_52),X1_52)
    | r1_xboole_0(X0_52,X1_52) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_977,plain,
    ( r2_hidden(sK0(X0_52,k1_connsp_2(sK3,sK4)),k1_connsp_2(sK3,sK4))
    | r1_xboole_0(X0_52,k1_connsp_2(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_700])).

cnf(c_983,plain,
    ( r2_hidden(sK0(sK2,k1_connsp_2(sK3,sK4)),k1_connsp_2(sK3,sK4))
    | r1_xboole_0(sK2,k1_connsp_2(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_977])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_697,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(X1_52))
    | ~ r2_hidden(X2_52,X0_52)
    | ~ v1_xboole_0(X1_52) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_868,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1_52,X0_52)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_697])).

cnf(c_941,plain,
    ( ~ m1_subset_1(k1_connsp_2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0_52,k1_connsp_2(sK3,sK4))
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_868])).

cnf(c_976,plain,
    ( ~ m1_subset_1(k1_connsp_2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(sK0(X0_52,k1_connsp_2(sK3,sK4)),k1_connsp_2(sK3,sK4))
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_941])).

cnf(c_979,plain,
    ( ~ m1_subset_1(k1_connsp_2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(sK0(sK2,k1_connsp_2(sK3,sK4)),k1_connsp_2(sK3,sK4))
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_976])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_701,plain,
    ( ~ r2_hidden(X0_52,X1_52)
    | ~ r2_hidden(X0_52,X2_52)
    | ~ r1_xboole_0(X2_52,X1_52) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_886,plain,
    ( ~ r2_hidden(sK4,X0_52)
    | ~ r2_hidden(sK4,X1_52)
    | ~ r1_xboole_0(X1_52,X0_52) ),
    inference(instantiation,[status(thm)],[c_701])).

cnf(c_913,plain,
    ( ~ r2_hidden(sK4,u1_struct_0(sK3))
    | ~ r2_hidden(sK4,sK2)
    | ~ r1_xboole_0(u1_struct_0(sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_886])).

cnf(c_878,plain,
    ( ~ r2_hidden(sK4,X0_52)
    | ~ r2_hidden(sK4,k1_connsp_2(sK3,sK4))
    | ~ r1_xboole_0(X0_52,k1_connsp_2(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_701])).

cnf(c_880,plain,
    ( ~ r2_hidden(sK4,k1_connsp_2(sK3,sK4))
    | ~ r2_hidden(sK4,sK2)
    | ~ r1_xboole_0(sK2,k1_connsp_2(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_878])).

cnf(c_17,plain,
    ( r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(X2,X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_690,plain,
    ( r1_tmap_1(X0_51,k6_tmap_1(X0_51,X0_52),k7_tmap_1(X0_51,X0_52),X1_52)
    | ~ m1_subset_1(X1_52,u1_struct_0(X0_51))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51)))
    | r2_hidden(X1_52,X0_52)
    | v2_struct_0(X0_51)
    | ~ l1_pre_topc(X0_51)
    | ~ v2_pre_topc(X0_51) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_854,plain,
    ( r1_tmap_1(sK1,k6_tmap_1(sK1,X0_52),k7_tmap_1(sK1,X0_52),sK4)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | r2_hidden(sK4,X0_52)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_690])).

cnf(c_856,plain,
    ( r1_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(sK4,sK2)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_854])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_696,plain,
    ( ~ m1_subset_1(X0_52,u1_struct_0(X0_51))
    | m1_subset_1(k1_connsp_2(X0_51,X0_52),k1_zfmisc_1(u1_struct_0(X0_51)))
    | v2_struct_0(X0_51)
    | ~ l1_pre_topc(X0_51)
    | ~ v2_pre_topc(X0_51) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_841,plain,
    ( m1_subset_1(k1_connsp_2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_696])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | r2_hidden(X0,k1_connsp_2(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_695,plain,
    ( ~ m1_subset_1(X0_52,u1_struct_0(X0_51))
    | r2_hidden(X0_52,k1_connsp_2(X0_51,X0_52))
    | v2_struct_0(X0_51)
    | ~ l1_pre_topc(X0_51)
    | ~ v2_pre_topc(X0_51) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_838,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | r2_hidden(sK4,k1_connsp_2(sK3,sK4))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_695])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_698,plain,
    ( ~ m1_subset_1(X0_52,X1_52)
    | r2_hidden(X0_52,X1_52)
    | v1_xboole_0(X1_52) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_832,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | r2_hidden(sK4,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_698])).

cnf(c_13,plain,
    ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_18,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_342,plain,
    ( r1_tmap_1(X0,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X0),X3)
    | ~ r1_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))
    | ~ v1_funct_1(k7_tmap_1(X1,X2))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(k6_tmap_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(k6_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(k6_tmap_1(X1,X2)) ),
    inference(resolution,[status(thm)],[c_13,c_18])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k6_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k6_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k6_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_funct_1(k7_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_376,plain,
    ( r1_tmap_1(X0,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X0),X3)
    | ~ r1_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_342,c_11,c_10,c_16,c_14,c_12,c_7])).

cnf(c_22,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_399,plain,
    ( ~ r1_tmap_1(sK1,k6_tmap_1(sK1,X0),k7_tmap_1(sK1,X0),X1)
    | r1_tmap_1(sK3,k6_tmap_1(sK1,X0),k2_tmap_1(sK1,k6_tmap_1(sK1,X0),k7_tmap_1(sK1,X0),sK3),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(resolution,[status(thm)],[c_376,c_22])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_26,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_403,plain,
    ( ~ r1_tmap_1(sK1,k6_tmap_1(sK1,X0),k7_tmap_1(sK1,X0),X1)
    | r1_tmap_1(sK3,k6_tmap_1(sK1,X0),k2_tmap_1(sK1,k6_tmap_1(sK1,X0),k7_tmap_1(sK1,X0),sK3),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_399,c_27,c_26,c_25,c_23])).

cnf(c_681,plain,
    ( ~ r1_tmap_1(sK1,k6_tmap_1(sK1,X0_52),k7_tmap_1(sK1,X0_52),X1_52)
    | r1_tmap_1(sK3,k6_tmap_1(sK1,X0_52),k2_tmap_1(sK1,k6_tmap_1(sK1,X0_52),k7_tmap_1(sK1,X0_52),sK3),X1_52)
    | ~ m1_subset_1(X1_52,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_403])).

cnf(c_827,plain,
    ( ~ r1_tmap_1(sK1,k6_tmap_1(sK1,X0_52),k7_tmap_1(sK1,X0_52),sK4)
    | r1_tmap_1(sK3,k6_tmap_1(sK1,X0_52),k2_tmap_1(sK1,k6_tmap_1(sK1,X0_52),k7_tmap_1(sK1,X0_52),sK3),sK4)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_681])).

cnf(c_829,plain,
    ( ~ r1_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK4)
    | r1_tmap_1(sK3,k6_tmap_1(sK1,sK2),k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_827])).

cnf(c_422,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[status(thm)],[c_7,c_22])).

cnf(c_426,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_422,c_27,c_25,c_23])).

cnf(c_427,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_426])).

cnf(c_680,plain,
    ( m1_subset_1(X0_52,u1_struct_0(sK1))
    | ~ m1_subset_1(X0_52,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_427])).

cnf(c_824,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_680])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_449,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_pre_topc(sK3) ),
    inference(resolution,[status(thm)],[c_5,c_22])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_439,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_pre_topc(sK3) ),
    inference(resolution,[status(thm)],[c_6,c_22])).

cnf(c_19,negated_conjecture,
    ( ~ r1_tmap_1(sK3,k6_tmap_1(sK1,sK2),k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),sK4) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_21,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(sK3),sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f73])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_983,c_979,c_913,c_880,c_856,c_841,c_838,c_832,c_829,c_824,c_449,c_439,c_19,c_20,c_21,c_23,c_24,c_25,c_26,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:09:29 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.20/0.34  % Running in FOF mode
% 1.10/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.10/0.99  
% 1.10/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.10/0.99  
% 1.10/0.99  ------  iProver source info
% 1.10/0.99  
% 1.10/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.10/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.10/0.99  git: non_committed_changes: false
% 1.10/0.99  git: last_make_outside_of_git: false
% 1.10/0.99  
% 1.10/0.99  ------ 
% 1.10/0.99  
% 1.10/0.99  ------ Input Options
% 1.10/0.99  
% 1.10/0.99  --out_options                           all
% 1.10/0.99  --tptp_safe_out                         true
% 1.10/0.99  --problem_path                          ""
% 1.10/0.99  --include_path                          ""
% 1.10/0.99  --clausifier                            res/vclausify_rel
% 1.10/0.99  --clausifier_options                    --mode clausify
% 1.10/0.99  --stdin                                 false
% 1.10/0.99  --stats_out                             all
% 1.10/0.99  
% 1.10/0.99  ------ General Options
% 1.10/0.99  
% 1.10/0.99  --fof                                   false
% 1.10/0.99  --time_out_real                         305.
% 1.10/0.99  --time_out_virtual                      -1.
% 1.10/0.99  --symbol_type_check                     false
% 1.10/0.99  --clausify_out                          false
% 1.10/0.99  --sig_cnt_out                           false
% 1.10/0.99  --trig_cnt_out                          false
% 1.10/0.99  --trig_cnt_out_tolerance                1.
% 1.10/0.99  --trig_cnt_out_sk_spl                   false
% 1.10/0.99  --abstr_cl_out                          false
% 1.10/0.99  
% 1.10/0.99  ------ Global Options
% 1.10/0.99  
% 1.10/0.99  --schedule                              default
% 1.10/0.99  --add_important_lit                     false
% 1.10/0.99  --prop_solver_per_cl                    1000
% 1.10/0.99  --min_unsat_core                        false
% 1.10/0.99  --soft_assumptions                      false
% 1.10/0.99  --soft_lemma_size                       3
% 1.10/0.99  --prop_impl_unit_size                   0
% 1.10/0.99  --prop_impl_unit                        []
% 1.10/0.99  --share_sel_clauses                     true
% 1.10/0.99  --reset_solvers                         false
% 1.10/0.99  --bc_imp_inh                            [conj_cone]
% 1.10/0.99  --conj_cone_tolerance                   3.
% 1.10/0.99  --extra_neg_conj                        none
% 1.10/0.99  --large_theory_mode                     true
% 1.10/0.99  --prolific_symb_bound                   200
% 1.10/0.99  --lt_threshold                          2000
% 1.10/0.99  --clause_weak_htbl                      true
% 1.10/0.99  --gc_record_bc_elim                     false
% 1.10/0.99  
% 1.10/0.99  ------ Preprocessing Options
% 1.10/0.99  
% 1.10/0.99  --preprocessing_flag                    true
% 1.10/0.99  --time_out_prep_mult                    0.1
% 1.10/0.99  --splitting_mode                        input
% 1.10/0.99  --splitting_grd                         true
% 1.10/0.99  --splitting_cvd                         false
% 1.10/0.99  --splitting_cvd_svl                     false
% 1.10/0.99  --splitting_nvd                         32
% 1.10/0.99  --sub_typing                            true
% 1.10/0.99  --prep_gs_sim                           true
% 1.10/0.99  --prep_unflatten                        true
% 1.10/0.99  --prep_res_sim                          true
% 1.10/0.99  --prep_upred                            true
% 1.10/0.99  --prep_sem_filter                       exhaustive
% 1.10/0.99  --prep_sem_filter_out                   false
% 1.10/0.99  --pred_elim                             true
% 1.10/0.99  --res_sim_input                         true
% 1.10/0.99  --eq_ax_congr_red                       true
% 1.10/0.99  --pure_diseq_elim                       true
% 1.10/0.99  --brand_transform                       false
% 1.10/0.99  --non_eq_to_eq                          false
% 1.10/0.99  --prep_def_merge                        true
% 1.10/0.99  --prep_def_merge_prop_impl              false
% 1.10/0.99  --prep_def_merge_mbd                    true
% 1.10/0.99  --prep_def_merge_tr_red                 false
% 1.10/0.99  --prep_def_merge_tr_cl                  false
% 1.10/0.99  --smt_preprocessing                     true
% 1.10/0.99  --smt_ac_axioms                         fast
% 1.10/0.99  --preprocessed_out                      false
% 1.10/0.99  --preprocessed_stats                    false
% 1.10/0.99  
% 1.10/0.99  ------ Abstraction refinement Options
% 1.10/0.99  
% 1.10/0.99  --abstr_ref                             []
% 1.10/0.99  --abstr_ref_prep                        false
% 1.10/0.99  --abstr_ref_until_sat                   false
% 1.10/0.99  --abstr_ref_sig_restrict                funpre
% 1.10/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.10/0.99  --abstr_ref_under                       []
% 1.10/0.99  
% 1.10/0.99  ------ SAT Options
% 1.10/0.99  
% 1.10/0.99  --sat_mode                              false
% 1.10/0.99  --sat_fm_restart_options                ""
% 1.10/0.99  --sat_gr_def                            false
% 1.10/0.99  --sat_epr_types                         true
% 1.10/0.99  --sat_non_cyclic_types                  false
% 1.10/0.99  --sat_finite_models                     false
% 1.10/0.99  --sat_fm_lemmas                         false
% 1.10/0.99  --sat_fm_prep                           false
% 1.10/0.99  --sat_fm_uc_incr                        true
% 1.10/0.99  --sat_out_model                         small
% 1.10/0.99  --sat_out_clauses                       false
% 1.10/0.99  
% 1.10/0.99  ------ QBF Options
% 1.10/0.99  
% 1.10/0.99  --qbf_mode                              false
% 1.10/0.99  --qbf_elim_univ                         false
% 1.10/0.99  --qbf_dom_inst                          none
% 1.10/0.99  --qbf_dom_pre_inst                      false
% 1.10/0.99  --qbf_sk_in                             false
% 1.10/0.99  --qbf_pred_elim                         true
% 1.10/0.99  --qbf_split                             512
% 1.10/0.99  
% 1.10/0.99  ------ BMC1 Options
% 1.10/0.99  
% 1.10/0.99  --bmc1_incremental                      false
% 1.10/0.99  --bmc1_axioms                           reachable_all
% 1.10/0.99  --bmc1_min_bound                        0
% 1.10/0.99  --bmc1_max_bound                        -1
% 1.10/0.99  --bmc1_max_bound_default                -1
% 1.10/0.99  --bmc1_symbol_reachability              true
% 1.10/0.99  --bmc1_property_lemmas                  false
% 1.10/0.99  --bmc1_k_induction                      false
% 1.10/0.99  --bmc1_non_equiv_states                 false
% 1.10/0.99  --bmc1_deadlock                         false
% 1.10/0.99  --bmc1_ucm                              false
% 1.10/0.99  --bmc1_add_unsat_core                   none
% 1.10/0.99  --bmc1_unsat_core_children              false
% 1.10/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.10/0.99  --bmc1_out_stat                         full
% 1.10/0.99  --bmc1_ground_init                      false
% 1.10/0.99  --bmc1_pre_inst_next_state              false
% 1.10/0.99  --bmc1_pre_inst_state                   false
% 1.10/0.99  --bmc1_pre_inst_reach_state             false
% 1.10/0.99  --bmc1_out_unsat_core                   false
% 1.10/0.99  --bmc1_aig_witness_out                  false
% 1.10/0.99  --bmc1_verbose                          false
% 1.10/0.99  --bmc1_dump_clauses_tptp                false
% 1.10/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.10/0.99  --bmc1_dump_file                        -
% 1.10/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.10/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.10/0.99  --bmc1_ucm_extend_mode                  1
% 1.10/0.99  --bmc1_ucm_init_mode                    2
% 1.10/0.99  --bmc1_ucm_cone_mode                    none
% 1.10/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.10/0.99  --bmc1_ucm_relax_model                  4
% 1.10/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.10/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.10/0.99  --bmc1_ucm_layered_model                none
% 1.10/0.99  --bmc1_ucm_max_lemma_size               10
% 1.10/0.99  
% 1.10/0.99  ------ AIG Options
% 1.10/0.99  
% 1.10/0.99  --aig_mode                              false
% 1.10/0.99  
% 1.10/0.99  ------ Instantiation Options
% 1.10/0.99  
% 1.10/0.99  --instantiation_flag                    true
% 1.10/0.99  --inst_sos_flag                         false
% 1.10/0.99  --inst_sos_phase                        true
% 1.10/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.10/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.10/0.99  --inst_lit_sel_side                     num_symb
% 1.10/0.99  --inst_solver_per_active                1400
% 1.10/0.99  --inst_solver_calls_frac                1.
% 1.10/0.99  --inst_passive_queue_type               priority_queues
% 1.10/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.10/0.99  --inst_passive_queues_freq              [25;2]
% 1.10/0.99  --inst_dismatching                      true
% 1.10/0.99  --inst_eager_unprocessed_to_passive     true
% 1.10/0.99  --inst_prop_sim_given                   true
% 1.10/0.99  --inst_prop_sim_new                     false
% 1.10/0.99  --inst_subs_new                         false
% 1.10/0.99  --inst_eq_res_simp                      false
% 1.10/0.99  --inst_subs_given                       false
% 1.10/0.99  --inst_orphan_elimination               true
% 1.10/0.99  --inst_learning_loop_flag               true
% 1.10/0.99  --inst_learning_start                   3000
% 1.10/0.99  --inst_learning_factor                  2
% 1.10/0.99  --inst_start_prop_sim_after_learn       3
% 1.10/0.99  --inst_sel_renew                        solver
% 1.10/0.99  --inst_lit_activity_flag                true
% 1.10/0.99  --inst_restr_to_given                   false
% 1.10/0.99  --inst_activity_threshold               500
% 1.10/0.99  --inst_out_proof                        true
% 1.10/0.99  
% 1.10/0.99  ------ Resolution Options
% 1.10/0.99  
% 1.10/0.99  --resolution_flag                       true
% 1.10/0.99  --res_lit_sel                           adaptive
% 1.10/0.99  --res_lit_sel_side                      none
% 1.10/0.99  --res_ordering                          kbo
% 1.10/0.99  --res_to_prop_solver                    active
% 1.10/0.99  --res_prop_simpl_new                    false
% 1.10/0.99  --res_prop_simpl_given                  true
% 1.10/0.99  --res_passive_queue_type                priority_queues
% 1.10/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.10/0.99  --res_passive_queues_freq               [15;5]
% 1.10/0.99  --res_forward_subs                      full
% 1.10/0.99  --res_backward_subs                     full
% 1.10/0.99  --res_forward_subs_resolution           true
% 1.10/0.99  --res_backward_subs_resolution          true
% 1.10/0.99  --res_orphan_elimination                true
% 1.10/0.99  --res_time_limit                        2.
% 1.10/0.99  --res_out_proof                         true
% 1.10/0.99  
% 1.10/0.99  ------ Superposition Options
% 1.10/0.99  
% 1.10/0.99  --superposition_flag                    true
% 1.10/0.99  --sup_passive_queue_type                priority_queues
% 1.10/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.10/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.10/0.99  --demod_completeness_check              fast
% 1.10/0.99  --demod_use_ground                      true
% 1.10/0.99  --sup_to_prop_solver                    passive
% 1.10/0.99  --sup_prop_simpl_new                    true
% 1.10/0.99  --sup_prop_simpl_given                  true
% 1.10/0.99  --sup_fun_splitting                     false
% 1.10/0.99  --sup_smt_interval                      50000
% 1.10/0.99  
% 1.10/0.99  ------ Superposition Simplification Setup
% 1.10/0.99  
% 1.10/0.99  --sup_indices_passive                   []
% 1.10/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.10/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.10/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.10/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.10/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.10/0.99  --sup_full_bw                           [BwDemod]
% 1.10/0.99  --sup_immed_triv                        [TrivRules]
% 1.10/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.10/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.10/0.99  --sup_immed_bw_main                     []
% 1.10/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.10/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.10/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.10/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.10/0.99  
% 1.10/0.99  ------ Combination Options
% 1.10/0.99  
% 1.10/0.99  --comb_res_mult                         3
% 1.10/0.99  --comb_sup_mult                         2
% 1.10/0.99  --comb_inst_mult                        10
% 1.10/0.99  
% 1.10/0.99  ------ Debug Options
% 1.10/0.99  
% 1.10/0.99  --dbg_backtrace                         false
% 1.10/0.99  --dbg_dump_prop_clauses                 false
% 1.10/0.99  --dbg_dump_prop_clauses_file            -
% 1.10/0.99  --dbg_out_stat                          false
% 1.10/0.99  ------ Parsing...
% 1.10/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.10/0.99  
% 1.10/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 1.10/0.99  
% 1.10/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.10/0.99  ------ Proving...
% 1.10/0.99  ------ Problem Properties 
% 1.10/0.99  
% 1.10/0.99  
% 1.10/0.99  clauses                                 24
% 1.10/0.99  conjectures                             8
% 1.10/0.99  EPR                                     8
% 1.10/0.99  Horn                                    15
% 1.10/0.99  unary                                   10
% 1.10/0.99  binary                                  3
% 1.10/0.99  lits                                    66
% 1.10/0.99  lits eq                                 0
% 1.10/0.99  fd_pure                                 0
% 1.10/0.99  fd_pseudo                               0
% 1.10/0.99  fd_cond                                 0
% 1.10/0.99  fd_pseudo_cond                          0
% 1.10/0.99  AC symbols                              0
% 1.10/0.99  
% 1.10/0.99  ------ Schedule dynamic 5 is on 
% 1.10/0.99  
% 1.10/0.99  ------ no equalities: superposition off 
% 1.10/0.99  
% 1.10/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.10/0.99  
% 1.10/0.99  
% 1.10/0.99  ------ 
% 1.10/0.99  Current options:
% 1.10/0.99  ------ 
% 1.10/0.99  
% 1.10/0.99  ------ Input Options
% 1.10/0.99  
% 1.10/0.99  --out_options                           all
% 1.10/0.99  --tptp_safe_out                         true
% 1.10/0.99  --problem_path                          ""
% 1.10/0.99  --include_path                          ""
% 1.10/0.99  --clausifier                            res/vclausify_rel
% 1.10/0.99  --clausifier_options                    --mode clausify
% 1.10/0.99  --stdin                                 false
% 1.10/0.99  --stats_out                             all
% 1.10/0.99  
% 1.10/0.99  ------ General Options
% 1.10/0.99  
% 1.10/0.99  --fof                                   false
% 1.10/0.99  --time_out_real                         305.
% 1.10/0.99  --time_out_virtual                      -1.
% 1.10/0.99  --symbol_type_check                     false
% 1.10/0.99  --clausify_out                          false
% 1.10/0.99  --sig_cnt_out                           false
% 1.10/0.99  --trig_cnt_out                          false
% 1.10/0.99  --trig_cnt_out_tolerance                1.
% 1.10/0.99  --trig_cnt_out_sk_spl                   false
% 1.10/0.99  --abstr_cl_out                          false
% 1.10/0.99  
% 1.10/0.99  ------ Global Options
% 1.10/0.99  
% 1.10/0.99  --schedule                              default
% 1.10/0.99  --add_important_lit                     false
% 1.10/0.99  --prop_solver_per_cl                    1000
% 1.10/0.99  --min_unsat_core                        false
% 1.10/0.99  --soft_assumptions                      false
% 1.10/0.99  --soft_lemma_size                       3
% 1.10/0.99  --prop_impl_unit_size                   0
% 1.10/0.99  --prop_impl_unit                        []
% 1.10/0.99  --share_sel_clauses                     true
% 1.10/0.99  --reset_solvers                         false
% 1.10/0.99  --bc_imp_inh                            [conj_cone]
% 1.10/0.99  --conj_cone_tolerance                   3.
% 1.10/0.99  --extra_neg_conj                        none
% 1.10/0.99  --large_theory_mode                     true
% 1.10/0.99  --prolific_symb_bound                   200
% 1.10/0.99  --lt_threshold                          2000
% 1.10/0.99  --clause_weak_htbl                      true
% 1.10/0.99  --gc_record_bc_elim                     false
% 1.10/0.99  
% 1.10/0.99  ------ Preprocessing Options
% 1.10/0.99  
% 1.10/0.99  --preprocessing_flag                    true
% 1.10/0.99  --time_out_prep_mult                    0.1
% 1.10/0.99  --splitting_mode                        input
% 1.10/0.99  --splitting_grd                         true
% 1.10/0.99  --splitting_cvd                         false
% 1.10/0.99  --splitting_cvd_svl                     false
% 1.10/0.99  --splitting_nvd                         32
% 1.10/0.99  --sub_typing                            true
% 1.10/0.99  --prep_gs_sim                           true
% 1.10/0.99  --prep_unflatten                        true
% 1.10/0.99  --prep_res_sim                          true
% 1.10/0.99  --prep_upred                            true
% 1.10/0.99  --prep_sem_filter                       exhaustive
% 1.10/0.99  --prep_sem_filter_out                   false
% 1.10/0.99  --pred_elim                             true
% 1.10/0.99  --res_sim_input                         true
% 1.10/1.00  --eq_ax_congr_red                       true
% 1.10/1.00  --pure_diseq_elim                       true
% 1.10/1.00  --brand_transform                       false
% 1.10/1.00  --non_eq_to_eq                          false
% 1.10/1.00  --prep_def_merge                        true
% 1.10/1.00  --prep_def_merge_prop_impl              false
% 1.10/1.00  --prep_def_merge_mbd                    true
% 1.10/1.00  --prep_def_merge_tr_red                 false
% 1.10/1.00  --prep_def_merge_tr_cl                  false
% 1.10/1.00  --smt_preprocessing                     true
% 1.10/1.00  --smt_ac_axioms                         fast
% 1.10/1.00  --preprocessed_out                      false
% 1.10/1.00  --preprocessed_stats                    false
% 1.10/1.00  
% 1.10/1.00  ------ Abstraction refinement Options
% 1.10/1.00  
% 1.10/1.00  --abstr_ref                             []
% 1.10/1.00  --abstr_ref_prep                        false
% 1.10/1.00  --abstr_ref_until_sat                   false
% 1.10/1.00  --abstr_ref_sig_restrict                funpre
% 1.10/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.10/1.00  --abstr_ref_under                       []
% 1.10/1.00  
% 1.10/1.00  ------ SAT Options
% 1.10/1.00  
% 1.10/1.00  --sat_mode                              false
% 1.10/1.00  --sat_fm_restart_options                ""
% 1.10/1.00  --sat_gr_def                            false
% 1.10/1.00  --sat_epr_types                         true
% 1.10/1.00  --sat_non_cyclic_types                  false
% 1.10/1.00  --sat_finite_models                     false
% 1.10/1.00  --sat_fm_lemmas                         false
% 1.10/1.00  --sat_fm_prep                           false
% 1.10/1.00  --sat_fm_uc_incr                        true
% 1.10/1.00  --sat_out_model                         small
% 1.10/1.00  --sat_out_clauses                       false
% 1.10/1.00  
% 1.10/1.00  ------ QBF Options
% 1.10/1.00  
% 1.10/1.00  --qbf_mode                              false
% 1.10/1.00  --qbf_elim_univ                         false
% 1.10/1.00  --qbf_dom_inst                          none
% 1.10/1.00  --qbf_dom_pre_inst                      false
% 1.10/1.00  --qbf_sk_in                             false
% 1.10/1.00  --qbf_pred_elim                         true
% 1.10/1.00  --qbf_split                             512
% 1.10/1.00  
% 1.10/1.00  ------ BMC1 Options
% 1.10/1.00  
% 1.10/1.00  --bmc1_incremental                      false
% 1.10/1.00  --bmc1_axioms                           reachable_all
% 1.10/1.00  --bmc1_min_bound                        0
% 1.10/1.00  --bmc1_max_bound                        -1
% 1.10/1.00  --bmc1_max_bound_default                -1
% 1.10/1.00  --bmc1_symbol_reachability              true
% 1.10/1.00  --bmc1_property_lemmas                  false
% 1.10/1.00  --bmc1_k_induction                      false
% 1.10/1.00  --bmc1_non_equiv_states                 false
% 1.10/1.00  --bmc1_deadlock                         false
% 1.10/1.00  --bmc1_ucm                              false
% 1.10/1.00  --bmc1_add_unsat_core                   none
% 1.10/1.00  --bmc1_unsat_core_children              false
% 1.10/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.10/1.00  --bmc1_out_stat                         full
% 1.10/1.00  --bmc1_ground_init                      false
% 1.10/1.00  --bmc1_pre_inst_next_state              false
% 1.10/1.00  --bmc1_pre_inst_state                   false
% 1.10/1.00  --bmc1_pre_inst_reach_state             false
% 1.10/1.00  --bmc1_out_unsat_core                   false
% 1.10/1.00  --bmc1_aig_witness_out                  false
% 1.10/1.00  --bmc1_verbose                          false
% 1.10/1.00  --bmc1_dump_clauses_tptp                false
% 1.10/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.10/1.00  --bmc1_dump_file                        -
% 1.10/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.10/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.10/1.00  --bmc1_ucm_extend_mode                  1
% 1.10/1.00  --bmc1_ucm_init_mode                    2
% 1.10/1.00  --bmc1_ucm_cone_mode                    none
% 1.10/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.10/1.00  --bmc1_ucm_relax_model                  4
% 1.10/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.10/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.10/1.00  --bmc1_ucm_layered_model                none
% 1.10/1.00  --bmc1_ucm_max_lemma_size               10
% 1.10/1.00  
% 1.10/1.00  ------ AIG Options
% 1.10/1.00  
% 1.10/1.00  --aig_mode                              false
% 1.10/1.00  
% 1.10/1.00  ------ Instantiation Options
% 1.10/1.00  
% 1.10/1.00  --instantiation_flag                    true
% 1.10/1.00  --inst_sos_flag                         false
% 1.10/1.00  --inst_sos_phase                        true
% 1.10/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.10/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.10/1.00  --inst_lit_sel_side                     none
% 1.10/1.00  --inst_solver_per_active                1400
% 1.10/1.00  --inst_solver_calls_frac                1.
% 1.10/1.00  --inst_passive_queue_type               priority_queues
% 1.10/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.10/1.00  --inst_passive_queues_freq              [25;2]
% 1.10/1.00  --inst_dismatching                      true
% 1.10/1.00  --inst_eager_unprocessed_to_passive     true
% 1.10/1.00  --inst_prop_sim_given                   true
% 1.10/1.00  --inst_prop_sim_new                     false
% 1.10/1.00  --inst_subs_new                         false
% 1.10/1.00  --inst_eq_res_simp                      false
% 1.10/1.00  --inst_subs_given                       false
% 1.10/1.00  --inst_orphan_elimination               true
% 1.10/1.00  --inst_learning_loop_flag               true
% 1.10/1.00  --inst_learning_start                   3000
% 1.10/1.00  --inst_learning_factor                  2
% 1.10/1.00  --inst_start_prop_sim_after_learn       3
% 1.10/1.00  --inst_sel_renew                        solver
% 1.10/1.00  --inst_lit_activity_flag                true
% 1.10/1.00  --inst_restr_to_given                   false
% 1.10/1.00  --inst_activity_threshold               500
% 1.10/1.00  --inst_out_proof                        true
% 1.10/1.00  
% 1.10/1.00  ------ Resolution Options
% 1.10/1.00  
% 1.10/1.00  --resolution_flag                       false
% 1.10/1.00  --res_lit_sel                           adaptive
% 1.10/1.00  --res_lit_sel_side                      none
% 1.10/1.00  --res_ordering                          kbo
% 1.10/1.00  --res_to_prop_solver                    active
% 1.10/1.00  --res_prop_simpl_new                    false
% 1.10/1.00  --res_prop_simpl_given                  true
% 1.10/1.00  --res_passive_queue_type                priority_queues
% 1.10/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.10/1.00  --res_passive_queues_freq               [15;5]
% 1.10/1.00  --res_forward_subs                      full
% 1.10/1.00  --res_backward_subs                     full
% 1.10/1.00  --res_forward_subs_resolution           true
% 1.10/1.00  --res_backward_subs_resolution          true
% 1.10/1.00  --res_orphan_elimination                true
% 1.10/1.00  --res_time_limit                        2.
% 1.10/1.00  --res_out_proof                         true
% 1.10/1.00  
% 1.10/1.00  ------ Superposition Options
% 1.10/1.00  
% 1.10/1.00  --superposition_flag                    false
% 1.10/1.00  --sup_passive_queue_type                priority_queues
% 1.10/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.10/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.10/1.00  --demod_completeness_check              fast
% 1.10/1.00  --demod_use_ground                      true
% 1.10/1.00  --sup_to_prop_solver                    passive
% 1.10/1.00  --sup_prop_simpl_new                    true
% 1.10/1.00  --sup_prop_simpl_given                  true
% 1.10/1.00  --sup_fun_splitting                     false
% 1.10/1.00  --sup_smt_interval                      50000
% 1.10/1.00  
% 1.10/1.00  ------ Superposition Simplification Setup
% 1.10/1.00  
% 1.10/1.00  --sup_indices_passive                   []
% 1.10/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.10/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.10/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.10/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.10/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.10/1.00  --sup_full_bw                           [BwDemod]
% 1.10/1.00  --sup_immed_triv                        [TrivRules]
% 1.10/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.10/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.10/1.00  --sup_immed_bw_main                     []
% 1.10/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.10/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.10/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.10/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.10/1.00  
% 1.10/1.00  ------ Combination Options
% 1.10/1.00  
% 1.10/1.00  --comb_res_mult                         3
% 1.10/1.00  --comb_sup_mult                         2
% 1.10/1.00  --comb_inst_mult                        10
% 1.10/1.00  
% 1.10/1.00  ------ Debug Options
% 1.10/1.00  
% 1.10/1.00  --dbg_backtrace                         false
% 1.10/1.00  --dbg_dump_prop_clauses                 false
% 1.10/1.00  --dbg_dump_prop_clauses_file            -
% 1.10/1.00  --dbg_out_stat                          false
% 1.10/1.00  
% 1.10/1.00  
% 1.10/1.00  
% 1.10/1.00  
% 1.10/1.00  ------ Proving...
% 1.10/1.00  
% 1.10/1.00  
% 1.10/1.00  % SZS status Theorem for theBenchmark.p
% 1.10/1.00  
% 1.10/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.10/1.00  
% 1.10/1.00  fof(f1,axiom,(
% 1.10/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.10/1.00  
% 1.10/1.00  fof(f16,plain,(
% 1.10/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.10/1.00    inference(rectify,[],[f1])).
% 1.10/1.00  
% 1.10/1.00  fof(f19,plain,(
% 1.10/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.10/1.00    inference(ennf_transformation,[],[f16])).
% 1.10/1.00  
% 1.10/1.00  fof(f44,plain,(
% 1.10/1.00    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 1.10/1.00    introduced(choice_axiom,[])).
% 1.10/1.00  
% 1.10/1.00  fof(f45,plain,(
% 1.10/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.10/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f44])).
% 1.10/1.00  
% 1.10/1.00  fof(f52,plain,(
% 1.10/1.00    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.10/1.00    inference(cnf_transformation,[],[f45])).
% 1.10/1.00  
% 1.10/1.00  fof(f3,axiom,(
% 1.10/1.00    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.10/1.00  
% 1.10/1.00  fof(f22,plain,(
% 1.10/1.00    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.10/1.00    inference(ennf_transformation,[],[f3])).
% 1.10/1.00  
% 1.10/1.00  fof(f55,plain,(
% 1.10/1.00    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.10/1.00    inference(cnf_transformation,[],[f22])).
% 1.10/1.00  
% 1.10/1.00  fof(f53,plain,(
% 1.10/1.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.10/1.00    inference(cnf_transformation,[],[f45])).
% 1.10/1.00  
% 1.10/1.00  fof(f12,axiom,(
% 1.10/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (~r2_hidden(X2,X1) => r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)))))),
% 1.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.10/1.00  
% 1.10/1.00  fof(f38,plain,(
% 1.10/1.00    ! [X0] : (! [X1] : (! [X2] : ((r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2) | r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.10/1.00    inference(ennf_transformation,[],[f12])).
% 1.10/1.00  
% 1.10/1.00  fof(f39,plain,(
% 1.10/1.00    ! [X0] : (! [X1] : (! [X2] : (r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2) | r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.10/1.00    inference(flattening,[],[f38])).
% 1.10/1.00  
% 1.10/1.00  fof(f68,plain,(
% 1.10/1.00    ( ! [X2,X0,X1] : (r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2) | r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.10/1.00    inference(cnf_transformation,[],[f39])).
% 1.10/1.00  
% 1.10/1.00  fof(f7,axiom,(
% 1.10/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.10/1.00  
% 1.10/1.00  fof(f28,plain,(
% 1.10/1.00    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.10/1.00    inference(ennf_transformation,[],[f7])).
% 1.10/1.00  
% 1.10/1.00  fof(f29,plain,(
% 1.10/1.00    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.10/1.00    inference(flattening,[],[f28])).
% 1.10/1.00  
% 1.10/1.00  fof(f59,plain,(
% 1.10/1.00    ( ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.10/1.00    inference(cnf_transformation,[],[f29])).
% 1.10/1.00  
% 1.10/1.00  fof(f8,axiom,(
% 1.10/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r2_hidden(X1,k1_connsp_2(X0,X1))))),
% 1.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.10/1.00  
% 1.10/1.00  fof(f30,plain,(
% 1.10/1.00    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.10/1.00    inference(ennf_transformation,[],[f8])).
% 1.10/1.00  
% 1.10/1.00  fof(f31,plain,(
% 1.10/1.00    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.10/1.00    inference(flattening,[],[f30])).
% 1.10/1.00  
% 1.10/1.00  fof(f60,plain,(
% 1.10/1.00    ( ! [X0,X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.10/1.00    inference(cnf_transformation,[],[f31])).
% 1.10/1.00  
% 1.10/1.00  fof(f2,axiom,(
% 1.10/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.10/1.00  
% 1.10/1.00  fof(f20,plain,(
% 1.10/1.00    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.10/1.00    inference(ennf_transformation,[],[f2])).
% 1.10/1.00  
% 1.10/1.00  fof(f21,plain,(
% 1.10/1.00    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.10/1.00    inference(flattening,[],[f20])).
% 1.10/1.00  
% 1.10/1.00  fof(f54,plain,(
% 1.10/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.10/1.00    inference(cnf_transformation,[],[f21])).
% 1.10/1.00  
% 1.10/1.00  fof(f10,axiom,(
% 1.10/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 1.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.10/1.00  
% 1.10/1.00  fof(f34,plain,(
% 1.10/1.00    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.10/1.00    inference(ennf_transformation,[],[f10])).
% 1.10/1.00  
% 1.10/1.00  fof(f35,plain,(
% 1.10/1.00    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.10/1.00    inference(flattening,[],[f34])).
% 1.10/1.00  
% 1.10/1.00  fof(f64,plain,(
% 1.10/1.00    ( ! [X0,X1] : (v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.10/1.00    inference(cnf_transformation,[],[f35])).
% 1.10/1.00  
% 1.10/1.00  fof(f13,axiom,(
% 1.10/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 1.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.10/1.00  
% 1.10/1.00  fof(f40,plain,(
% 1.10/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.10/1.00    inference(ennf_transformation,[],[f13])).
% 1.10/1.00  
% 1.10/1.00  fof(f41,plain,(
% 1.10/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.10/1.00    inference(flattening,[],[f40])).
% 1.10/1.00  
% 1.10/1.00  fof(f69,plain,(
% 1.10/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.10/1.00    inference(cnf_transformation,[],[f41])).
% 1.10/1.00  
% 1.10/1.00  fof(f79,plain,(
% 1.10/1.00    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.10/1.00    inference(equality_resolution,[],[f69])).
% 1.10/1.00  
% 1.10/1.00  fof(f9,axiom,(
% 1.10/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))))),
% 1.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.10/1.00  
% 1.10/1.00  fof(f18,plain,(
% 1.10/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))))),
% 1.10/1.00    inference(pure_predicate_removal,[],[f9])).
% 1.10/1.00  
% 1.10/1.00  fof(f32,plain,(
% 1.10/1.00    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.10/1.00    inference(ennf_transformation,[],[f18])).
% 1.10/1.00  
% 1.10/1.00  fof(f33,plain,(
% 1.10/1.00    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.10/1.00    inference(flattening,[],[f32])).
% 1.10/1.00  
% 1.10/1.00  fof(f61,plain,(
% 1.10/1.00    ( ! [X0,X1] : (v2_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.10/1.00    inference(cnf_transformation,[],[f33])).
% 1.10/1.00  
% 1.10/1.00  fof(f62,plain,(
% 1.10/1.00    ( ! [X0,X1] : (l1_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.10/1.00    inference(cnf_transformation,[],[f33])).
% 1.10/1.00  
% 1.10/1.00  fof(f11,axiom,(
% 1.10/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))))),
% 1.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.10/1.00  
% 1.10/1.00  fof(f17,plain,(
% 1.10/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))))),
% 1.10/1.00    inference(pure_predicate_removal,[],[f11])).
% 1.10/1.00  
% 1.10/1.00  fof(f36,plain,(
% 1.10/1.00    ! [X0,X1] : ((v2_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.10/1.00    inference(ennf_transformation,[],[f17])).
% 1.10/1.00  
% 1.10/1.00  fof(f37,plain,(
% 1.10/1.00    ! [X0,X1] : ((v2_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.10/1.00    inference(flattening,[],[f36])).
% 1.10/1.00  
% 1.10/1.00  fof(f66,plain,(
% 1.10/1.00    ( ! [X0,X1] : (~v2_struct_0(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.10/1.00    inference(cnf_transformation,[],[f37])).
% 1.10/1.00  
% 1.10/1.00  fof(f63,plain,(
% 1.10/1.00    ( ! [X0,X1] : (v1_funct_1(k7_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.10/1.00    inference(cnf_transformation,[],[f35])).
% 1.10/1.00  
% 1.10/1.00  fof(f65,plain,(
% 1.10/1.00    ( ! [X0,X1] : (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.10/1.00    inference(cnf_transformation,[],[f35])).
% 1.10/1.00  
% 1.10/1.00  fof(f6,axiom,(
% 1.10/1.00    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 1.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.10/1.00  
% 1.10/1.00  fof(f26,plain,(
% 1.10/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.10/1.00    inference(ennf_transformation,[],[f6])).
% 1.10/1.00  
% 1.10/1.00  fof(f27,plain,(
% 1.10/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.10/1.00    inference(flattening,[],[f26])).
% 1.10/1.00  
% 1.10/1.00  fof(f58,plain,(
% 1.10/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.10/1.00    inference(cnf_transformation,[],[f27])).
% 1.10/1.00  
% 1.10/1.00  fof(f14,conjecture,(
% 1.10/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_xboole_0(u1_struct_0(X2),X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3))))))),
% 1.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.10/1.00  
% 1.10/1.00  fof(f15,negated_conjecture,(
% 1.10/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_xboole_0(u1_struct_0(X2),X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3))))))),
% 1.10/1.00    inference(negated_conjecture,[],[f14])).
% 1.10/1.00  
% 1.10/1.00  fof(f42,plain,(
% 1.10/1.00    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (~r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),X1)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.10/1.00    inference(ennf_transformation,[],[f15])).
% 1.10/1.00  
% 1.10/1.00  fof(f43,plain,(
% 1.10/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),X1) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.10/1.00    inference(flattening,[],[f42])).
% 1.10/1.00  
% 1.10/1.00  fof(f49,plain,(
% 1.10/1.00    ( ! [X2,X0,X1] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) => (~r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),sK4) & m1_subset_1(sK4,u1_struct_0(X2)))) )),
% 1.10/1.00    introduced(choice_axiom,[])).
% 1.10/1.00  
% 1.10/1.00  fof(f48,plain,(
% 1.10/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),X1) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (~r1_tmap_1(sK3,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),sK3),X3) & m1_subset_1(X3,u1_struct_0(sK3))) & r1_xboole_0(u1_struct_0(sK3),X1) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 1.10/1.00    introduced(choice_axiom,[])).
% 1.10/1.00  
% 1.10/1.00  fof(f47,plain,(
% 1.10/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),X1) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(X0,sK2),k2_tmap_1(X0,k6_tmap_1(X0,sK2),k7_tmap_1(X0,sK2),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),sK2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.10/1.00    introduced(choice_axiom,[])).
% 1.10/1.00  
% 1.10/1.00  fof(f46,plain,(
% 1.10/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),X1) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(sK1,X1),k2_tmap_1(sK1,k6_tmap_1(sK1,X1),k7_tmap_1(sK1,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),X1) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.10/1.00    introduced(choice_axiom,[])).
% 1.10/1.00  
% 1.10/1.00  fof(f50,plain,(
% 1.10/1.00    (((~r1_tmap_1(sK3,k6_tmap_1(sK1,sK2),k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),sK4) & m1_subset_1(sK4,u1_struct_0(sK3))) & r1_xboole_0(u1_struct_0(sK3),sK2) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 1.10/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f43,f49,f48,f47,f46])).
% 1.10/1.00  
% 1.10/1.00  fof(f75,plain,(
% 1.10/1.00    m1_pre_topc(sK3,sK1)),
% 1.10/1.00    inference(cnf_transformation,[],[f50])).
% 1.10/1.00  
% 1.10/1.00  fof(f70,plain,(
% 1.10/1.00    ~v2_struct_0(sK1)),
% 1.10/1.00    inference(cnf_transformation,[],[f50])).
% 1.10/1.00  
% 1.10/1.00  fof(f71,plain,(
% 1.10/1.00    v2_pre_topc(sK1)),
% 1.10/1.00    inference(cnf_transformation,[],[f50])).
% 1.10/1.00  
% 1.10/1.00  fof(f72,plain,(
% 1.10/1.00    l1_pre_topc(sK1)),
% 1.10/1.00    inference(cnf_transformation,[],[f50])).
% 1.10/1.00  
% 1.10/1.00  fof(f74,plain,(
% 1.10/1.00    ~v2_struct_0(sK3)),
% 1.10/1.00    inference(cnf_transformation,[],[f50])).
% 1.10/1.00  
% 1.10/1.00  fof(f4,axiom,(
% 1.10/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.10/1.00  
% 1.10/1.00  fof(f23,plain,(
% 1.10/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.10/1.00    inference(ennf_transformation,[],[f4])).
% 1.10/1.00  
% 1.10/1.00  fof(f24,plain,(
% 1.10/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.10/1.00    inference(flattening,[],[f23])).
% 1.10/1.00  
% 1.10/1.00  fof(f56,plain,(
% 1.10/1.00    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.10/1.00    inference(cnf_transformation,[],[f24])).
% 1.10/1.00  
% 1.10/1.00  fof(f5,axiom,(
% 1.10/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.10/1.00  
% 1.10/1.00  fof(f25,plain,(
% 1.10/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.10/1.00    inference(ennf_transformation,[],[f5])).
% 1.10/1.00  
% 1.10/1.00  fof(f57,plain,(
% 1.10/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.10/1.00    inference(cnf_transformation,[],[f25])).
% 1.10/1.00  
% 1.10/1.00  fof(f78,plain,(
% 1.10/1.00    ~r1_tmap_1(sK3,k6_tmap_1(sK1,sK2),k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),sK4)),
% 1.10/1.00    inference(cnf_transformation,[],[f50])).
% 1.10/1.00  
% 1.10/1.00  fof(f77,plain,(
% 1.10/1.00    m1_subset_1(sK4,u1_struct_0(sK3))),
% 1.10/1.00    inference(cnf_transformation,[],[f50])).
% 1.10/1.00  
% 1.10/1.00  fof(f76,plain,(
% 1.10/1.00    r1_xboole_0(u1_struct_0(sK3),sK2)),
% 1.10/1.00    inference(cnf_transformation,[],[f50])).
% 1.10/1.00  
% 1.10/1.00  fof(f73,plain,(
% 1.10/1.00    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.10/1.00    inference(cnf_transformation,[],[f50])).
% 1.10/1.00  
% 1.10/1.00  cnf(c_1,plain,
% 1.10/1.00      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 1.10/1.00      inference(cnf_transformation,[],[f52]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_700,plain,
% 1.10/1.00      ( r2_hidden(sK0(X0_52,X1_52),X1_52) | r1_xboole_0(X0_52,X1_52) ),
% 1.10/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_977,plain,
% 1.10/1.00      ( r2_hidden(sK0(X0_52,k1_connsp_2(sK3,sK4)),k1_connsp_2(sK3,sK4))
% 1.10/1.00      | r1_xboole_0(X0_52,k1_connsp_2(sK3,sK4)) ),
% 1.10/1.00      inference(instantiation,[status(thm)],[c_700]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_983,plain,
% 1.10/1.00      ( r2_hidden(sK0(sK2,k1_connsp_2(sK3,sK4)),k1_connsp_2(sK3,sK4))
% 1.10/1.00      | r1_xboole_0(sK2,k1_connsp_2(sK3,sK4)) ),
% 1.10/1.00      inference(instantiation,[status(thm)],[c_977]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_4,plain,
% 1.10/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.10/1.00      | ~ r2_hidden(X2,X0)
% 1.10/1.00      | ~ v1_xboole_0(X1) ),
% 1.10/1.00      inference(cnf_transformation,[],[f55]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_697,plain,
% 1.10/1.00      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(X1_52))
% 1.10/1.00      | ~ r2_hidden(X2_52,X0_52)
% 1.10/1.00      | ~ v1_xboole_0(X1_52) ),
% 1.10/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_868,plain,
% 1.10/1.00      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.10/1.00      | ~ r2_hidden(X1_52,X0_52)
% 1.10/1.00      | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 1.10/1.00      inference(instantiation,[status(thm)],[c_697]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_941,plain,
% 1.10/1.00      ( ~ m1_subset_1(k1_connsp_2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 1.10/1.00      | ~ r2_hidden(X0_52,k1_connsp_2(sK3,sK4))
% 1.10/1.00      | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 1.10/1.00      inference(instantiation,[status(thm)],[c_868]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_976,plain,
% 1.10/1.00      ( ~ m1_subset_1(k1_connsp_2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 1.10/1.00      | ~ r2_hidden(sK0(X0_52,k1_connsp_2(sK3,sK4)),k1_connsp_2(sK3,sK4))
% 1.10/1.00      | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 1.10/1.00      inference(instantiation,[status(thm)],[c_941]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_979,plain,
% 1.10/1.00      ( ~ m1_subset_1(k1_connsp_2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 1.10/1.00      | ~ r2_hidden(sK0(sK2,k1_connsp_2(sK3,sK4)),k1_connsp_2(sK3,sK4))
% 1.10/1.00      | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 1.10/1.00      inference(instantiation,[status(thm)],[c_976]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_0,plain,
% 1.10/1.00      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 1.10/1.00      inference(cnf_transformation,[],[f53]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_701,plain,
% 1.10/1.00      ( ~ r2_hidden(X0_52,X1_52)
% 1.10/1.00      | ~ r2_hidden(X0_52,X2_52)
% 1.10/1.00      | ~ r1_xboole_0(X2_52,X1_52) ),
% 1.10/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_886,plain,
% 1.10/1.00      ( ~ r2_hidden(sK4,X0_52)
% 1.10/1.00      | ~ r2_hidden(sK4,X1_52)
% 1.10/1.00      | ~ r1_xboole_0(X1_52,X0_52) ),
% 1.10/1.00      inference(instantiation,[status(thm)],[c_701]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_913,plain,
% 1.10/1.00      ( ~ r2_hidden(sK4,u1_struct_0(sK3))
% 1.10/1.00      | ~ r2_hidden(sK4,sK2)
% 1.10/1.00      | ~ r1_xboole_0(u1_struct_0(sK3),sK2) ),
% 1.10/1.00      inference(instantiation,[status(thm)],[c_886]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_878,plain,
% 1.10/1.00      ( ~ r2_hidden(sK4,X0_52)
% 1.10/1.00      | ~ r2_hidden(sK4,k1_connsp_2(sK3,sK4))
% 1.10/1.00      | ~ r1_xboole_0(X0_52,k1_connsp_2(sK3,sK4)) ),
% 1.10/1.00      inference(instantiation,[status(thm)],[c_701]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_880,plain,
% 1.10/1.00      ( ~ r2_hidden(sK4,k1_connsp_2(sK3,sK4))
% 1.10/1.00      | ~ r2_hidden(sK4,sK2)
% 1.10/1.00      | ~ r1_xboole_0(sK2,k1_connsp_2(sK3,sK4)) ),
% 1.10/1.00      inference(instantiation,[status(thm)],[c_878]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_17,plain,
% 1.10/1.00      ( r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)
% 1.10/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.10/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.10/1.00      | r2_hidden(X2,X1)
% 1.10/1.00      | v2_struct_0(X0)
% 1.10/1.00      | ~ l1_pre_topc(X0)
% 1.10/1.00      | ~ v2_pre_topc(X0) ),
% 1.10/1.00      inference(cnf_transformation,[],[f68]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_690,plain,
% 1.10/1.00      ( r1_tmap_1(X0_51,k6_tmap_1(X0_51,X0_52),k7_tmap_1(X0_51,X0_52),X1_52)
% 1.10/1.00      | ~ m1_subset_1(X1_52,u1_struct_0(X0_51))
% 1.10/1.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51)))
% 1.10/1.00      | r2_hidden(X1_52,X0_52)
% 1.10/1.00      | v2_struct_0(X0_51)
% 1.10/1.00      | ~ l1_pre_topc(X0_51)
% 1.10/1.00      | ~ v2_pre_topc(X0_51) ),
% 1.10/1.00      inference(subtyping,[status(esa)],[c_17]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_854,plain,
% 1.10/1.00      ( r1_tmap_1(sK1,k6_tmap_1(sK1,X0_52),k7_tmap_1(sK1,X0_52),sK4)
% 1.10/1.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.10/1.00      | ~ m1_subset_1(sK4,u1_struct_0(sK1))
% 1.10/1.00      | r2_hidden(sK4,X0_52)
% 1.10/1.00      | v2_struct_0(sK1)
% 1.10/1.00      | ~ l1_pre_topc(sK1)
% 1.10/1.00      | ~ v2_pre_topc(sK1) ),
% 1.10/1.00      inference(instantiation,[status(thm)],[c_690]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_856,plain,
% 1.10/1.00      ( r1_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK4)
% 1.10/1.00      | ~ m1_subset_1(sK4,u1_struct_0(sK1))
% 1.10/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.10/1.00      | r2_hidden(sK4,sK2)
% 1.10/1.00      | v2_struct_0(sK1)
% 1.10/1.00      | ~ l1_pre_topc(sK1)
% 1.10/1.00      | ~ v2_pre_topc(sK1) ),
% 1.10/1.00      inference(instantiation,[status(thm)],[c_854]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_8,plain,
% 1.10/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.10/1.00      | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.10/1.00      | v2_struct_0(X1)
% 1.10/1.00      | ~ l1_pre_topc(X1)
% 1.10/1.00      | ~ v2_pre_topc(X1) ),
% 1.10/1.00      inference(cnf_transformation,[],[f59]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_696,plain,
% 1.10/1.00      ( ~ m1_subset_1(X0_52,u1_struct_0(X0_51))
% 1.10/1.00      | m1_subset_1(k1_connsp_2(X0_51,X0_52),k1_zfmisc_1(u1_struct_0(X0_51)))
% 1.10/1.00      | v2_struct_0(X0_51)
% 1.10/1.00      | ~ l1_pre_topc(X0_51)
% 1.10/1.00      | ~ v2_pre_topc(X0_51) ),
% 1.10/1.00      inference(subtyping,[status(esa)],[c_8]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_841,plain,
% 1.10/1.00      ( m1_subset_1(k1_connsp_2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 1.10/1.00      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 1.10/1.00      | v2_struct_0(sK3)
% 1.10/1.00      | ~ l1_pre_topc(sK3)
% 1.10/1.00      | ~ v2_pre_topc(sK3) ),
% 1.10/1.00      inference(instantiation,[status(thm)],[c_696]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_9,plain,
% 1.10/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.10/1.00      | r2_hidden(X0,k1_connsp_2(X1,X0))
% 1.10/1.00      | v2_struct_0(X1)
% 1.10/1.00      | ~ l1_pre_topc(X1)
% 1.10/1.00      | ~ v2_pre_topc(X1) ),
% 1.10/1.00      inference(cnf_transformation,[],[f60]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_695,plain,
% 1.10/1.00      ( ~ m1_subset_1(X0_52,u1_struct_0(X0_51))
% 1.10/1.00      | r2_hidden(X0_52,k1_connsp_2(X0_51,X0_52))
% 1.10/1.00      | v2_struct_0(X0_51)
% 1.10/1.00      | ~ l1_pre_topc(X0_51)
% 1.10/1.00      | ~ v2_pre_topc(X0_51) ),
% 1.10/1.00      inference(subtyping,[status(esa)],[c_9]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_838,plain,
% 1.10/1.00      ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 1.10/1.00      | r2_hidden(sK4,k1_connsp_2(sK3,sK4))
% 1.10/1.00      | v2_struct_0(sK3)
% 1.10/1.00      | ~ l1_pre_topc(sK3)
% 1.10/1.00      | ~ v2_pre_topc(sK3) ),
% 1.10/1.00      inference(instantiation,[status(thm)],[c_695]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_3,plain,
% 1.10/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 1.10/1.00      inference(cnf_transformation,[],[f54]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_698,plain,
% 1.10/1.00      ( ~ m1_subset_1(X0_52,X1_52)
% 1.10/1.00      | r2_hidden(X0_52,X1_52)
% 1.10/1.00      | v1_xboole_0(X1_52) ),
% 1.10/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_832,plain,
% 1.10/1.00      ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 1.10/1.00      | r2_hidden(sK4,u1_struct_0(sK3))
% 1.10/1.00      | v1_xboole_0(u1_struct_0(sK3)) ),
% 1.10/1.00      inference(instantiation,[status(thm)],[c_698]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_13,plain,
% 1.10/1.00      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
% 1.10/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.10/1.00      | v2_struct_0(X0)
% 1.10/1.00      | ~ l1_pre_topc(X0)
% 1.10/1.00      | ~ v2_pre_topc(X0) ),
% 1.10/1.00      inference(cnf_transformation,[],[f64]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_18,plain,
% 1.10/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.10/1.00      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.10/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.10/1.00      | ~ m1_pre_topc(X4,X0)
% 1.10/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.10/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.10/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.10/1.00      | ~ v1_funct_1(X2)
% 1.10/1.00      | v2_struct_0(X1)
% 1.10/1.00      | v2_struct_0(X0)
% 1.10/1.00      | v2_struct_0(X4)
% 1.10/1.00      | ~ l1_pre_topc(X1)
% 1.10/1.00      | ~ l1_pre_topc(X0)
% 1.10/1.00      | ~ v2_pre_topc(X1)
% 1.10/1.00      | ~ v2_pre_topc(X0) ),
% 1.10/1.00      inference(cnf_transformation,[],[f79]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_342,plain,
% 1.10/1.00      ( r1_tmap_1(X0,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X0),X3)
% 1.10/1.00      | ~ r1_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3)
% 1.10/1.00      | ~ m1_pre_topc(X0,X1)
% 1.10/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.10/1.00      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 1.10/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.10/1.00      | ~ m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))
% 1.10/1.00      | ~ v1_funct_1(k7_tmap_1(X1,X2))
% 1.10/1.00      | v2_struct_0(X0)
% 1.10/1.00      | v2_struct_0(X1)
% 1.10/1.00      | v2_struct_0(k6_tmap_1(X1,X2))
% 1.10/1.00      | ~ l1_pre_topc(X1)
% 1.10/1.00      | ~ l1_pre_topc(k6_tmap_1(X1,X2))
% 1.10/1.00      | ~ v2_pre_topc(X1)
% 1.10/1.00      | ~ v2_pre_topc(k6_tmap_1(X1,X2)) ),
% 1.10/1.00      inference(resolution,[status(thm)],[c_13,c_18]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_11,plain,
% 1.10/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.10/1.00      | v2_struct_0(X1)
% 1.10/1.00      | ~ l1_pre_topc(X1)
% 1.10/1.00      | ~ v2_pre_topc(X1)
% 1.10/1.00      | v2_pre_topc(k6_tmap_1(X1,X0)) ),
% 1.10/1.00      inference(cnf_transformation,[],[f61]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_10,plain,
% 1.10/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.10/1.00      | v2_struct_0(X1)
% 1.10/1.00      | ~ l1_pre_topc(X1)
% 1.10/1.00      | l1_pre_topc(k6_tmap_1(X1,X0))
% 1.10/1.00      | ~ v2_pre_topc(X1) ),
% 1.10/1.00      inference(cnf_transformation,[],[f62]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_16,plain,
% 1.10/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.10/1.00      | v2_struct_0(X1)
% 1.10/1.00      | ~ v2_struct_0(k6_tmap_1(X1,X0))
% 1.10/1.00      | ~ l1_pre_topc(X1)
% 1.10/1.00      | ~ v2_pre_topc(X1) ),
% 1.10/1.00      inference(cnf_transformation,[],[f66]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_14,plain,
% 1.10/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.10/1.00      | v1_funct_1(k7_tmap_1(X1,X0))
% 1.10/1.00      | v2_struct_0(X1)
% 1.10/1.00      | ~ l1_pre_topc(X1)
% 1.10/1.00      | ~ v2_pre_topc(X1) ),
% 1.10/1.00      inference(cnf_transformation,[],[f63]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_12,plain,
% 1.10/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.10/1.00      | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
% 1.10/1.00      | v2_struct_0(X1)
% 1.10/1.00      | ~ l1_pre_topc(X1)
% 1.10/1.00      | ~ v2_pre_topc(X1) ),
% 1.10/1.00      inference(cnf_transformation,[],[f65]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_7,plain,
% 1.10/1.00      ( ~ m1_pre_topc(X0,X1)
% 1.10/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.10/1.00      | m1_subset_1(X2,u1_struct_0(X1))
% 1.10/1.00      | v2_struct_0(X1)
% 1.10/1.00      | v2_struct_0(X0)
% 1.10/1.00      | ~ l1_pre_topc(X1) ),
% 1.10/1.00      inference(cnf_transformation,[],[f58]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_376,plain,
% 1.10/1.00      ( r1_tmap_1(X0,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X0),X3)
% 1.10/1.00      | ~ r1_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3)
% 1.10/1.00      | ~ m1_pre_topc(X0,X1)
% 1.10/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.10/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.10/1.00      | v2_struct_0(X0)
% 1.10/1.00      | v2_struct_0(X1)
% 1.10/1.00      | ~ l1_pre_topc(X1)
% 1.10/1.00      | ~ v2_pre_topc(X1) ),
% 1.10/1.00      inference(forward_subsumption_resolution,
% 1.10/1.00                [status(thm)],
% 1.10/1.00                [c_342,c_11,c_10,c_16,c_14,c_12,c_7]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_22,negated_conjecture,
% 1.10/1.00      ( m1_pre_topc(sK3,sK1) ),
% 1.10/1.00      inference(cnf_transformation,[],[f75]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_399,plain,
% 1.10/1.00      ( ~ r1_tmap_1(sK1,k6_tmap_1(sK1,X0),k7_tmap_1(sK1,X0),X1)
% 1.10/1.00      | r1_tmap_1(sK3,k6_tmap_1(sK1,X0),k2_tmap_1(sK1,k6_tmap_1(sK1,X0),k7_tmap_1(sK1,X0),sK3),X1)
% 1.10/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.10/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.10/1.00      | v2_struct_0(sK1)
% 1.10/1.00      | v2_struct_0(sK3)
% 1.10/1.00      | ~ l1_pre_topc(sK1)
% 1.10/1.00      | ~ v2_pre_topc(sK1) ),
% 1.10/1.00      inference(resolution,[status(thm)],[c_376,c_22]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_27,negated_conjecture,
% 1.10/1.00      ( ~ v2_struct_0(sK1) ),
% 1.10/1.00      inference(cnf_transformation,[],[f70]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_26,negated_conjecture,
% 1.10/1.00      ( v2_pre_topc(sK1) ),
% 1.10/1.00      inference(cnf_transformation,[],[f71]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_25,negated_conjecture,
% 1.10/1.00      ( l1_pre_topc(sK1) ),
% 1.10/1.00      inference(cnf_transformation,[],[f72]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_23,negated_conjecture,
% 1.10/1.00      ( ~ v2_struct_0(sK3) ),
% 1.10/1.00      inference(cnf_transformation,[],[f74]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_403,plain,
% 1.10/1.00      ( ~ r1_tmap_1(sK1,k6_tmap_1(sK1,X0),k7_tmap_1(sK1,X0),X1)
% 1.10/1.00      | r1_tmap_1(sK3,k6_tmap_1(sK1,X0),k2_tmap_1(sK1,k6_tmap_1(sK1,X0),k7_tmap_1(sK1,X0),sK3),X1)
% 1.10/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.10/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.10/1.00      inference(global_propositional_subsumption,
% 1.10/1.00                [status(thm)],
% 1.10/1.00                [c_399,c_27,c_26,c_25,c_23]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_681,plain,
% 1.10/1.00      ( ~ r1_tmap_1(sK1,k6_tmap_1(sK1,X0_52),k7_tmap_1(sK1,X0_52),X1_52)
% 1.10/1.00      | r1_tmap_1(sK3,k6_tmap_1(sK1,X0_52),k2_tmap_1(sK1,k6_tmap_1(sK1,X0_52),k7_tmap_1(sK1,X0_52),sK3),X1_52)
% 1.10/1.00      | ~ m1_subset_1(X1_52,u1_struct_0(sK3))
% 1.10/1.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.10/1.00      inference(subtyping,[status(esa)],[c_403]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_827,plain,
% 1.10/1.00      ( ~ r1_tmap_1(sK1,k6_tmap_1(sK1,X0_52),k7_tmap_1(sK1,X0_52),sK4)
% 1.10/1.00      | r1_tmap_1(sK3,k6_tmap_1(sK1,X0_52),k2_tmap_1(sK1,k6_tmap_1(sK1,X0_52),k7_tmap_1(sK1,X0_52),sK3),sK4)
% 1.10/1.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.10/1.00      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 1.10/1.00      inference(instantiation,[status(thm)],[c_681]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_829,plain,
% 1.10/1.00      ( ~ r1_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK4)
% 1.10/1.00      | r1_tmap_1(sK3,k6_tmap_1(sK1,sK2),k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),sK4)
% 1.10/1.00      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 1.10/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.10/1.00      inference(instantiation,[status(thm)],[c_827]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_422,plain,
% 1.10/1.00      ( m1_subset_1(X0,u1_struct_0(sK1))
% 1.10/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.10/1.00      | v2_struct_0(sK1)
% 1.10/1.00      | v2_struct_0(sK3)
% 1.10/1.00      | ~ l1_pre_topc(sK1) ),
% 1.10/1.00      inference(resolution,[status(thm)],[c_7,c_22]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_426,plain,
% 1.10/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.10/1.00      | m1_subset_1(X0,u1_struct_0(sK1)) ),
% 1.10/1.00      inference(global_propositional_subsumption,
% 1.10/1.00                [status(thm)],
% 1.10/1.00                [c_422,c_27,c_25,c_23]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_427,plain,
% 1.10/1.00      ( m1_subset_1(X0,u1_struct_0(sK1))
% 1.10/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 1.10/1.00      inference(renaming,[status(thm)],[c_426]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_680,plain,
% 1.10/1.00      ( m1_subset_1(X0_52,u1_struct_0(sK1))
% 1.10/1.00      | ~ m1_subset_1(X0_52,u1_struct_0(sK3)) ),
% 1.10/1.00      inference(subtyping,[status(esa)],[c_427]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_824,plain,
% 1.10/1.00      ( m1_subset_1(sK4,u1_struct_0(sK1))
% 1.10/1.00      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 1.10/1.00      inference(instantiation,[status(thm)],[c_680]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_5,plain,
% 1.10/1.00      ( ~ m1_pre_topc(X0,X1)
% 1.10/1.00      | ~ l1_pre_topc(X1)
% 1.10/1.00      | ~ v2_pre_topc(X1)
% 1.10/1.00      | v2_pre_topc(X0) ),
% 1.10/1.00      inference(cnf_transformation,[],[f56]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_449,plain,
% 1.10/1.00      ( ~ l1_pre_topc(sK1) | ~ v2_pre_topc(sK1) | v2_pre_topc(sK3) ),
% 1.10/1.00      inference(resolution,[status(thm)],[c_5,c_22]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_6,plain,
% 1.10/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 1.10/1.00      inference(cnf_transformation,[],[f57]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_439,plain,
% 1.10/1.00      ( ~ l1_pre_topc(sK1) | l1_pre_topc(sK3) ),
% 1.10/1.00      inference(resolution,[status(thm)],[c_6,c_22]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_19,negated_conjecture,
% 1.10/1.00      ( ~ r1_tmap_1(sK3,k6_tmap_1(sK1,sK2),k2_tmap_1(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2),sK3),sK4) ),
% 1.10/1.00      inference(cnf_transformation,[],[f78]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_20,negated_conjecture,
% 1.10/1.00      ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 1.10/1.00      inference(cnf_transformation,[],[f77]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_21,negated_conjecture,
% 1.10/1.00      ( r1_xboole_0(u1_struct_0(sK3),sK2) ),
% 1.10/1.00      inference(cnf_transformation,[],[f76]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(c_24,negated_conjecture,
% 1.10/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.10/1.00      inference(cnf_transformation,[],[f73]) ).
% 1.10/1.00  
% 1.10/1.00  cnf(contradiction,plain,
% 1.10/1.00      ( $false ),
% 1.10/1.00      inference(minisat,
% 1.10/1.00                [status(thm)],
% 1.10/1.00                [c_983,c_979,c_913,c_880,c_856,c_841,c_838,c_832,c_829,
% 1.10/1.00                 c_824,c_449,c_439,c_19,c_20,c_21,c_23,c_24,c_25,c_26,
% 1.10/1.00                 c_27]) ).
% 1.10/1.00  
% 1.10/1.00  
% 1.10/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.10/1.00  
% 1.10/1.00  ------                               Statistics
% 1.10/1.00  
% 1.10/1.00  ------ General
% 1.10/1.00  
% 1.10/1.00  abstr_ref_over_cycles:                  0
% 1.10/1.00  abstr_ref_under_cycles:                 0
% 1.10/1.00  gc_basic_clause_elim:                   0
% 1.10/1.00  forced_gc_time:                         0
% 1.10/1.00  parsing_time:                           0.009
% 1.10/1.00  unif_index_cands_time:                  0.
% 1.10/1.00  unif_index_add_time:                    0.
% 1.10/1.00  orderings_time:                         0.
% 1.10/1.00  out_proof_time:                         0.009
% 1.10/1.00  total_time:                             0.063
% 1.10/1.00  num_of_symbols:                         56
% 1.10/1.00  num_of_terms:                           1237
% 1.10/1.00  
% 1.10/1.00  ------ Preprocessing
% 1.10/1.00  
% 1.10/1.00  num_of_splits:                          0
% 1.10/1.00  num_of_split_atoms:                     0
% 1.10/1.00  num_of_reused_defs:                     0
% 1.10/1.00  num_eq_ax_congr_red:                    0
% 1.10/1.00  num_of_sem_filtered_clauses:            0
% 1.10/1.00  num_of_subtypes:                        2
% 1.10/1.00  monotx_restored_types:                  0
% 1.10/1.00  sat_num_of_epr_types:                   0
% 1.10/1.00  sat_num_of_non_cyclic_types:            0
% 1.10/1.00  sat_guarded_non_collapsed_types:        0
% 1.10/1.00  num_pure_diseq_elim:                    0
% 1.10/1.00  simp_replaced_by:                       0
% 1.10/1.00  res_preprocessed:                       51
% 1.10/1.00  prep_upred:                             0
% 1.10/1.00  prep_unflattend:                        0
% 1.10/1.00  smt_new_axioms:                         0
% 1.10/1.00  pred_elim_cands:                        8
% 1.10/1.00  pred_elim:                              3
% 1.10/1.00  pred_elim_cl:                           3
% 1.10/1.00  pred_elim_cycles:                       8
% 1.10/1.00  merged_defs:                            0
% 1.10/1.00  merged_defs_ncl:                        0
% 1.10/1.00  bin_hyper_res:                          0
% 1.10/1.00  prep_cycles:                            2
% 1.10/1.00  pred_elim_time:                         0.005
% 1.10/1.00  splitting_time:                         0.
% 1.10/1.00  sem_filter_time:                        0.
% 1.10/1.00  monotx_time:                            0.
% 1.10/1.00  subtype_inf_time:                       0.
% 1.10/1.00  
% 1.10/1.00  ------ Problem properties
% 1.10/1.00  
% 1.10/1.00  clauses:                                24
% 1.10/1.00  conjectures:                            8
% 1.10/1.00  epr:                                    8
% 1.10/1.00  horn:                                   15
% 1.10/1.00  ground:                                 10
% 1.10/1.00  unary:                                  10
% 1.10/1.00  binary:                                 3
% 1.10/1.00  lits:                                   66
% 1.10/1.00  lits_eq:                                0
% 1.10/1.00  fd_pure:                                0
% 1.10/1.00  fd_pseudo:                              0
% 1.10/1.00  fd_cond:                                0
% 1.10/1.00  fd_pseudo_cond:                         0
% 1.10/1.00  ac_symbols:                             0
% 1.10/1.00  
% 1.10/1.00  ------ Propositional Solver
% 1.10/1.00  
% 1.10/1.00  prop_solver_calls:                      16
% 1.10/1.00  prop_fast_solver_calls:                 396
% 1.10/1.00  smt_solver_calls:                       0
% 1.10/1.00  smt_fast_solver_calls:                  0
% 1.10/1.00  prop_num_of_clauses:                    291
% 1.10/1.00  prop_preprocess_simplified:             1594
% 1.10/1.00  prop_fo_subsumed:                       10
% 1.10/1.00  prop_solver_time:                       0.
% 1.10/1.00  smt_solver_time:                        0.
% 1.10/1.00  smt_fast_solver_time:                   0.
% 1.10/1.00  prop_fast_solver_time:                  0.
% 1.10/1.00  prop_unsat_core_time:                   0.
% 1.10/1.00  
% 1.10/1.00  ------ QBF
% 1.10/1.00  
% 1.10/1.00  qbf_q_res:                              0
% 1.10/1.00  qbf_num_tautologies:                    0
% 1.10/1.00  qbf_prep_cycles:                        0
% 1.10/1.00  
% 1.10/1.00  ------ BMC1
% 1.10/1.00  
% 1.10/1.00  bmc1_current_bound:                     -1
% 1.10/1.00  bmc1_last_solved_bound:                 -1
% 1.10/1.00  bmc1_unsat_core_size:                   -1
% 1.10/1.00  bmc1_unsat_core_parents_size:           -1
% 1.10/1.00  bmc1_merge_next_fun:                    0
% 1.10/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.10/1.00  
% 1.10/1.00  ------ Instantiation
% 1.10/1.00  
% 1.10/1.00  inst_num_of_clauses:                    61
% 1.10/1.00  inst_num_in_passive:                    1
% 1.10/1.00  inst_num_in_active:                     54
% 1.10/1.00  inst_num_in_unprocessed:                5
% 1.10/1.00  inst_num_of_loops:                      66
% 1.10/1.00  inst_num_of_learning_restarts:          0
% 1.10/1.00  inst_num_moves_active_passive:          7
% 1.10/1.00  inst_lit_activity:                      0
% 1.10/1.00  inst_lit_activity_moves:                0
% 1.10/1.00  inst_num_tautologies:                   0
% 1.10/1.00  inst_num_prop_implied:                  0
% 1.10/1.00  inst_num_existing_simplified:           0
% 1.10/1.00  inst_num_eq_res_simplified:             0
% 1.10/1.00  inst_num_child_elim:                    0
% 1.10/1.00  inst_num_of_dismatching_blockings:      3
% 1.10/1.00  inst_num_of_non_proper_insts:           36
% 1.10/1.00  inst_num_of_duplicates:                 0
% 1.10/1.00  inst_inst_num_from_inst_to_res:         0
% 1.10/1.00  inst_dismatching_checking_time:         0.
% 1.10/1.00  
% 1.10/1.00  ------ Resolution
% 1.10/1.00  
% 1.10/1.00  res_num_of_clauses:                     0
% 1.10/1.00  res_num_in_passive:                     0
% 1.10/1.00  res_num_in_active:                      0
% 1.10/1.00  res_num_of_loops:                       53
% 1.10/1.00  res_forward_subset_subsumed:            1
% 1.10/1.00  res_backward_subset_subsumed:           0
% 1.10/1.00  res_forward_subsumed:                   0
% 1.10/1.00  res_backward_subsumed:                  0
% 1.10/1.00  res_forward_subsumption_resolution:     6
% 1.10/1.00  res_backward_subsumption_resolution:    0
% 1.10/1.00  res_clause_to_clause_subsumption:       19
% 1.10/1.00  res_orphan_elimination:                 0
% 1.10/1.00  res_tautology_del:                      0
% 1.10/1.00  res_num_eq_res_simplified:              0
% 1.10/1.00  res_num_sel_changes:                    0
% 1.10/1.00  res_moves_from_active_to_pass:          0
% 1.10/1.00  
% 1.10/1.00  ------ Superposition
% 1.10/1.00  
% 1.10/1.00  sup_time_total:                         0.
% 1.10/1.00  sup_time_generating:                    0.
% 1.10/1.00  sup_time_sim_full:                      0.
% 1.10/1.00  sup_time_sim_immed:                     0.
% 1.10/1.00  
% 1.10/1.00  sup_num_of_clauses:                     0
% 1.10/1.00  sup_num_in_active:                      0
% 1.10/1.00  sup_num_in_passive:                     0
% 1.10/1.00  sup_num_of_loops:                       0
% 1.10/1.00  sup_fw_superposition:                   0
% 1.10/1.00  sup_bw_superposition:                   0
% 1.10/1.00  sup_immediate_simplified:               0
% 1.10/1.00  sup_given_eliminated:                   0
% 1.10/1.00  comparisons_done:                       0
% 1.10/1.00  comparisons_avoided:                    0
% 1.10/1.00  
% 1.10/1.00  ------ Simplifications
% 1.10/1.00  
% 1.10/1.00  
% 1.10/1.00  sim_fw_subset_subsumed:                 0
% 1.10/1.00  sim_bw_subset_subsumed:                 0
% 1.10/1.00  sim_fw_subsumed:                        0
% 1.10/1.00  sim_bw_subsumed:                        0
% 1.10/1.00  sim_fw_subsumption_res:                 0
% 1.10/1.00  sim_bw_subsumption_res:                 0
% 1.10/1.00  sim_tautology_del:                      0
% 1.10/1.00  sim_eq_tautology_del:                   0
% 1.10/1.00  sim_eq_res_simp:                        0
% 1.10/1.00  sim_fw_demodulated:                     0
% 1.10/1.00  sim_bw_demodulated:                     0
% 1.10/1.00  sim_light_normalised:                   0
% 1.10/1.00  sim_joinable_taut:                      0
% 1.10/1.00  sim_joinable_simp:                      0
% 1.10/1.00  sim_ac_normalised:                      0
% 1.10/1.00  sim_smt_subsumption:                    0
% 1.10/1.00  
%------------------------------------------------------------------------------
