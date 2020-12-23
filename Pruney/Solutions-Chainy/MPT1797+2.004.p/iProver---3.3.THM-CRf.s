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
% DateTime   : Thu Dec  3 12:23:59 EST 2020

% Result     : Theorem 47.37s
% Output     : CNFRefutation 47.37s
% Verified   : 
% Statistics : Number of formulae       :  505 (3084914 expanded)
%              Number of clauses        :  424 (884919 expanded)
%              Number of leaves         :   24 (659439 expanded)
%              Depth                    :   69
%              Number of atoms          : 2413 (26982270 expanded)
%              Number of equality atoms : 1513 (1280886 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   28 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f16])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f53,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
            | ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
            | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
            | ~ v1_funct_1(k7_tmap_1(X0,X1))
            | ~ v3_pre_topc(X1,X0) )
          & ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) )
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f54,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
            | ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
            | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
            | ~ v1_funct_1(k7_tmap_1(X0,X1))
            | ~ v3_pre_topc(X1,X0) )
          & ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) )
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
            | ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
            | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
            | ~ v1_funct_1(k7_tmap_1(X0,X1))
            | ~ v3_pre_topc(X1,X0) )
          & ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) )
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ m1_subset_1(k7_tmap_1(X0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2)))))
          | ~ v5_pre_topc(k7_tmap_1(X0,sK2),X0,k6_tmap_1(X0,sK2))
          | ~ v1_funct_2(k7_tmap_1(X0,sK2),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2)))
          | ~ v1_funct_1(k7_tmap_1(X0,sK2))
          | ~ v3_pre_topc(sK2,X0) )
        & ( ( m1_subset_1(k7_tmap_1(X0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2)))))
            & v5_pre_topc(k7_tmap_1(X0,sK2),X0,k6_tmap_1(X0,sK2))
            & v1_funct_2(k7_tmap_1(X0,sK2),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2)))
            & v1_funct_1(k7_tmap_1(X0,sK2)) )
          | v3_pre_topc(sK2,X0) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              | ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              | ~ v1_funct_1(k7_tmap_1(X0,X1))
              | ~ v3_pre_topc(X1,X0) )
            & ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
                & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
                & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
                & v1_funct_1(k7_tmap_1(X0,X1)) )
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(k7_tmap_1(sK1,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X1)))))
            | ~ v5_pre_topc(k7_tmap_1(sK1,X1),sK1,k6_tmap_1(sK1,X1))
            | ~ v1_funct_2(k7_tmap_1(sK1,X1),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X1)))
            | ~ v1_funct_1(k7_tmap_1(sK1,X1))
            | ~ v3_pre_topc(X1,sK1) )
          & ( ( m1_subset_1(k7_tmap_1(sK1,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X1)))))
              & v5_pre_topc(k7_tmap_1(sK1,X1),sK1,k6_tmap_1(sK1,X1))
              & v1_funct_2(k7_tmap_1(sK1,X1),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X1)))
              & v1_funct_1(k7_tmap_1(sK1,X1)) )
            | v3_pre_topc(X1,sK1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ( ~ m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))))
      | ~ v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
      | ~ v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
      | ~ v1_funct_1(k7_tmap_1(sK1,sK2))
      | ~ v3_pre_topc(sK2,sK1) )
    & ( ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))))
        & v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
        & v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
        & v1_funct_1(k7_tmap_1(sK1,sK2)) )
      | v3_pre_topc(sK2,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f54,f56,f55])).

fof(f95,plain,
    ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f91,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f57])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f88,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f89,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f90,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( k2_struct_0(X1) = k1_xboole_0
                 => k2_struct_0(X0) = k1_xboole_0 )
               => ( v5_pre_topc(X2,X0,X1)
                <=> ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( v3_pre_topc(X3,X1)
                       => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ( k2_struct_0(X0) != k1_xboole_0
                & k2_struct_0(X1) = k1_xboole_0 )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ( k2_struct_0(X0) != k1_xboole_0
                & k2_struct_0(X1) = k1_xboole_0 )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v3_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      | ~ v3_pre_topc(X3,X1)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ( k2_struct_0(X0) != k1_xboole_0
                & k2_struct_0(X1) = k1_xboole_0 )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v3_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v3_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ( k2_struct_0(X0) != k1_xboole_0
                & k2_struct_0(X1) = k1_xboole_0 )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f48])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v3_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
        & v3_pre_topc(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
                    & v3_pre_topc(sK0(X0,X1,X2),X1)
                    & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v3_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ( k2_struct_0(X0) != k1_xboole_0
                & k2_struct_0(X1) = k1_xboole_0 )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f49,f50])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | k2_struct_0(X1) = k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f10,axiom,(
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
    inference(pure_predicate_removal,[],[f10])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f76,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f61,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f60,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f83,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))
             => ( X1 = X2
               => v3_pre_topc(X2,k6_tmap_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v3_pre_topc(X2,k6_tmap_1(X0,X1))
              | X1 != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v3_pre_topc(X2,k6_tmap_1(X0,X1))
              | X1 != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,k6_tmap_1(X0,X1))
      | X1 != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f99,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,k6_tmap_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X2))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f85])).

fof(f92,plain,
    ( v1_funct_1(k7_tmap_1(sK1,sK2))
    | v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f96,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | ~ v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
    | ~ v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | ~ v1_funct_1(k7_tmap_1(sK1,sK2))
    | ~ v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f66,plain,(
    ! [X4,X2,X0,X1] :
      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
      | ~ v3_pre_topc(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | k2_struct_0(X1) = k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | v3_pre_topc(sK0(X0,X1,X2),X1)
      | k2_struct_0(X1) = k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f94,plain,
    ( v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
    | v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
      | k2_struct_0(X1) = k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) )
            & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f86,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v5_pre_topc(X2,X0,X1)
                      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                    & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                      | ~ v5_pre_topc(X2,X0,X1) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f97,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | v3_pre_topc(sK0(X0,X1,X2),X1)
      | k2_struct_0(X0) != k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | k2_struct_0(X0) != k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f93,plain,
    ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f67,plain,(
    ! [X4,X2,X0,X1] :
      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
      | ~ v3_pre_topc(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | k2_struct_0(X0) != k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
      | k2_struct_0(X0) != k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_31,negated_conjecture,
    ( v3_pre_topc(sK2,sK1)
    | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_3384,negated_conjecture,
    ( v3_pre_topc(sK2,sK1)
    | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_4328,plain,
    ( v3_pre_topc(sK2,sK1) = iProver_top
    | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3384])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_42,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_38,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_621,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_38])).

cnf(c_622,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k7_tmap_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0)))))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_621])).

cnf(c_37,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_36,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_626,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k7_tmap_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_622,c_37,c_36])).

cnf(c_3366,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k7_tmap_1(sK1,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_55))))) ),
    inference(subtyping,[status(esa)],[c_626])).

cnf(c_3521,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK1,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_55))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3366])).

cnf(c_3523,plain,
    ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3521])).

cnf(c_4573,plain,
    ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4328,c_42,c_3523])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_3388,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58))
    | v5_pre_topc(X0_55,X0_58,X1_58)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
    | m1_subset_1(sK0(X0_58,X1_58,X0_55),k1_zfmisc_1(u1_struct_0(X1_58)))
    | ~ v1_funct_1(X0_55)
    | ~ l1_pre_topc(X0_58)
    | ~ l1_pre_topc(X1_58)
    | k2_struct_0(X1_58) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_4324,plain,
    ( k2_struct_0(X0_58) = k1_xboole_0
    | v1_funct_2(X0_55,u1_struct_0(X1_58),u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(X0_55,X1_58,X0_58) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X0_58)))) != iProver_top
    | m1_subset_1(sK0(X1_58,X0_58,X0_55),k1_zfmisc_1(u1_struct_0(X0_58))) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3388])).

cnf(c_4792,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(sK0(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2)),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) = iProver_top
    | v1_funct_1(k7_tmap_1(sK1,sK2)) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4573,c_4324])).

cnf(c_41,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_20,plain,
    ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_486,plain,
    ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_38])).

cnf(c_487,plain,
    ( v1_funct_2(k7_tmap_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_486])).

cnf(c_491,plain,
    ( v1_funct_2(k7_tmap_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_487,c_37,c_36])).

cnf(c_3373,plain,
    ( v1_funct_2(k7_tmap_1(sK1,X0_55),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_55)))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_491])).

cnf(c_3500,plain,
    ( v1_funct_2(k7_tmap_1(sK1,X0_55),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_55))) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3373])).

cnf(c_3502,plain,
    ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3500])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k7_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_603,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k7_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_38])).

cnf(c_604,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | v1_funct_1(k7_tmap_1(sK1,X0))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_603])).

cnf(c_608,plain,
    ( v1_funct_1(k7_tmap_1(sK1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_604,c_37,c_36])).

cnf(c_609,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_funct_1(k7_tmap_1(sK1,X0)) ),
    inference(renaming,[status(thm)],[c_608])).

cnf(c_3367,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_funct_1(k7_tmap_1(sK1,X0_55)) ),
    inference(subtyping,[status(esa)],[c_609])).

cnf(c_3518,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK1,X0_55)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3367])).

cnf(c_3520,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK1,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3518])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k6_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_657,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k6_tmap_1(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_38])).

cnf(c_658,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | l1_pre_topc(k6_tmap_1(sK1,X0))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_657])).

cnf(c_662,plain,
    ( l1_pre_topc(k6_tmap_1(sK1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_658,c_37,c_36])).

cnf(c_663,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | l1_pre_topc(k6_tmap_1(sK1,X0)) ),
    inference(renaming,[status(thm)],[c_662])).

cnf(c_3364,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1)))
    | l1_pre_topc(k6_tmap_1(sK1,X0_55)) ),
    inference(subtyping,[status(esa)],[c_663])).

cnf(c_3527,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,X0_55)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3364])).

cnf(c_3529,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3527])).

cnf(c_6468,plain,
    ( m1_subset_1(sK0(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2)),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) = iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4792,c_41,c_42,c_3502,c_3520,c_3529])).

cnf(c_6469,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(sK0(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2)),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) = iProver_top ),
    inference(renaming,[status(thm)],[c_6468])).

cnf(c_3379,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(subtyping,[status(esa)],[c_36])).

cnf(c_4333,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3379])).

cnf(c_3,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_439,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_3,c_2])).

cnf(c_3377,plain,
    ( ~ l1_pre_topc(X0_58)
    | u1_struct_0(X0_58) = k2_struct_0(X0_58) ),
    inference(subtyping,[status(esa)],[c_439])).

cnf(c_4335,plain,
    ( u1_struct_0(X0_58) = k2_struct_0(X0_58)
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3377])).

cnf(c_5702,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_4333,c_4335])).

cnf(c_3380,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_35])).

cnf(c_4332,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3380])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_675,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_38])).

cnf(c_676,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | k7_tmap_1(sK1,X0) = k6_partfun1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_675])).

cnf(c_680,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k7_tmap_1(sK1,X0) = k6_partfun1(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_676,c_37,c_36])).

cnf(c_3363,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1)))
    | k7_tmap_1(sK1,X0_55) = k6_partfun1(u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_680])).

cnf(c_4349,plain,
    ( k7_tmap_1(sK1,X0_55) = k6_partfun1(u1_struct_0(sK1))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3363])).

cnf(c_5471,plain,
    ( k7_tmap_1(sK1,sK2) = k6_partfun1(u1_struct_0(sK1)) ),
    inference(superposition,[status(thm)],[c_4332,c_4349])).

cnf(c_5776,plain,
    ( k7_tmap_1(sK1,sK2) = k6_partfun1(k2_struct_0(sK1)) ),
    inference(demodulation,[status(thm)],[c_5702,c_5471])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_567,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_38])).

cnf(c_568,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(k6_tmap_1(sK1,X0)) = u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_567])).

cnf(c_572,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | u1_struct_0(k6_tmap_1(sK1,X0)) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_568,c_37,c_36])).

cnf(c_3369,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1)))
    | u1_struct_0(k6_tmap_1(sK1,X0_55)) = u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_572])).

cnf(c_4343,plain,
    ( u1_struct_0(k6_tmap_1(sK1,X0_55)) = u1_struct_0(sK1)
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3369])).

cnf(c_5255,plain,
    ( u1_struct_0(k6_tmap_1(sK1,sK2)) = u1_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_4332,c_4343])).

cnf(c_5778,plain,
    ( u1_struct_0(k6_tmap_1(sK1,sK2)) = k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_5702,c_5255])).

cnf(c_6472,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6469,c_5776,c_5778])).

cnf(c_4348,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,X0_55)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3364])).

cnf(c_5207,plain,
    ( l1_pre_topc(k6_tmap_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4332,c_4348])).

cnf(c_5703,plain,
    ( u1_struct_0(k6_tmap_1(sK1,sK2)) = k2_struct_0(k6_tmap_1(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_5207,c_4335])).

cnf(c_5704,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = u1_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_5703,c_5255])).

cnf(c_5705,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_5702,c_5704])).

cnf(c_6473,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6472,c_5705])).

cnf(c_5777,plain,
    ( k7_tmap_1(sK1,X0_55) = k6_partfun1(k2_struct_0(sK1))
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5702,c_4349])).

cnf(c_7438,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | k7_tmap_1(sK1,sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))) = k6_partfun1(k2_struct_0(sK1))
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6473,c_5777])).

cnf(c_3399,plain,
    ( X0_55 = X0_55 ),
    theory(equality)).

cnf(c_3445,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_3399])).

cnf(c_27,plain,
    ( v3_pre_topc(X0,k6_tmap_1(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X0))))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_546,plain,
    ( v3_pre_topc(X0,k6_tmap_1(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X0))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_38])).

cnf(c_547,plain,
    ( v3_pre_topc(X0,k6_tmap_1(sK1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_546])).

cnf(c_551,plain,
    ( v3_pre_topc(X0,k6_tmap_1(sK1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_547,c_37,c_36])).

cnf(c_3370,plain,
    ( v3_pre_topc(X0_55,k6_tmap_1(sK1,X0_55))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0_55))))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_551])).

cnf(c_3509,plain,
    ( v3_pre_topc(X0_55,k6_tmap_1(sK1,X0_55)) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0_55)))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3370])).

cnf(c_3511,plain,
    ( v3_pre_topc(sK2,k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3509])).

cnf(c_3513,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | u1_struct_0(k6_tmap_1(sK1,sK2)) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_3369])).

cnf(c_3411,plain,
    ( ~ m1_subset_1(X0_55,X0_56)
    | m1_subset_1(X1_55,X1_56)
    | X1_56 != X0_56
    | X1_55 != X0_55 ),
    theory(equality)).

cnf(c_4426,plain,
    ( ~ m1_subset_1(X0_55,X0_56)
    | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X1_55))))
    | k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X1_55))) != X0_56
    | X1_55 != X0_55 ),
    inference(instantiation,[status(thm)],[c_3411])).

cnf(c_4448,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0_55))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0_55))) != k1_zfmisc_1(u1_struct_0(sK1))
    | X0_55 != sK2 ),
    inference(instantiation,[status(thm)],[c_4426])).

cnf(c_4449,plain,
    ( k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0_55))) != k1_zfmisc_1(u1_struct_0(sK1))
    | X0_55 != sK2
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0_55)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4448])).

cnf(c_4451,plain,
    ( k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2))) != k1_zfmisc_1(u1_struct_0(sK1))
    | sK2 != sK2
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4449])).

cnf(c_3410,plain,
    ( X0_57 != X1_57
    | k1_zfmisc_1(X0_57) = k1_zfmisc_1(X1_57) ),
    theory(equality)).

cnf(c_4504,plain,
    ( u1_struct_0(k6_tmap_1(sK1,X0_55)) != u1_struct_0(sK1)
    | k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0_55))) = k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_3410])).

cnf(c_4505,plain,
    ( u1_struct_0(k6_tmap_1(sK1,sK2)) != u1_struct_0(sK1)
    | k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2))) = k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_4504])).

cnf(c_5785,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5702,c_4332])).

cnf(c_34,negated_conjecture,
    ( v3_pre_topc(sK2,sK1)
    | v1_funct_1(k7_tmap_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_3381,negated_conjecture,
    ( v3_pre_topc(sK2,sK1)
    | v1_funct_1(k7_tmap_1(sK1,sK2)) ),
    inference(subtyping,[status(esa)],[c_34])).

cnf(c_4331,plain,
    ( v3_pre_topc(sK2,sK1) = iProver_top
    | v1_funct_1(k7_tmap_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3381])).

cnf(c_4491,plain,
    ( v1_funct_1(k7_tmap_1(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4331,c_42,c_3520])).

cnf(c_5565,plain,
    ( v1_funct_1(k6_partfun1(u1_struct_0(sK1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5471,c_4491])).

cnf(c_5899,plain,
    ( v1_funct_1(k6_partfun1(k2_struct_0(sK1))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5565,c_5702])).

cnf(c_30,negated_conjecture,
    ( ~ v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | ~ v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
    | ~ v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | ~ v1_funct_1(k7_tmap_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_3385,negated_conjecture,
    ( ~ v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | ~ v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
    | ~ v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | ~ v1_funct_1(k7_tmap_1(sK1,sK2)) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_4327,plain,
    ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3385])).

cnf(c_3501,plain,
    ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_3373])).

cnf(c_3519,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_funct_1(k7_tmap_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_3367])).

cnf(c_3522,plain,
    ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_3366])).

cnf(c_3595,negated_conjecture,
    ( ~ v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
    | ~ v3_pre_topc(sK2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3385,c_35,c_30,c_3501,c_3519,c_3522])).

cnf(c_3597,plain,
    ( v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(sK2,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3595])).

cnf(c_4422,plain,
    ( v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(sK2,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4327,c_3597])).

cnf(c_5566,plain,
    ( v5_pre_topc(k6_partfun1(u1_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(sK2,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5471,c_4422])).

cnf(c_5990,plain,
    ( v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(sK2,sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5566,c_5702])).

cnf(c_4339,plain,
    ( v1_funct_2(k7_tmap_1(sK1,X0_55),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_55))) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3373])).

cnf(c_6098,plain,
    ( v1_funct_2(k7_tmap_1(sK1,X0_55),k2_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_55))) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4339,c_5702])).

cnf(c_6536,plain,
    ( v1_funct_2(k6_partfun1(k2_struct_0(sK1)),k2_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5776,c_6098])).

cnf(c_6537,plain,
    ( v1_funct_2(k6_partfun1(k2_struct_0(sK1)),k2_struct_0(sK1),k2_struct_0(sK1)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6536,c_5778])).

cnf(c_4346,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK1,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_55))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3366])).

cnf(c_6103,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK1,X0_55),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_55))))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4346,c_5702])).

cnf(c_6535,plain,
    ( m1_subset_1(k6_partfun1(k2_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5776,c_6103])).

cnf(c_6538,plain,
    ( m1_subset_1(k6_partfun1(k2_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6535,c_5778])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k8_relset_1(X1,X1,k6_partfun1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_3396,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(X0_57))
    | k8_relset_1(X0_57,X0_57,k6_partfun1(X0_57),X0_55) = X0_55 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_4316,plain,
    ( k8_relset_1(X0_57,X0_57,k6_partfun1(X0_57),X0_55) = X0_55
    | m1_subset_1(X0_55,k1_zfmisc_1(X0_57)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3396])).

cnf(c_4628,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k6_partfun1(u1_struct_0(sK1)),sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_4332,c_4316])).

cnf(c_5783,plain,
    ( k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),k6_partfun1(k2_struct_0(sK1)),sK2) = sK2 ),
    inference(demodulation,[status(thm)],[c_5702,c_4628])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ v3_pre_topc(X3,X2)
    | v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_3386,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58))
    | ~ v5_pre_topc(X0_55,X0_58,X1_58)
    | ~ v3_pre_topc(X1_55,X1_58)
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_55,X1_55),X0_58)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(X1_58)))
    | ~ v1_funct_1(X0_55)
    | ~ l1_pre_topc(X0_58)
    | ~ l1_pre_topc(X1_58)
    | k2_struct_0(X1_58) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_4326,plain,
    ( k2_struct_0(X0_58) = k1_xboole_0
    | v1_funct_2(X0_55,u1_struct_0(X1_58),u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(X0_55,X1_58,X0_58) != iProver_top
    | v3_pre_topc(X1_55,X0_58) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X1_58),u1_struct_0(X0_58),X0_55,X1_55),X1_58) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X0_58)))) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(X0_58))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3386])).

cnf(c_5352,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | v5_pre_topc(X0_55,X0_58,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(X1_55,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_58),u1_struct_0(sK1),X0_55,X1_55),X0_58) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5255,c_4326])).

cnf(c_5371,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_55,X0_58,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(X1_55,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_58),u1_struct_0(sK1),X0_55,X1_55),X0_58) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5352,c_5255])).

cnf(c_10288,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK1)))) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_58),u1_struct_0(sK1),X0_55,X1_55),X0_58) = iProver_top
    | v3_pre_topc(X1_55,k6_tmap_1(sK1,sK2)) != iProver_top
    | v5_pre_topc(X0_55,X0_58,k6_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(sK1)) != iProver_top
    | k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5371,c_42,c_3529])).

cnf(c_10289,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_55,X0_58,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(X1_55,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_58),u1_struct_0(sK1),X0_55,X1_55),X0_58) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_10288])).

cnf(c_10294,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | v1_funct_2(X0_55,u1_struct_0(X0_58),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_55,X0_58,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(X1_55,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_58),k2_struct_0(sK1),X0_55,X1_55),X0_58) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),k2_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10289,c_5702])).

cnf(c_10295,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0_55,u1_struct_0(X0_58),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_55,X0_58,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(X1_55,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_58),k2_struct_0(sK1),X0_55,X1_55),X0_58) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),k2_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10294,c_5705])).

cnf(c_10299,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0_55,u1_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_55,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(X1_55,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_55,X1_55),sK1) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5702,c_10295])).

cnf(c_10304,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0_55,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_55,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(X1_55,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_55,X1_55),sK1) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10299,c_5702])).

cnf(c_10650,plain,
    ( v1_funct_1(X0_55) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_55,X1_55),sK1) = iProver_top
    | v3_pre_topc(X1_55,k6_tmap_1(sK1,sK2)) != iProver_top
    | v5_pre_topc(X0_55,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_2(X0_55,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | k2_struct_0(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10304,c_41])).

cnf(c_10651,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0_55,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_55,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(X1_55,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_55,X1_55),sK1) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_10650])).

cnf(c_10656,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(k6_partfun1(k2_struct_0(sK1)),k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(sK2,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(sK2,sK1) = iProver_top
    | m1_subset_1(k6_partfun1(k2_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v1_funct_1(k6_partfun1(k2_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5783,c_10651])).

cnf(c_14470,plain,
    ( k7_tmap_1(sK1,sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))) = k6_partfun1(k2_struct_0(sK1))
    | k2_struct_0(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7438,c_35,c_42,c_3445,c_3511,c_3513,c_4451,c_4505,c_5785,c_5899,c_5990,c_6537,c_6538,c_10656])).

cnf(c_14471,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | k7_tmap_1(sK1,sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))) = k6_partfun1(k2_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_14470])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | v3_pre_topc(sK0(X1,X2,X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_3390,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58))
    | v5_pre_topc(X0_55,X0_58,X1_58)
    | v3_pre_topc(sK0(X0_58,X1_58,X0_55),X1_58)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
    | ~ v1_funct_1(X0_55)
    | ~ l1_pre_topc(X0_58)
    | ~ l1_pre_topc(X1_58)
    | k2_struct_0(X1_58) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_4322,plain,
    ( k2_struct_0(X0_58) = k1_xboole_0
    | v1_funct_2(X0_55,u1_struct_0(X1_58),u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(X0_55,X1_58,X0_58) = iProver_top
    | v3_pre_topc(sK0(X1_58,X0_58,X0_55),X0_58) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X0_58)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3390])).

cnf(c_5361,plain,
    ( k2_struct_0(X0_58) = k1_xboole_0
    | v1_funct_2(X0_55,u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
    | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55),X0_58) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5255,c_4322])).

cnf(c_5362,plain,
    ( k2_struct_0(X0_58) = k1_xboole_0
    | v1_funct_2(X0_55,u1_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
    | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55),X0_58) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5361,c_5255])).

cnf(c_6829,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
    | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55),X0_58) = iProver_top
    | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
    | k2_struct_0(X0_58) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5362,c_42,c_3529])).

cnf(c_6830,plain,
    ( k2_struct_0(X0_58) = k1_xboole_0
    | v1_funct_2(X0_55,u1_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
    | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55),X0_58) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_6829])).

cnf(c_6835,plain,
    ( k2_struct_0(X0_58) = k1_xboole_0
    | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
    | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55),X0_58) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6830,c_5702])).

cnf(c_6839,plain,
    ( k2_struct_0(k6_tmap_1(sK1,X0_55)) = k1_xboole_0
    | v1_funct_2(k7_tmap_1(sK1,X0_55),k2_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_55))) != iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,X0_55),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_55)) = iProver_top
    | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_55),k7_tmap_1(sK1,X0_55)),k6_tmap_1(sK1,X0_55)) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK1,X0_55)) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,X0_55)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6103,c_6835])).

cnf(c_5780,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,X0_55)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5702,c_4348])).

cnf(c_4345,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK1,X0_55)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3367])).

cnf(c_5782,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK1,X0_55)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5702,c_4345])).

cnf(c_17497,plain,
    ( k2_struct_0(k6_tmap_1(sK1,X0_55)) = k1_xboole_0
    | v5_pre_topc(k7_tmap_1(sK1,X0_55),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_55)) = iProver_top
    | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_55),k7_tmap_1(sK1,X0_55)),k6_tmap_1(sK1,X0_55)) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6839,c_5780,c_5782,c_6098])).

cnf(c_17504,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))))) = k1_xboole_0
    | k2_struct_0(sK1) = k1_xboole_0
    | v5_pre_topc(k7_tmap_1(sK1,sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))))) = iProver_top
    | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))),k6_partfun1(k2_struct_0(sK1))),k6_tmap_1(sK1,sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))))) = iProver_top
    | m1_subset_1(sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_14471,c_17497])).

cnf(c_17503,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | v5_pre_topc(k7_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5776,c_17497])).

cnf(c_17505,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17503,c_5776])).

cnf(c_17506,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_17505,c_5705])).

cnf(c_18235,plain,
    ( v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k6_tmap_1(sK1,sK2)) = iProver_top
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | k2_struct_0(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_17506,c_5785])).

cnf(c_18236,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k6_tmap_1(sK1,sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_18235])).

cnf(c_32,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
    | v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_3383,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
    | v3_pre_topc(sK2,sK1) ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_4329,plain,
    ( v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3383])).

cnf(c_5564,plain,
    ( v5_pre_topc(k6_partfun1(u1_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(sK2,sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5471,c_4329])).

cnf(c_6286,plain,
    ( v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(sK2,sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5564,c_5702])).

cnf(c_5348,plain,
    ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5255,c_4573])).

cnf(c_5562,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5471,c_5348])).

cnf(c_7176,plain,
    ( m1_subset_1(k6_partfun1(k2_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5562,c_5702])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_3392,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58))
    | v5_pre_topc(X0_55,X0_58,X1_58)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_55,sK0(X0_58,X1_58,X0_55)),X0_58)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
    | ~ v1_funct_1(X0_55)
    | ~ l1_pre_topc(X0_58)
    | ~ l1_pre_topc(X1_58)
    | k2_struct_0(X1_58) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_4320,plain,
    ( k2_struct_0(X0_58) = k1_xboole_0
    | v1_funct_2(X0_55,u1_struct_0(X1_58),u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(X0_55,X1_58,X0_58) = iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X1_58),u1_struct_0(X0_58),X0_55,sK0(X1_58,X0_58,X0_55)),X1_58) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X0_58)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3392])).

cnf(c_5801,plain,
    ( k2_struct_0(X0_58) = k1_xboole_0
    | v1_funct_2(X0_55,u1_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(X0_55,sK1,X0_58) = iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0_58),X0_55,sK0(sK1,X0_58,X0_55)),sK1) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5702,c_4320])).

cnf(c_5808,plain,
    ( k2_struct_0(X0_58) = k1_xboole_0
    | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(X0_55,sK1,X0_58) = iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0_58),X0_55,sK0(sK1,X0_58,X0_55)),sK1) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5801,c_5702])).

cnf(c_9704,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0_58),X0_55,sK0(sK1,X0_58,X0_55)),sK1) != iProver_top
    | v5_pre_topc(X0_55,sK1,X0_58) = iProver_top
    | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
    | k2_struct_0(X0_58) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5808,c_41])).

cnf(c_9705,plain,
    ( k2_struct_0(X0_58) = k1_xboole_0
    | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(X0_55,sK1,X0_58) = iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0_58),X0_55,sK0(sK1,X0_58,X0_55)),sK1) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_9704])).

cnf(c_9708,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_55,sK1,sK1) = iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_55,sK0(sK1,sK1,X0_55)),sK1) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5702,c_9705])).

cnf(c_9712,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0_55,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_55,sK1,sK1) = iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_55,sK0(sK1,sK1,X0_55)),sK1) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9708,c_5702])).

cnf(c_9806,plain,
    ( v1_funct_1(X0_55) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_55,sK0(sK1,sK1,X0_55)),sK1) != iProver_top
    | v5_pre_topc(X0_55,sK1,sK1) = iProver_top
    | v1_funct_2(X0_55,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | k2_struct_0(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9712,c_41])).

cnf(c_9807,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0_55,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_55,sK1,sK1) = iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_55,sK0(sK1,sK1,X0_55)),sK1) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_9806])).

cnf(c_10658,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0_55,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_55,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v5_pre_topc(X0_55,sK1,sK1) = iProver_top
    | v3_pre_topc(sK0(sK1,sK1,X0_55),k6_tmap_1(sK1,sK2)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK1,X0_55),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(superposition,[status(thm)],[c_10651,c_9807])).

cnf(c_5803,plain,
    ( k2_struct_0(X0_58) = k1_xboole_0
    | v1_funct_2(X0_55,u1_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(X0_55,sK1,X0_58) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
    | m1_subset_1(sK0(sK1,X0_58,X0_55),k1_zfmisc_1(u1_struct_0(X0_58))) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5702,c_4324])).

cnf(c_5806,plain,
    ( k2_struct_0(X0_58) = k1_xboole_0
    | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(X0_55,sK1,X0_58) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
    | m1_subset_1(sK0(sK1,X0_58,X0_55),k1_zfmisc_1(u1_struct_0(X0_58))) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5803,c_5702])).

cnf(c_9589,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | m1_subset_1(sK0(sK1,X0_58,X0_55),k1_zfmisc_1(u1_struct_0(X0_58))) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
    | v5_pre_topc(X0_55,sK1,X0_58) = iProver_top
    | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
    | k2_struct_0(X0_58) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5806,c_41])).

cnf(c_9590,plain,
    ( k2_struct_0(X0_58) = k1_xboole_0
    | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(X0_55,sK1,X0_58) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
    | m1_subset_1(sK0(sK1,X0_58,X0_55),k1_zfmisc_1(u1_struct_0(X0_58))) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_9589])).

cnf(c_9594,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_55,sK1,sK1) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK1,X0_55),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5702,c_9590])).

cnf(c_9598,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0_55,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_55,sK1,sK1) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK1,X0_55),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9594,c_5702])).

cnf(c_9609,plain,
    ( v1_funct_1(X0_55) != iProver_top
    | m1_subset_1(sK0(sK1,sK1,X0_55),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | v5_pre_topc(X0_55,sK1,sK1) = iProver_top
    | v1_funct_2(X0_55,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | k2_struct_0(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9598,c_41])).

cnf(c_9610,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0_55,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_55,sK1,sK1) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK1,X0_55),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_9609])).

cnf(c_28047,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | v3_pre_topc(sK0(sK1,sK1,X0_55),k6_tmap_1(sK1,sK2)) != iProver_top
    | v5_pre_topc(X0_55,sK1,sK1) = iProver_top
    | v5_pre_topc(X0_55,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_2(X0_55,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_1(X0_55) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10658,c_9610])).

cnf(c_28048,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0_55,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_55,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v5_pre_topc(X0_55,sK1,sK1) = iProver_top
    | v3_pre_topc(sK0(sK1,sK1,X0_55),k6_tmap_1(sK1,sK2)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_28047])).

cnf(c_28053,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(k6_partfun1(k2_struct_0(sK1)),k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,sK1) = iProver_top
    | v3_pre_topc(sK0(sK1,sK1,k6_partfun1(k2_struct_0(sK1))),k6_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(k6_partfun1(k2_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7176,c_28048])).

cnf(c_28058,plain,
    ( v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | k2_struct_0(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_28053,c_35,c_42,c_3445,c_3511,c_3513,c_4451,c_4505,c_5785,c_5899,c_5990,c_6537,c_6538,c_10656])).

cnf(c_28059,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_28058])).

cnf(c_28062,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v3_pre_topc(sK2,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_6286,c_28059])).

cnf(c_29,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_504,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_38])).

cnf(c_505,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_504])).

cnf(c_509,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_505,c_37,c_36])).

cnf(c_3372,plain,
    ( ~ v3_pre_topc(X0_55,sK1)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1)))
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,X0_55) ),
    inference(subtyping,[status(esa)],[c_509])).

cnf(c_4340,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,X0_55)
    | v3_pre_topc(X0_55,sK1) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3372])).

cnf(c_6169,plain,
    ( g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,X0_55)
    | v3_pre_topc(X0_55,sK1) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4340,c_5702])).

cnf(c_6173,plain,
    ( g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,sK2)
    | v3_pre_topc(sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5785,c_6169])).

cnf(c_28171,plain,
    ( g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,sK2)
    | k2_struct_0(sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_28062,c_6173])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_3395,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58))
    | ~ v1_funct_2(X0_55,u1_struct_0(g1_pre_topc(u1_struct_0(X0_58),u1_pre_topc(X0_58))),u1_struct_0(X1_58))
    | v5_pre_topc(X0_55,X0_58,X1_58)
    | ~ v5_pre_topc(X0_55,g1_pre_topc(u1_struct_0(X0_58),u1_pre_topc(X0_58)),X1_58)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0_58),u1_pre_topc(X0_58))),u1_struct_0(X1_58))))
    | ~ v2_pre_topc(X1_58)
    | ~ v2_pre_topc(X0_58)
    | ~ v1_funct_1(X0_55)
    | ~ l1_pre_topc(X0_58)
    | ~ l1_pre_topc(X1_58) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_4317,plain,
    ( v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(g1_pre_topc(u1_struct_0(X0_58),u1_pre_topc(X0_58))),u1_struct_0(X1_58)) != iProver_top
    | v5_pre_topc(X0_55,X0_58,X1_58) = iProver_top
    | v5_pre_topc(X0_55,g1_pre_topc(u1_struct_0(X0_58),u1_pre_topc(X0_58)),X1_58) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0_58),u1_pre_topc(X0_58))),u1_struct_0(X1_58)))) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X1_58) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3395])).

cnf(c_5796,plain,
    ( v1_funct_2(X0_55,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(X0_55,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0_58) != iProver_top
    | v5_pre_topc(X0_55,sK1,X0_58) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X0_58)))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5702,c_4317])).

cnf(c_5813,plain,
    ( v1_funct_2(X0_55,u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(X0_55,g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X0_58) != iProver_top
    | v5_pre_topc(X0_55,sK1,X0_58) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X0_58)))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5796,c_5702])).

cnf(c_40,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_8135,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(X0_55,g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X0_58) != iProver_top
    | v5_pre_topc(X0_55,sK1,X0_58) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X0_58)))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5813,c_40,c_41])).

cnf(c_8136,plain,
    ( v1_funct_2(X0_55,u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(X0_55,g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X0_58) != iProver_top
    | v5_pre_topc(X0_55,sK1,X0_58) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X0_58)))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_8135])).

cnf(c_28179,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0_55,u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(X0_55,g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X0_58) != iProver_top
    | v5_pre_topc(X0_55,sK1,X0_58) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(X0_58)))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(superposition,[status(thm)],[c_28171,c_8136])).

cnf(c_28185,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0_55,u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(X0_55,g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X0_58) != iProver_top
    | v5_pre_topc(X0_55,sK1,X0_58) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_28179,c_5778])).

cnf(c_33191,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0_55,u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(X0_55,g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X0_58) != iProver_top
    | v5_pre_topc(X0_55,sK1,X0_58) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(superposition,[status(thm)],[c_28171,c_28185])).

cnf(c_33198,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(X0_55,g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X0_58) != iProver_top
    | v5_pre_topc(X0_55,sK1,X0_58) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_33191,c_5778])).

cnf(c_33474,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(k7_tmap_1(sK1,X0_55),k2_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_55))) != iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,X0_55),g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),k6_tmap_1(sK1,X0_55)) != iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,X0_55),sK1,k6_tmap_1(sK1,X0_55)) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v2_pre_topc(k6_tmap_1(sK1,X0_55)) != iProver_top
    | v1_funct_1(k7_tmap_1(sK1,X0_55)) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,X0_55)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6103,c_33198])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k6_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_639,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k6_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_38])).

cnf(c_640,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_pre_topc(k6_tmap_1(sK1,X0))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_639])).

cnf(c_644,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_pre_topc(k6_tmap_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_640,c_37,c_36])).

cnf(c_3365,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_pre_topc(k6_tmap_1(sK1,X0_55)) ),
    inference(subtyping,[status(esa)],[c_644])).

cnf(c_4347,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_pre_topc(k6_tmap_1(sK1,X0_55)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3365])).

cnf(c_5781,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v2_pre_topc(k6_tmap_1(sK1,X0_55)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5702,c_4347])).

cnf(c_34073,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,X0_55),sK1,k6_tmap_1(sK1,X0_55)) = iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,X0_55),g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),k6_tmap_1(sK1,X0_55)) != iProver_top
    | k2_struct_0(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_33474,c_5780,c_5781,c_5782,c_6098])).

cnf(c_34074,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v5_pre_topc(k7_tmap_1(sK1,X0_55),g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),k6_tmap_1(sK1,X0_55)) != iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,X0_55),sK1,k6_tmap_1(sK1,X0_55)) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_34073])).

cnf(c_34081,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),k6_tmap_1(sK1,sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5776,c_34074])).

cnf(c_34084,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),k6_tmap_1(sK1,sK2)) != iProver_top
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_34081,c_5776])).

cnf(c_34092,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_34084,c_5785,c_28059])).

cnf(c_34097,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_28171,c_34092])).

cnf(c_5360,plain,
    ( k2_struct_0(X0_58) = k1_xboole_0
    | v1_funct_2(X0_55,u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
    | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55),k1_zfmisc_1(u1_struct_0(X0_58))) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5255,c_4324])).

cnf(c_5363,plain,
    ( k2_struct_0(X0_58) = k1_xboole_0
    | v1_funct_2(X0_55,u1_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
    | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55),k1_zfmisc_1(u1_struct_0(X0_58))) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5360,c_5255])).

cnf(c_7623,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55),k1_zfmisc_1(u1_struct_0(X0_58))) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
    | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
    | k2_struct_0(X0_58) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5363,c_42,c_3529])).

cnf(c_7624,plain,
    ( k2_struct_0(X0_58) = k1_xboole_0
    | v1_funct_2(X0_55,u1_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
    | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55),k1_zfmisc_1(u1_struct_0(X0_58))) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_7623])).

cnf(c_7629,plain,
    ( k2_struct_0(X0_58) = k1_xboole_0
    | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
    | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55),k1_zfmisc_1(u1_struct_0(X0_58))) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7624,c_5702])).

cnf(c_7635,plain,
    ( k2_struct_0(X0_58) = k1_xboole_0
    | k8_relset_1(u1_struct_0(X0_58),u1_struct_0(X0_58),k6_partfun1(u1_struct_0(X0_58)),sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55)) = sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55)
    | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(superposition,[status(thm)],[c_7629,c_4316])).

cnf(c_7649,plain,
    ( k2_struct_0(k6_tmap_1(sK1,X0_55)) = k1_xboole_0
    | k8_relset_1(u1_struct_0(k6_tmap_1(sK1,X0_55)),u1_struct_0(k6_tmap_1(sK1,X0_55)),k6_partfun1(u1_struct_0(k6_tmap_1(sK1,X0_55))),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_55),k7_tmap_1(sK1,X0_55))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_55),k7_tmap_1(sK1,X0_55))
    | v1_funct_2(k7_tmap_1(sK1,X0_55),k2_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_55))) != iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,X0_55),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_55)) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK1,X0_55)) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,X0_55)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6103,c_7635])).

cnf(c_12459,plain,
    ( k8_relset_1(u1_struct_0(k6_tmap_1(sK1,X0_55)),u1_struct_0(k6_tmap_1(sK1,X0_55)),k6_partfun1(u1_struct_0(k6_tmap_1(sK1,X0_55))),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_55),k7_tmap_1(sK1,X0_55))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_55),k7_tmap_1(sK1,X0_55))
    | k2_struct_0(k6_tmap_1(sK1,X0_55)) = k1_xboole_0
    | v5_pre_topc(k7_tmap_1(sK1,X0_55),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_55)) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7649,c_5780,c_5782,c_6098])).

cnf(c_12460,plain,
    ( k2_struct_0(k6_tmap_1(sK1,X0_55)) = k1_xboole_0
    | k8_relset_1(u1_struct_0(k6_tmap_1(sK1,X0_55)),u1_struct_0(k6_tmap_1(sK1,X0_55)),k6_partfun1(u1_struct_0(k6_tmap_1(sK1,X0_55))),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_55),k7_tmap_1(sK1,X0_55))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_55),k7_tmap_1(sK1,X0_55))
    | v5_pre_topc(k7_tmap_1(sK1,X0_55),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_55)) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_12459])).

cnf(c_12465,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | k8_relset_1(u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(k6_tmap_1(sK1,sK2)),k6_partfun1(u1_struct_0(k6_tmap_1(sK1,sK2))),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2))
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5776,c_12460])).

cnf(c_12466,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),k6_partfun1(k2_struct_0(sK1)),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12465,c_5776,c_5778])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_3397,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | k8_relset_1(X0_57,X1_57,X0_55,X1_55) = k10_relat_1(X0_55,X1_55) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_4315,plain,
    ( k8_relset_1(X0_57,X1_57,X0_55,X1_55) = k10_relat_1(X0_55,X1_55)
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3397])).

cnf(c_4624,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)),k7_tmap_1(sK1,sK2),X0_55) = k10_relat_1(k7_tmap_1(sK1,sK2),X0_55) ),
    inference(superposition,[status(thm)],[c_4573,c_4315])).

cnf(c_5987,plain,
    ( k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),k6_partfun1(k2_struct_0(sK1)),X0_55) = k10_relat_1(k6_partfun1(k2_struct_0(sK1)),X0_55) ),
    inference(light_normalisation,[status(thm)],[c_4624,c_4624,c_5702,c_5776,c_5778])).

cnf(c_12467,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | k10_relat_1(k6_partfun1(k2_struct_0(sK1)),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12466,c_5705,c_5987])).

cnf(c_16483,plain,
    ( v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | k10_relat_1(k6_partfun1(k2_struct_0(sK1)),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))
    | k2_struct_0(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12467,c_5785])).

cnf(c_16484,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | k10_relat_1(k6_partfun1(k2_struct_0(sK1)),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_16483])).

cnf(c_59499,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | k10_relat_1(k6_partfun1(k2_struct_0(sK1)),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))) ),
    inference(superposition,[status(thm)],[c_16484,c_34097])).

cnf(c_5358,plain,
    ( k2_struct_0(X0_58) = k1_xboole_0
    | v1_funct_2(X0_55,u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0_58),X0_55,sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55)),k6_tmap_1(sK1,sK2)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(X0_58)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5255,c_4320])).

cnf(c_5365,plain,
    ( k2_struct_0(X0_58) = k1_xboole_0
    | v1_funct_2(X0_55,u1_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0_58),X0_55,sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55)),k6_tmap_1(sK1,sK2)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5358,c_5255])).

cnf(c_8511,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0_58),X0_55,sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55)),k6_tmap_1(sK1,sK2)) != iProver_top
    | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
    | k2_struct_0(X0_58) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5365,c_42,c_3529])).

cnf(c_8512,plain,
    ( k2_struct_0(X0_58) = k1_xboole_0
    | v1_funct_2(X0_55,u1_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0_58),X0_55,sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55)),k6_tmap_1(sK1,sK2)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_8511])).

cnf(c_8517,plain,
    ( k2_struct_0(X0_58) = k1_xboole_0
    | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0_58),X0_55,sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55)),k6_tmap_1(sK1,sK2)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8512,c_5702])).

cnf(c_8522,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_55,sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_55)),k6_tmap_1(sK1,sK2)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5778,c_8517])).

cnf(c_8523,plain,
    ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
    | v1_funct_2(X0_55,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_55,sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_55)),k6_tmap_1(sK1,sK2)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8522,c_5778])).

cnf(c_8524,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0_55,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_55,sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_55)),k6_tmap_1(sK1,sK2)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8523,c_5705])).

cnf(c_23462,plain,
    ( v1_funct_1(X0_55) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_55,sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_55)),k6_tmap_1(sK1,sK2)) != iProver_top
    | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(X0_55,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | k2_struct_0(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8524,c_42,c_3529])).

cnf(c_23463,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(X0_55,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_55,sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_55)),k6_tmap_1(sK1,sK2)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_23462])).

cnf(c_23469,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(k6_partfun1(k2_struct_0(sK1)),k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK1)),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))),k6_tmap_1(sK1,sK2)) != iProver_top
    | m1_subset_1(k6_partfun1(k2_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k6_partfun1(k2_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5987,c_23463])).

cnf(c_29663,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK1)),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))),k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_23469,c_5785,c_5899,c_6537,c_6538])).

cnf(c_89212,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_59499,c_29663])).

cnf(c_89489,plain,
    ( k2_struct_0(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_17504,c_18236,c_34097,c_89212])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | v3_pre_topc(sK0(X1,X2,X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_3391,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58))
    | v5_pre_topc(X0_55,X0_58,X1_58)
    | v3_pre_topc(sK0(X0_58,X1_58,X0_55),X1_58)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
    | ~ v1_funct_1(X0_55)
    | ~ l1_pre_topc(X0_58)
    | ~ l1_pre_topc(X1_58)
    | k2_struct_0(X0_58) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_4321,plain,
    ( k2_struct_0(X0_58) != k1_xboole_0
    | v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
    | v5_pre_topc(X0_55,X0_58,X1_58) = iProver_top
    | v3_pre_topc(sK0(X0_58,X1_58,X0_55),X1_58) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3391])).

cnf(c_6518,plain,
    ( k2_struct_0(sK1) != k1_xboole_0
    | v1_funct_2(X0_55,u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
    | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55),X0_58) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(X0_58)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5705,c_4321])).

cnf(c_6519,plain,
    ( k2_struct_0(sK1) != k1_xboole_0
    | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
    | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55),X0_58) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6518,c_5778])).

cnf(c_10963,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
    | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55),X0_58) = iProver_top
    | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
    | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
    | k2_struct_0(sK1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6519,c_42,c_3529])).

cnf(c_10964,plain,
    ( k2_struct_0(sK1) != k1_xboole_0
    | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
    | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55),X0_58) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_10963])).

cnf(c_89982,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v1_funct_2(X0_55,k1_xboole_0,u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
    | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55),X0_58) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0_58)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(demodulation,[status(thm)],[c_89489,c_10964])).

cnf(c_90040,plain,
    ( v1_funct_2(X0_55,k1_xboole_0,u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
    | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55),X0_58) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0_58)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_89982])).

cnf(c_90024,plain,
    ( k7_tmap_1(sK1,sK2) = k6_partfun1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_89489,c_5776])).

cnf(c_90032,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k7_tmap_1(sK1,X0_55),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,X0_55))))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_89489,c_6103])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_3389,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58))
    | v5_pre_topc(X0_55,X0_58,X1_58)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
    | m1_subset_1(sK0(X0_58,X1_58,X0_55),k1_zfmisc_1(u1_struct_0(X1_58)))
    | ~ v1_funct_1(X0_55)
    | ~ l1_pre_topc(X0_58)
    | ~ l1_pre_topc(X1_58)
    | k2_struct_0(X0_58) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_4323,plain,
    ( k2_struct_0(X0_58) != k1_xboole_0
    | v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
    | v5_pre_topc(X0_55,X0_58,X1_58) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
    | m1_subset_1(sK0(X0_58,X1_58,X0_55),k1_zfmisc_1(u1_struct_0(X1_58))) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3389])).

cnf(c_6517,plain,
    ( k2_struct_0(sK1) != k1_xboole_0
    | v1_funct_2(X0_55,u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(X0_58)))) != iProver_top
    | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55),k1_zfmisc_1(u1_struct_0(X0_58))) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5705,c_4323])).

cnf(c_6520,plain,
    ( k2_struct_0(sK1) != k1_xboole_0
    | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
    | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55),k1_zfmisc_1(u1_struct_0(X0_58))) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6517,c_5778])).

cnf(c_11153,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55),k1_zfmisc_1(u1_struct_0(X0_58))) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
    | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
    | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
    | k2_struct_0(sK1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6520,c_42,c_3529])).

cnf(c_11154,plain,
    ( k2_struct_0(sK1) != k1_xboole_0
    | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
    | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55),k1_zfmisc_1(u1_struct_0(X0_58))) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_11153])).

cnf(c_89981,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v1_funct_2(X0_55,k1_xboole_0,u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0_58)))) != iProver_top
    | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55),k1_zfmisc_1(u1_struct_0(X0_58))) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(demodulation,[status(thm)],[c_89489,c_11154])).

cnf(c_90041,plain,
    ( v1_funct_2(X0_55,k1_xboole_0,u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0_58)))) != iProver_top
    | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55),k1_zfmisc_1(u1_struct_0(X0_58))) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_89981])).

cnf(c_126577,plain,
    ( k8_relset_1(u1_struct_0(X0_58),u1_struct_0(X0_58),k6_partfun1(u1_struct_0(X0_58)),sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55)) = sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55)
    | v1_funct_2(X0_55,k1_xboole_0,u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0_58)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(superposition,[status(thm)],[c_90041,c_4316])).

cnf(c_127525,plain,
    ( k8_relset_1(u1_struct_0(k6_tmap_1(sK1,X0_55)),u1_struct_0(k6_tmap_1(sK1,X0_55)),k6_partfun1(u1_struct_0(k6_tmap_1(sK1,X0_55))),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_55),k7_tmap_1(sK1,X0_55))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_55),k7_tmap_1(sK1,X0_55))
    | v1_funct_2(k7_tmap_1(sK1,X0_55),k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,X0_55))) != iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,X0_55),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_55)) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k7_tmap_1(sK1,X0_55)) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,X0_55)) != iProver_top ),
    inference(superposition,[status(thm)],[c_90032,c_126577])).

cnf(c_90012,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k7_tmap_1(sK1,X0_55)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_89489,c_5782])).

cnf(c_90014,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,X0_55)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_89489,c_5780])).

cnf(c_90033,plain,
    ( v1_funct_2(k7_tmap_1(sK1,X0_55),k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,X0_55))) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_89489,c_6098])).

cnf(c_128142,plain,
    ( k8_relset_1(u1_struct_0(k6_tmap_1(sK1,X0_55)),u1_struct_0(k6_tmap_1(sK1,X0_55)),k6_partfun1(u1_struct_0(k6_tmap_1(sK1,X0_55))),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_55),k7_tmap_1(sK1,X0_55))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_55),k7_tmap_1(sK1,X0_55))
    | v5_pre_topc(k7_tmap_1(sK1,X0_55),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_55)) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_127525,c_90012,c_90014,c_90033])).

cnf(c_128148,plain,
    ( k8_relset_1(u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(k6_tmap_1(sK1,sK2)),k6_partfun1(u1_struct_0(k6_tmap_1(sK1,sK2))),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2))
    | v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_90024,c_128142])).

cnf(c_90023,plain,
    ( u1_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_89489,c_5778])).

cnf(c_128162,plain,
    ( k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k1_xboole_0))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k1_xboole_0))
    | v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_128148,c_90023,c_90024])).

cnf(c_90035,plain,
    ( k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),X0_55) = k10_relat_1(k6_partfun1(k1_xboole_0),X0_55) ),
    inference(demodulation,[status(thm)],[c_89489,c_5987])).

cnf(c_128163,plain,
    ( k10_relat_1(k6_partfun1(k1_xboole_0),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k1_xboole_0))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k1_xboole_0))
    | v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_128162,c_90035])).

cnf(c_3401,plain,
    ( X0_57 = X0_57 ),
    theory(equality)).

cnf(c_3447,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3401])).

cnf(c_3495,plain,
    ( ~ l1_pre_topc(sK1)
    | u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_3377])).

cnf(c_3531,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k7_tmap_1(sK1,sK2) = k6_partfun1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_3363])).

cnf(c_4469,plain,
    ( m1_subset_1(X0_55,X0_56)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | X0_56 != k1_zfmisc_1(u1_struct_0(sK1))
    | X0_55 != sK2 ),
    inference(instantiation,[status(thm)],[c_3411])).

cnf(c_4523,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(X0_57))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_zfmisc_1(X0_57) != k1_zfmisc_1(u1_struct_0(sK1))
    | X0_55 != sK2 ),
    inference(instantiation,[status(thm)],[c_4469])).

cnf(c_4524,plain,
    ( k1_zfmisc_1(X0_57) != k1_zfmisc_1(u1_struct_0(sK1))
    | X0_55 != sK2
    | m1_subset_1(X0_55,k1_zfmisc_1(X0_57)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4523])).

cnf(c_4526,plain,
    ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(u1_struct_0(sK1))
    | sK2 != sK2
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4524])).

cnf(c_3404,plain,
    ( X0_55 != X1_55
    | X2_55 != X1_55
    | X2_55 = X0_55 ),
    theory(equality)).

cnf(c_4485,plain,
    ( X0_55 != X1_55
    | X0_55 = k7_tmap_1(sK1,sK2)
    | k7_tmap_1(sK1,sK2) != X1_55 ),
    inference(instantiation,[status(thm)],[c_3404])).

cnf(c_4529,plain,
    ( X0_55 = k7_tmap_1(sK1,sK2)
    | X0_55 != k6_partfun1(u1_struct_0(sK1))
    | k7_tmap_1(sK1,sK2) != k6_partfun1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_4485])).

cnf(c_4662,plain,
    ( k7_tmap_1(sK1,sK2) != k6_partfun1(u1_struct_0(sK1))
    | k6_partfun1(u1_struct_0(sK1)) = k7_tmap_1(sK1,sK2)
    | k6_partfun1(u1_struct_0(sK1)) != k6_partfun1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_4529])).

cnf(c_4705,plain,
    ( X0_57 != u1_struct_0(sK1)
    | k1_zfmisc_1(X0_57) = k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_3410])).

cnf(c_4706,plain,
    ( k1_xboole_0 != u1_struct_0(sK1)
    | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_4705])).

cnf(c_4800,plain,
    ( k6_partfun1(u1_struct_0(sK1)) = k6_partfun1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_3399])).

cnf(c_3412,plain,
    ( X0_57 != X1_57
    | k6_partfun1(X0_57) = k6_partfun1(X1_57) ),
    theory(equality)).

cnf(c_4808,plain,
    ( X0_57 != u1_struct_0(sK1)
    | k6_partfun1(X0_57) = k6_partfun1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_3412])).

cnf(c_4809,plain,
    ( k1_xboole_0 != u1_struct_0(sK1)
    | k6_partfun1(k1_xboole_0) = k6_partfun1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_4808])).

cnf(c_3405,plain,
    ( X0_57 != X1_57
    | X2_57 != X1_57
    | X2_57 = X0_57 ),
    theory(equality)).

cnf(c_5049,plain,
    ( k2_struct_0(sK1) != X0_57
    | k1_xboole_0 != X0_57
    | k1_xboole_0 = k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_3405])).

cnf(c_5050,plain,
    ( k2_struct_0(sK1) != k1_xboole_0
    | k1_xboole_0 = k2_struct_0(sK1)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5049])).

cnf(c_3419,plain,
    ( ~ v1_funct_1(X0_55)
    | v1_funct_1(X1_55)
    | X1_55 != X0_55 ),
    theory(equality)).

cnf(c_4687,plain,
    ( v1_funct_1(X0_55)
    | ~ v1_funct_1(k7_tmap_1(sK1,X1_55))
    | X0_55 != k7_tmap_1(sK1,X1_55) ),
    inference(instantiation,[status(thm)],[c_3419])).

cnf(c_5276,plain,
    ( ~ v1_funct_1(k7_tmap_1(sK1,X0_55))
    | v1_funct_1(k6_partfun1(u1_struct_0(sK1)))
    | k6_partfun1(u1_struct_0(sK1)) != k7_tmap_1(sK1,X0_55) ),
    inference(instantiation,[status(thm)],[c_4687])).

cnf(c_5287,plain,
    ( k6_partfun1(u1_struct_0(sK1)) != k7_tmap_1(sK1,X0_55)
    | v1_funct_1(k7_tmap_1(sK1,X0_55)) != iProver_top
    | v1_funct_1(k6_partfun1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5276])).

cnf(c_5289,plain,
    ( k6_partfun1(u1_struct_0(sK1)) != k7_tmap_1(sK1,sK2)
    | v1_funct_1(k7_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(k6_partfun1(u1_struct_0(sK1))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5287])).

cnf(c_5909,plain,
    ( v1_funct_1(X0_55)
    | ~ v1_funct_1(k6_partfun1(u1_struct_0(sK1)))
    | X0_55 != k6_partfun1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_3419])).

cnf(c_6244,plain,
    ( v1_funct_1(k6_partfun1(X0_57))
    | ~ v1_funct_1(k6_partfun1(u1_struct_0(sK1)))
    | k6_partfun1(X0_57) != k6_partfun1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_5909])).

cnf(c_6245,plain,
    ( k6_partfun1(X0_57) != k6_partfun1(u1_struct_0(sK1))
    | v1_funct_1(k6_partfun1(X0_57)) = iProver_top
    | v1_funct_1(k6_partfun1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6244])).

cnf(c_6247,plain,
    ( k6_partfun1(k1_xboole_0) != k6_partfun1(u1_struct_0(sK1))
    | v1_funct_1(k6_partfun1(u1_struct_0(sK1))) != iProver_top
    | v1_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6245])).

cnf(c_5250,plain,
    ( X0_57 != X1_57
    | X0_57 = u1_struct_0(sK1)
    | u1_struct_0(sK1) != X1_57 ),
    inference(instantiation,[status(thm)],[c_3405])).

cnf(c_7125,plain,
    ( X0_57 = u1_struct_0(sK1)
    | X0_57 != k2_struct_0(sK1)
    | u1_struct_0(sK1) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_5250])).

cnf(c_7126,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | k1_xboole_0 = u1_struct_0(sK1)
    | k1_xboole_0 != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_7125])).

cnf(c_90015,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_89489,c_7176])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_3382,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
    | v3_pre_topc(sK2,sK1) ),
    inference(subtyping,[status(esa)],[c_33])).

cnf(c_4330,plain,
    ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) = iProver_top
    | v3_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3382])).

cnf(c_4568,plain,
    ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4330,c_42,c_3502])).

cnf(c_5349,plain,
    ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5255,c_4568])).

cnf(c_5563,plain,
    ( v1_funct_2(k6_partfun1(u1_struct_0(sK1)),u1_struct_0(sK1),u1_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5471,c_5349])).

cnf(c_7066,plain,
    ( v1_funct_2(k6_partfun1(k2_struct_0(sK1)),k2_struct_0(sK1),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5563,c_5702])).

cnf(c_90017,plain,
    ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_89489,c_7066])).

cnf(c_90034,plain,
    ( v5_pre_topc(k6_partfun1(k1_xboole_0),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(sK2,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_89489,c_5990])).

cnf(c_90016,plain,
    ( k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK2) = sK2 ),
    inference(demodulation,[status(thm)],[c_89489,c_5783])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ v3_pre_topc(X3,X2)
    | v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_3387,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58))
    | ~ v5_pre_topc(X0_55,X0_58,X1_58)
    | ~ v3_pre_topc(X1_55,X1_58)
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_55,X1_55),X0_58)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(X1_58)))
    | ~ v1_funct_1(X0_55)
    | ~ l1_pre_topc(X0_58)
    | ~ l1_pre_topc(X1_58)
    | k2_struct_0(X0_58) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_4325,plain,
    ( k2_struct_0(X0_58) != k1_xboole_0
    | v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
    | v5_pre_topc(X0_55,X0_58,X1_58) != iProver_top
    | v3_pre_topc(X1_55,X1_58) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_55,X1_55),X0_58) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(X1_58))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3387])).

cnf(c_90177,plain,
    ( v1_funct_2(X0_55,u1_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(X0_55,sK1,X0_58) != iProver_top
    | v3_pre_topc(X1_55,X0_58) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0_58),X0_55,X1_55),sK1) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(X0_58))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_89489,c_4325])).

cnf(c_90039,plain,
    ( u1_struct_0(sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_89489,c_5702])).

cnf(c_90184,plain,
    ( v1_funct_2(X0_55,k1_xboole_0,u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(X0_55,sK1,X0_58) != iProver_top
    | v3_pre_topc(X1_55,X0_58) != iProver_top
    | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X0_58),X0_55,X1_55),sK1) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0_58)))) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(X0_58))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_90177,c_90039])).

cnf(c_93374,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(X0_58))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0_58)))) != iProver_top
    | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X0_58),X0_55,X1_55),sK1) = iProver_top
    | v3_pre_topc(X1_55,X0_58) != iProver_top
    | v5_pre_topc(X0_55,sK1,X0_58) != iProver_top
    | v1_funct_2(X0_55,k1_xboole_0,u1_struct_0(X0_58)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_90184,c_41])).

cnf(c_93375,plain,
    ( v1_funct_2(X0_55,k1_xboole_0,u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(X0_55,sK1,X0_58) != iProver_top
    | v3_pre_topc(X1_55,X0_58) != iProver_top
    | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X0_58),X0_55,X1_55),sK1) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0_58)))) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(X0_58))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_93374])).

cnf(c_93379,plain,
    ( v1_funct_2(X0_55,k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | v5_pre_topc(X0_55,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(X1_55,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0_55,X1_55),sK1) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_90023,c_93375])).

cnf(c_93381,plain,
    ( v1_funct_2(X0_55,k1_xboole_0,k1_xboole_0) != iProver_top
    | v5_pre_topc(X0_55,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(X1_55,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0_55,X1_55),sK1) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_93379,c_90023])).

cnf(c_97184,plain,
    ( v1_funct_1(X0_55) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0_55,X1_55),sK1) = iProver_top
    | v3_pre_topc(X1_55,k6_tmap_1(sK1,sK2)) != iProver_top
    | v5_pre_topc(X0_55,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_2(X0_55,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_93381,c_42,c_3529])).

cnf(c_97185,plain,
    ( v1_funct_2(X0_55,k1_xboole_0,k1_xboole_0) != iProver_top
    | v5_pre_topc(X0_55,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(X1_55,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0_55,X1_55),sK1) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_97184])).

cnf(c_97190,plain,
    ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) != iProver_top
    | v5_pre_topc(k6_partfun1(k1_xboole_0),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(sK2,k6_tmap_1(sK1,sK2)) != iProver_top
    | v3_pre_topc(sK2,sK1) = iProver_top
    | m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_90016,c_97185])).

cnf(c_90028,plain,
    ( v5_pre_topc(k6_partfun1(k1_xboole_0),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(sK2,sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_89489,c_6286])).

cnf(c_97361,plain,
    ( v3_pre_topc(sK2,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_97190,c_36,c_35,c_42,c_3445,c_3447,c_3495,c_3511,c_3513,c_3520,c_3531,c_4451,c_4505,c_4526,c_4662,c_4706,c_4800,c_4809,c_5050,c_5289,c_6247,c_7126,c_18236,c_34097,c_89212,c_90015,c_90017,c_90028])).

cnf(c_90009,plain,
    ( g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)) = k6_tmap_1(sK1,sK2)
    | v3_pre_topc(sK2,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_89489,c_6173])).

cnf(c_97365,plain,
    ( g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)) = k6_tmap_1(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_97361,c_90009])).

cnf(c_5359,plain,
    ( v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(g1_pre_topc(u1_struct_0(X0_58),u1_pre_topc(X0_58))),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | v5_pre_topc(X0_55,X0_58,k6_tmap_1(sK1,sK2)) = iProver_top
    | v5_pre_topc(X0_55,g1_pre_topc(u1_struct_0(X0_58),u1_pre_topc(X0_58)),k6_tmap_1(sK1,sK2)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0_58),u1_pre_topc(X0_58))),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5255,c_4317])).

cnf(c_5364,plain,
    ( v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(g1_pre_topc(u1_struct_0(X0_58),u1_pre_topc(X0_58))),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_55,X0_58,k6_tmap_1(sK1,sK2)) = iProver_top
    | v5_pre_topc(X0_55,g1_pre_topc(u1_struct_0(X0_58),u1_pre_topc(X0_58)),k6_tmap_1(sK1,sK2)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0_58),u1_pre_topc(X0_58))),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5359,c_5255])).

cnf(c_3524,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_pre_topc(k6_tmap_1(sK1,X0_55)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3365])).

cnf(c_3526,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_pre_topc(k6_tmap_1(sK1,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3524])).

cnf(c_8311,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(g1_pre_topc(u1_struct_0(X0_58),u1_pre_topc(X0_58))),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_55,X0_58,k6_tmap_1(sK1,sK2)) = iProver_top
    | v5_pre_topc(X0_55,g1_pre_topc(u1_struct_0(X0_58),u1_pre_topc(X0_58)),k6_tmap_1(sK1,sK2)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0_58),u1_pre_topc(X0_58))),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5364,c_42,c_3526,c_3529])).

cnf(c_8312,plain,
    ( v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(g1_pre_topc(u1_struct_0(X0_58),u1_pre_topc(X0_58))),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_55,X0_58,k6_tmap_1(sK1,sK2)) = iProver_top
    | v5_pre_topc(X0_55,g1_pre_topc(u1_struct_0(X0_58),u1_pre_topc(X0_58)),k6_tmap_1(sK1,sK2)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0_58),u1_pre_topc(X0_58))),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_8311])).

cnf(c_8317,plain,
    ( v1_funct_2(X0_55,u1_struct_0(X0_58),k2_struct_0(sK1)) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(g1_pre_topc(u1_struct_0(X0_58),u1_pre_topc(X0_58))),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_55,X0_58,k6_tmap_1(sK1,sK2)) = iProver_top
    | v5_pre_topc(X0_55,g1_pre_topc(u1_struct_0(X0_58),u1_pre_topc(X0_58)),k6_tmap_1(sK1,sK2)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),k2_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0_58),u1_pre_topc(X0_58))),k2_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8312,c_5702])).

cnf(c_8321,plain,
    ( v1_funct_2(X0_55,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k2_struct_0(sK1)) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_55,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),k6_tmap_1(sK1,sK2)) != iProver_top
    | v5_pre_topc(X0_55,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),k2_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5702,c_8317])).

cnf(c_8326,plain,
    ( v1_funct_2(X0_55,u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),k2_struct_0(sK1)) != iProver_top
    | v1_funct_2(X0_55,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_55,g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),k6_tmap_1(sK1,sK2)) != iProver_top
    | v5_pre_topc(X0_55,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),k2_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8321,c_5702])).

cnf(c_8504,plain,
    ( v1_funct_1(X0_55) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),k2_struct_0(sK1)) != iProver_top
    | v1_funct_2(X0_55,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_55,g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),k6_tmap_1(sK1,sK2)) != iProver_top
    | v5_pre_topc(X0_55,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),k2_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8326,c_40,c_41])).

cnf(c_8505,plain,
    ( v1_funct_2(X0_55,u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),k2_struct_0(sK1)) != iProver_top
    | v1_funct_2(X0_55,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
    | v5_pre_topc(X0_55,g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),k6_tmap_1(sK1,sK2)) != iProver_top
    | v5_pre_topc(X0_55,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),k2_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_8504])).

cnf(c_89997,plain,
    ( v1_funct_2(X0_55,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),k1_xboole_0) != iProver_top
    | v1_funct_2(X0_55,k1_xboole_0,k1_xboole_0) != iProver_top
    | v5_pre_topc(X0_55,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)),k6_tmap_1(sK1,sK2)) != iProver_top
    | v5_pre_topc(X0_55,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),k1_xboole_0))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(demodulation,[status(thm)],[c_89489,c_8505])).

cnf(c_97368,plain,
    ( v1_funct_2(X0_55,u1_struct_0(k6_tmap_1(sK1,sK2)),k1_xboole_0) != iProver_top
    | v1_funct_2(X0_55,k1_xboole_0,k1_xboole_0) != iProver_top
    | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) != iProver_top
    | v5_pre_topc(X0_55,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)),k1_xboole_0))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(demodulation,[status(thm)],[c_97365,c_89997])).

cnf(c_97377,plain,
    ( v1_funct_2(X0_55,k1_xboole_0,k1_xboole_0) != iProver_top
    | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) != iProver_top
    | v5_pre_topc(X0_55,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_97368,c_90023])).

cnf(c_128151,plain,
    ( k8_relset_1(u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(k6_tmap_1(sK1,sK2)),k6_partfun1(u1_struct_0(k6_tmap_1(sK1,sK2))),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2))
    | v1_funct_2(k7_tmap_1(sK1,sK2),k1_xboole_0,k1_xboole_0) != iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k7_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_128142,c_97377])).

cnf(c_128158,plain,
    ( k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k1_xboole_0))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k1_xboole_0))
    | v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) != iProver_top
    | v5_pre_topc(k6_partfun1(k1_xboole_0),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_128151,c_90023,c_90024])).

cnf(c_128159,plain,
    ( k10_relat_1(k6_partfun1(k1_xboole_0),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k1_xboole_0))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k1_xboole_0))
    | v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) != iProver_top
    | v5_pre_topc(k6_partfun1(k1_xboole_0),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_128158,c_90035])).

cnf(c_128703,plain,
    ( k10_relat_1(k6_partfun1(k1_xboole_0),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k1_xboole_0))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k1_xboole_0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_128163,c_36,c_35,c_42,c_3445,c_3447,c_3495,c_3511,c_3513,c_3520,c_3531,c_4451,c_4505,c_4526,c_4662,c_4706,c_4800,c_4809,c_5050,c_5289,c_6247,c_7126,c_18236,c_34097,c_89212,c_90015,c_90017,c_90028,c_90034,c_97190,c_128159])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_3393,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58))
    | v5_pre_topc(X0_55,X0_58,X1_58)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_55,sK0(X0_58,X1_58,X0_55)),X0_58)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
    | ~ v1_funct_1(X0_55)
    | ~ l1_pre_topc(X0_58)
    | ~ l1_pre_topc(X1_58)
    | k2_struct_0(X0_58) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_4319,plain,
    ( k2_struct_0(X0_58) != k1_xboole_0
    | v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
    | v5_pre_topc(X0_55,X0_58,X1_58) = iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_55,sK0(X0_58,X1_58,X0_55)),X0_58) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3393])).

cnf(c_6516,plain,
    ( k2_struct_0(sK1) != k1_xboole_0
    | v1_funct_2(X0_55,u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(X0_58),X0_55,sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55)),k6_tmap_1(sK1,sK2)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(X0_58)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5705,c_4319])).

cnf(c_6521,plain,
    ( k2_struct_0(sK1) != k1_xboole_0
    | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0_58),X0_55,sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55)),k6_tmap_1(sK1,sK2)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6516,c_5778])).

cnf(c_11334,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0_58),X0_55,sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55)),k6_tmap_1(sK1,sK2)) != iProver_top
    | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
    | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
    | k2_struct_0(sK1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6521,c_42,c_3529])).

cnf(c_11335,plain,
    ( k2_struct_0(sK1) != k1_xboole_0
    | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0_58),X0_55,sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55)),k6_tmap_1(sK1,sK2)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_11334])).

cnf(c_89980,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v1_funct_2(X0_55,k1_xboole_0,u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
    | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X0_58),X0_55,sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55)),k6_tmap_1(sK1,sK2)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0_58)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(demodulation,[status(thm)],[c_89489,c_11335])).

cnf(c_90042,plain,
    ( v1_funct_2(X0_55,k1_xboole_0,u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
    | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X0_58),X0_55,sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55)),k6_tmap_1(sK1,sK2)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0_58)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_89980])).

cnf(c_119637,plain,
    ( v1_funct_2(X0_55,k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0_55,sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_55)),k6_tmap_1(sK1,sK2)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_90023,c_90042])).

cnf(c_119640,plain,
    ( v1_funct_2(X0_55,k1_xboole_0,k1_xboole_0) != iProver_top
    | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0_55,sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_55)),k6_tmap_1(sK1,sK2)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_119637,c_90023])).

cnf(c_119896,plain,
    ( v1_funct_1(X0_55) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0_55,sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_55)),k6_tmap_1(sK1,sK2)) != iProver_top
    | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(X0_55,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_119640,c_42,c_3529])).

cnf(c_119897,plain,
    ( v1_funct_2(X0_55,k1_xboole_0,k1_xboole_0) != iProver_top
    | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0_55,sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_55)),k6_tmap_1(sK1,sK2)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_119896])).

cnf(c_119902,plain,
    ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) != iProver_top
    | v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k1_xboole_0))),k6_tmap_1(sK1,sK2)) != iProver_top
    | m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_90035,c_119897])).

cnf(c_90000,plain,
    ( v1_funct_2(X0_55,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_2(X0_55,k1_xboole_0,u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(X0_55,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)),X0_58) != iProver_top
    | v5_pre_topc(X0_55,sK1,X0_58) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),u1_struct_0(X0_58)))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0_58)))) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(demodulation,[status(thm)],[c_89489,c_8136])).

cnf(c_97366,plain,
    ( v1_funct_2(X0_55,u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_2(X0_55,k1_xboole_0,u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) != iProver_top
    | v5_pre_topc(X0_55,sK1,X0_58) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(X0_58)))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0_58)))) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(demodulation,[status(thm)],[c_97365,c_90000])).

cnf(c_97379,plain,
    ( v1_funct_2(X0_55,k1_xboole_0,u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) != iProver_top
    | v5_pre_topc(X0_55,sK1,X0_58) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0_58)))) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_97366,c_90023])).

cnf(c_98045,plain,
    ( v1_funct_2(k7_tmap_1(sK1,X0_55),k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,X0_55))) != iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,X0_55),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_55)) != iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,X0_55),sK1,k6_tmap_1(sK1,X0_55)) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v2_pre_topc(k6_tmap_1(sK1,X0_55)) != iProver_top
    | v1_funct_1(k7_tmap_1(sK1,X0_55)) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,X0_55)) != iProver_top ),
    inference(superposition,[status(thm)],[c_90032,c_97379])).

cnf(c_90013,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v2_pre_topc(k6_tmap_1(sK1,X0_55)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_89489,c_5781])).

cnf(c_98470,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,X0_55),sK1,k6_tmap_1(sK1,X0_55)) = iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,X0_55),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_55)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_98045,c_90012,c_90013,c_90014,c_90033])).

cnf(c_98471,plain,
    ( v5_pre_topc(k7_tmap_1(sK1,X0_55),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_55)) != iProver_top
    | v5_pre_topc(k7_tmap_1(sK1,X0_55),sK1,k6_tmap_1(sK1,X0_55)) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_98470])).

cnf(c_98478,plain,
    ( v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_90024,c_98471])).

cnf(c_98479,plain,
    ( v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) != iProver_top
    | v5_pre_topc(k6_partfun1(k1_xboole_0),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_98478,c_90024])).

cnf(c_119905,plain,
    ( v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k1_xboole_0))),k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_119902,c_36,c_35,c_42,c_3445,c_3447,c_3495,c_3511,c_3513,c_3520,c_3531,c_4451,c_4505,c_4526,c_4662,c_4706,c_4800,c_4809,c_5050,c_5289,c_6247,c_7126,c_18236,c_34097,c_89212,c_90015,c_90017,c_90028,c_90034,c_97190,c_98479])).

cnf(c_128705,plain,
    ( v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k1_xboole_0)),k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_128703,c_119905])).

cnf(c_134575,plain,
    ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
    | v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
    | v1_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_90040,c_128705])).

cnf(c_134576,plain,
    ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) != iProver_top
    | v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
    | m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_134575,c_90023])).

cnf(c_87665,plain,
    ( X0_57 != k2_struct_0(sK1)
    | k6_partfun1(X0_57) = k6_partfun1(k2_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_3412])).

cnf(c_87667,plain,
    ( k1_xboole_0 != k2_struct_0(sK1)
    | k6_partfun1(k1_xboole_0) = k6_partfun1(k2_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_87665])).

cnf(c_60951,plain,
    ( X0_55 != X1_55
    | X0_55 = k7_tmap_1(sK1,sK2)
    | k7_tmap_1(sK1,sK2) != X1_55 ),
    inference(instantiation,[status(thm)],[c_3404])).

cnf(c_66552,plain,
    ( X0_55 = k7_tmap_1(sK1,sK2)
    | X0_55 != k6_partfun1(k2_struct_0(sK1))
    | k7_tmap_1(sK1,sK2) != k6_partfun1(k2_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_60951])).

cnf(c_78478,plain,
    ( k7_tmap_1(sK1,sK2) != k6_partfun1(k2_struct_0(sK1))
    | k6_partfun1(X0_57) = k7_tmap_1(sK1,sK2)
    | k6_partfun1(X0_57) != k6_partfun1(k2_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_66552])).

cnf(c_78479,plain,
    ( k7_tmap_1(sK1,sK2) != k6_partfun1(k2_struct_0(sK1))
    | k6_partfun1(k1_xboole_0) = k7_tmap_1(sK1,sK2)
    | k6_partfun1(k1_xboole_0) != k6_partfun1(k2_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_78478])).

cnf(c_64333,plain,
    ( u1_struct_0(k6_tmap_1(sK1,X0_55)) != X0_57
    | k1_xboole_0 != X0_57
    | k1_xboole_0 = u1_struct_0(k6_tmap_1(sK1,X0_55)) ),
    inference(instantiation,[status(thm)],[c_3405])).

cnf(c_66094,plain,
    ( u1_struct_0(k6_tmap_1(sK1,sK2)) != k2_struct_0(sK1)
    | k1_xboole_0 = u1_struct_0(k6_tmap_1(sK1,sK2))
    | k1_xboole_0 != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_64333])).

cnf(c_4677,plain,
    ( v1_funct_1(X0_55)
    | ~ v1_funct_1(k7_tmap_1(sK1,sK2))
    | X0_55 != k7_tmap_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_3419])).

cnf(c_14850,plain,
    ( ~ v1_funct_1(k7_tmap_1(sK1,sK2))
    | v1_funct_1(k6_partfun1(X0_57))
    | k6_partfun1(X0_57) != k7_tmap_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_4677])).

cnf(c_14861,plain,
    ( k6_partfun1(X0_57) != k7_tmap_1(sK1,sK2)
    | v1_funct_1(k7_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(k6_partfun1(X0_57)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14850])).

cnf(c_14863,plain,
    ( k6_partfun1(k1_xboole_0) != k7_tmap_1(sK1,sK2)
    | v1_funct_1(k7_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_14861])).

cnf(c_5432,plain,
    ( X0_57 != u1_struct_0(k6_tmap_1(sK1,X0_55))
    | k1_zfmisc_1(X0_57) = k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0_55))) ),
    inference(instantiation,[status(thm)],[c_3410])).

cnf(c_5433,plain,
    ( k1_xboole_0 != u1_struct_0(k6_tmap_1(sK1,sK2))
    | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_5432])).

cnf(c_4629,plain,
    ( m1_subset_1(X0_55,X0_56)
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X1_55))))
    | X0_56 != k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X1_55)))
    | X0_55 != X1_55 ),
    inference(instantiation,[status(thm)],[c_3411])).

cnf(c_4777,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(X0_57))
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X1_55))))
    | k1_zfmisc_1(X0_57) != k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X1_55)))
    | X0_55 != X1_55 ),
    inference(instantiation,[status(thm)],[c_4629])).

cnf(c_4778,plain,
    ( k1_zfmisc_1(X0_57) != k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0_55)))
    | X1_55 != X0_55
    | m1_subset_1(X1_55,k1_zfmisc_1(X0_57)) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0_55)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4777])).

cnf(c_4780,plain,
    ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))
    | sK2 != sK2
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4778])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_134576,c_98479,c_97361,c_90034,c_90017,c_90015,c_89489,c_87667,c_78479,c_66094,c_14863,c_5778,c_5776,c_5433,c_5050,c_4780,c_4505,c_4451,c_3529,c_3520,c_3513,c_3447,c_3445,c_42,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:04:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 47.37/6.54  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 47.37/6.54  
% 47.37/6.54  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 47.37/6.54  
% 47.37/6.54  ------  iProver source info
% 47.37/6.54  
% 47.37/6.54  git: date: 2020-06-30 10:37:57 +0100
% 47.37/6.54  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 47.37/6.54  git: non_committed_changes: false
% 47.37/6.54  git: last_make_outside_of_git: false
% 47.37/6.54  
% 47.37/6.54  ------ 
% 47.37/6.54  
% 47.37/6.54  ------ Input Options
% 47.37/6.54  
% 47.37/6.54  --out_options                           all
% 47.37/6.54  --tptp_safe_out                         true
% 47.37/6.54  --problem_path                          ""
% 47.37/6.54  --include_path                          ""
% 47.37/6.54  --clausifier                            res/vclausify_rel
% 47.37/6.54  --clausifier_options                    ""
% 47.37/6.54  --stdin                                 false
% 47.37/6.54  --stats_out                             all
% 47.37/6.54  
% 47.37/6.54  ------ General Options
% 47.37/6.54  
% 47.37/6.54  --fof                                   false
% 47.37/6.54  --time_out_real                         305.
% 47.37/6.54  --time_out_virtual                      -1.
% 47.37/6.54  --symbol_type_check                     false
% 47.37/6.54  --clausify_out                          false
% 47.37/6.54  --sig_cnt_out                           false
% 47.37/6.54  --trig_cnt_out                          false
% 47.37/6.54  --trig_cnt_out_tolerance                1.
% 47.37/6.54  --trig_cnt_out_sk_spl                   false
% 47.37/6.54  --abstr_cl_out                          false
% 47.37/6.54  
% 47.37/6.54  ------ Global Options
% 47.37/6.54  
% 47.37/6.54  --schedule                              default
% 47.37/6.54  --add_important_lit                     false
% 47.37/6.54  --prop_solver_per_cl                    1000
% 47.37/6.54  --min_unsat_core                        false
% 47.37/6.54  --soft_assumptions                      false
% 47.37/6.54  --soft_lemma_size                       3
% 47.37/6.54  --prop_impl_unit_size                   0
% 47.37/6.54  --prop_impl_unit                        []
% 47.37/6.54  --share_sel_clauses                     true
% 47.37/6.54  --reset_solvers                         false
% 47.37/6.54  --bc_imp_inh                            [conj_cone]
% 47.37/6.54  --conj_cone_tolerance                   3.
% 47.37/6.54  --extra_neg_conj                        none
% 47.37/6.54  --large_theory_mode                     true
% 47.37/6.54  --prolific_symb_bound                   200
% 47.37/6.54  --lt_threshold                          2000
% 47.37/6.54  --clause_weak_htbl                      true
% 47.37/6.54  --gc_record_bc_elim                     false
% 47.37/6.54  
% 47.37/6.54  ------ Preprocessing Options
% 47.37/6.54  
% 47.37/6.54  --preprocessing_flag                    true
% 47.37/6.54  --time_out_prep_mult                    0.1
% 47.37/6.54  --splitting_mode                        input
% 47.37/6.54  --splitting_grd                         true
% 47.37/6.54  --splitting_cvd                         false
% 47.37/6.54  --splitting_cvd_svl                     false
% 47.37/6.54  --splitting_nvd                         32
% 47.37/6.54  --sub_typing                            true
% 47.37/6.54  --prep_gs_sim                           true
% 47.37/6.54  --prep_unflatten                        true
% 47.37/6.54  --prep_res_sim                          true
% 47.37/6.54  --prep_upred                            true
% 47.37/6.54  --prep_sem_filter                       exhaustive
% 47.37/6.54  --prep_sem_filter_out                   false
% 47.37/6.54  --pred_elim                             true
% 47.37/6.54  --res_sim_input                         true
% 47.37/6.54  --eq_ax_congr_red                       true
% 47.37/6.54  --pure_diseq_elim                       true
% 47.37/6.54  --brand_transform                       false
% 47.37/6.54  --non_eq_to_eq                          false
% 47.37/6.54  --prep_def_merge                        true
% 47.37/6.54  --prep_def_merge_prop_impl              false
% 47.37/6.54  --prep_def_merge_mbd                    true
% 47.37/6.54  --prep_def_merge_tr_red                 false
% 47.37/6.54  --prep_def_merge_tr_cl                  false
% 47.37/6.54  --smt_preprocessing                     true
% 47.37/6.54  --smt_ac_axioms                         fast
% 47.37/6.54  --preprocessed_out                      false
% 47.37/6.54  --preprocessed_stats                    false
% 47.37/6.54  
% 47.37/6.54  ------ Abstraction refinement Options
% 47.37/6.54  
% 47.37/6.54  --abstr_ref                             []
% 47.37/6.54  --abstr_ref_prep                        false
% 47.37/6.54  --abstr_ref_until_sat                   false
% 47.37/6.54  --abstr_ref_sig_restrict                funpre
% 47.37/6.54  --abstr_ref_af_restrict_to_split_sk     false
% 47.37/6.54  --abstr_ref_under                       []
% 47.37/6.54  
% 47.37/6.54  ------ SAT Options
% 47.37/6.54  
% 47.37/6.54  --sat_mode                              false
% 47.37/6.54  --sat_fm_restart_options                ""
% 47.37/6.54  --sat_gr_def                            false
% 47.37/6.54  --sat_epr_types                         true
% 47.37/6.54  --sat_non_cyclic_types                  false
% 47.37/6.54  --sat_finite_models                     false
% 47.37/6.54  --sat_fm_lemmas                         false
% 47.37/6.54  --sat_fm_prep                           false
% 47.37/6.54  --sat_fm_uc_incr                        true
% 47.37/6.54  --sat_out_model                         small
% 47.37/6.54  --sat_out_clauses                       false
% 47.37/6.54  
% 47.37/6.54  ------ QBF Options
% 47.37/6.54  
% 47.37/6.54  --qbf_mode                              false
% 47.37/6.54  --qbf_elim_univ                         false
% 47.37/6.54  --qbf_dom_inst                          none
% 47.37/6.54  --qbf_dom_pre_inst                      false
% 47.37/6.54  --qbf_sk_in                             false
% 47.37/6.54  --qbf_pred_elim                         true
% 47.37/6.54  --qbf_split                             512
% 47.37/6.54  
% 47.37/6.54  ------ BMC1 Options
% 47.37/6.54  
% 47.37/6.54  --bmc1_incremental                      false
% 47.37/6.54  --bmc1_axioms                           reachable_all
% 47.37/6.54  --bmc1_min_bound                        0
% 47.37/6.54  --bmc1_max_bound                        -1
% 47.37/6.54  --bmc1_max_bound_default                -1
% 47.37/6.54  --bmc1_symbol_reachability              true
% 47.37/6.54  --bmc1_property_lemmas                  false
% 47.37/6.54  --bmc1_k_induction                      false
% 47.37/6.54  --bmc1_non_equiv_states                 false
% 47.37/6.54  --bmc1_deadlock                         false
% 47.37/6.54  --bmc1_ucm                              false
% 47.37/6.54  --bmc1_add_unsat_core                   none
% 47.37/6.54  --bmc1_unsat_core_children              false
% 47.37/6.54  --bmc1_unsat_core_extrapolate_axioms    false
% 47.37/6.54  --bmc1_out_stat                         full
% 47.37/6.54  --bmc1_ground_init                      false
% 47.37/6.54  --bmc1_pre_inst_next_state              false
% 47.37/6.54  --bmc1_pre_inst_state                   false
% 47.37/6.54  --bmc1_pre_inst_reach_state             false
% 47.37/6.54  --bmc1_out_unsat_core                   false
% 47.37/6.54  --bmc1_aig_witness_out                  false
% 47.37/6.54  --bmc1_verbose                          false
% 47.37/6.54  --bmc1_dump_clauses_tptp                false
% 47.37/6.54  --bmc1_dump_unsat_core_tptp             false
% 47.37/6.54  --bmc1_dump_file                        -
% 47.37/6.54  --bmc1_ucm_expand_uc_limit              128
% 47.37/6.54  --bmc1_ucm_n_expand_iterations          6
% 47.37/6.54  --bmc1_ucm_extend_mode                  1
% 47.37/6.54  --bmc1_ucm_init_mode                    2
% 47.37/6.54  --bmc1_ucm_cone_mode                    none
% 47.37/6.54  --bmc1_ucm_reduced_relation_type        0
% 47.37/6.54  --bmc1_ucm_relax_model                  4
% 47.37/6.54  --bmc1_ucm_full_tr_after_sat            true
% 47.37/6.54  --bmc1_ucm_expand_neg_assumptions       false
% 47.37/6.54  --bmc1_ucm_layered_model                none
% 47.37/6.54  --bmc1_ucm_max_lemma_size               10
% 47.37/6.54  
% 47.37/6.54  ------ AIG Options
% 47.37/6.54  
% 47.37/6.54  --aig_mode                              false
% 47.37/6.54  
% 47.37/6.54  ------ Instantiation Options
% 47.37/6.54  
% 47.37/6.54  --instantiation_flag                    true
% 47.37/6.54  --inst_sos_flag                         true
% 47.37/6.54  --inst_sos_phase                        true
% 47.37/6.54  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 47.37/6.54  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 47.37/6.54  --inst_lit_sel_side                     num_symb
% 47.37/6.54  --inst_solver_per_active                1400
% 47.37/6.54  --inst_solver_calls_frac                1.
% 47.37/6.54  --inst_passive_queue_type               priority_queues
% 47.37/6.54  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 47.37/6.54  --inst_passive_queues_freq              [25;2]
% 47.37/6.54  --inst_dismatching                      true
% 47.37/6.54  --inst_eager_unprocessed_to_passive     true
% 47.37/6.54  --inst_prop_sim_given                   true
% 47.37/6.54  --inst_prop_sim_new                     false
% 47.37/6.54  --inst_subs_new                         false
% 47.37/6.54  --inst_eq_res_simp                      false
% 47.37/6.54  --inst_subs_given                       false
% 47.37/6.54  --inst_orphan_elimination               true
% 47.37/6.54  --inst_learning_loop_flag               true
% 47.37/6.54  --inst_learning_start                   3000
% 47.37/6.54  --inst_learning_factor                  2
% 47.37/6.54  --inst_start_prop_sim_after_learn       3
% 47.37/6.54  --inst_sel_renew                        solver
% 47.37/6.54  --inst_lit_activity_flag                true
% 47.37/6.54  --inst_restr_to_given                   false
% 47.37/6.54  --inst_activity_threshold               500
% 47.37/6.54  --inst_out_proof                        true
% 47.37/6.54  
% 47.37/6.54  ------ Resolution Options
% 47.37/6.54  
% 47.37/6.54  --resolution_flag                       true
% 47.37/6.54  --res_lit_sel                           adaptive
% 47.37/6.54  --res_lit_sel_side                      none
% 47.37/6.54  --res_ordering                          kbo
% 47.37/6.54  --res_to_prop_solver                    active
% 47.37/6.54  --res_prop_simpl_new                    false
% 47.37/6.54  --res_prop_simpl_given                  true
% 47.37/6.54  --res_passive_queue_type                priority_queues
% 47.37/6.54  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 47.37/6.54  --res_passive_queues_freq               [15;5]
% 47.37/6.54  --res_forward_subs                      full
% 47.37/6.54  --res_backward_subs                     full
% 47.37/6.54  --res_forward_subs_resolution           true
% 47.37/6.54  --res_backward_subs_resolution          true
% 47.37/6.54  --res_orphan_elimination                true
% 47.37/6.54  --res_time_limit                        2.
% 47.37/6.54  --res_out_proof                         true
% 47.37/6.54  
% 47.37/6.54  ------ Superposition Options
% 47.37/6.54  
% 47.37/6.54  --superposition_flag                    true
% 47.37/6.54  --sup_passive_queue_type                priority_queues
% 47.37/6.54  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 47.37/6.54  --sup_passive_queues_freq               [8;1;4]
% 47.37/6.54  --demod_completeness_check              fast
% 47.37/6.54  --demod_use_ground                      true
% 47.37/6.54  --sup_to_prop_solver                    passive
% 47.37/6.54  --sup_prop_simpl_new                    true
% 47.37/6.54  --sup_prop_simpl_given                  true
% 47.37/6.54  --sup_fun_splitting                     true
% 47.37/6.54  --sup_smt_interval                      50000
% 47.37/6.54  
% 47.37/6.54  ------ Superposition Simplification Setup
% 47.37/6.54  
% 47.37/6.54  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 47.37/6.54  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 47.37/6.54  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 47.37/6.54  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 47.37/6.54  --sup_full_triv                         [TrivRules;PropSubs]
% 47.37/6.54  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 47.37/6.54  --sup_full_bw                           [BwDemod;BwSubsumption]
% 47.37/6.54  --sup_immed_triv                        [TrivRules]
% 47.37/6.54  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 47.37/6.54  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 47.37/6.54  --sup_immed_bw_main                     []
% 47.37/6.54  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 47.37/6.54  --sup_input_triv                        [Unflattening;TrivRules]
% 47.37/6.54  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 47.37/6.54  --sup_input_bw                          []
% 47.37/6.54  
% 47.37/6.54  ------ Combination Options
% 47.37/6.54  
% 47.37/6.54  --comb_res_mult                         3
% 47.37/6.54  --comb_sup_mult                         2
% 47.37/6.54  --comb_inst_mult                        10
% 47.37/6.54  
% 47.37/6.54  ------ Debug Options
% 47.37/6.54  
% 47.37/6.54  --dbg_backtrace                         false
% 47.37/6.54  --dbg_dump_prop_clauses                 false
% 47.37/6.54  --dbg_dump_prop_clauses_file            -
% 47.37/6.54  --dbg_out_stat                          false
% 47.37/6.54  ------ Parsing...
% 47.37/6.54  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 47.37/6.54  
% 47.37/6.54  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 47.37/6.54  
% 47.37/6.54  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 47.37/6.54  
% 47.37/6.54  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 47.37/6.54  ------ Proving...
% 47.37/6.54  ------ Problem Properties 
% 47.37/6.54  
% 47.37/6.54  
% 47.37/6.54  clauses                                 35
% 47.37/6.54  conjectures                             8
% 47.37/6.54  EPR                                     2
% 47.37/6.54  Horn                                    25
% 47.37/6.54  unary                                   6
% 47.37/6.54  binary                                  15
% 47.37/6.54  lits                                    140
% 47.37/6.54  lits eq                                 16
% 47.37/6.54  fd_pure                                 0
% 47.37/6.54  fd_pseudo                               0
% 47.37/6.54  fd_cond                                 0
% 47.37/6.54  fd_pseudo_cond                          0
% 47.37/6.54  AC symbols                              0
% 47.37/6.54  
% 47.37/6.54  ------ Schedule dynamic 5 is on 
% 47.37/6.54  
% 47.37/6.54  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 47.37/6.54  
% 47.37/6.54  
% 47.37/6.54  ------ 
% 47.37/6.54  Current options:
% 47.37/6.54  ------ 
% 47.37/6.54  
% 47.37/6.54  ------ Input Options
% 47.37/6.54  
% 47.37/6.54  --out_options                           all
% 47.37/6.54  --tptp_safe_out                         true
% 47.37/6.54  --problem_path                          ""
% 47.37/6.54  --include_path                          ""
% 47.37/6.54  --clausifier                            res/vclausify_rel
% 47.37/6.54  --clausifier_options                    ""
% 47.37/6.54  --stdin                                 false
% 47.37/6.54  --stats_out                             all
% 47.37/6.54  
% 47.37/6.54  ------ General Options
% 47.37/6.54  
% 47.37/6.54  --fof                                   false
% 47.37/6.54  --time_out_real                         305.
% 47.37/6.54  --time_out_virtual                      -1.
% 47.37/6.54  --symbol_type_check                     false
% 47.37/6.54  --clausify_out                          false
% 47.37/6.54  --sig_cnt_out                           false
% 47.37/6.54  --trig_cnt_out                          false
% 47.37/6.54  --trig_cnt_out_tolerance                1.
% 47.37/6.54  --trig_cnt_out_sk_spl                   false
% 47.37/6.54  --abstr_cl_out                          false
% 47.37/6.54  
% 47.37/6.54  ------ Global Options
% 47.37/6.54  
% 47.37/6.54  --schedule                              default
% 47.37/6.54  --add_important_lit                     false
% 47.37/6.54  --prop_solver_per_cl                    1000
% 47.37/6.54  --min_unsat_core                        false
% 47.37/6.54  --soft_assumptions                      false
% 47.37/6.54  --soft_lemma_size                       3
% 47.37/6.54  --prop_impl_unit_size                   0
% 47.37/6.54  --prop_impl_unit                        []
% 47.37/6.54  --share_sel_clauses                     true
% 47.37/6.54  --reset_solvers                         false
% 47.37/6.54  --bc_imp_inh                            [conj_cone]
% 47.37/6.54  --conj_cone_tolerance                   3.
% 47.37/6.54  --extra_neg_conj                        none
% 47.37/6.54  --large_theory_mode                     true
% 47.37/6.54  --prolific_symb_bound                   200
% 47.37/6.54  --lt_threshold                          2000
% 47.37/6.54  --clause_weak_htbl                      true
% 47.37/6.54  --gc_record_bc_elim                     false
% 47.37/6.54  
% 47.37/6.54  ------ Preprocessing Options
% 47.37/6.54  
% 47.37/6.54  --preprocessing_flag                    true
% 47.37/6.54  --time_out_prep_mult                    0.1
% 47.37/6.54  --splitting_mode                        input
% 47.37/6.54  --splitting_grd                         true
% 47.37/6.54  --splitting_cvd                         false
% 47.37/6.54  --splitting_cvd_svl                     false
% 47.37/6.54  --splitting_nvd                         32
% 47.37/6.54  --sub_typing                            true
% 47.37/6.54  --prep_gs_sim                           true
% 47.37/6.54  --prep_unflatten                        true
% 47.37/6.54  --prep_res_sim                          true
% 47.37/6.54  --prep_upred                            true
% 47.37/6.54  --prep_sem_filter                       exhaustive
% 47.37/6.54  --prep_sem_filter_out                   false
% 47.37/6.54  --pred_elim                             true
% 47.37/6.54  --res_sim_input                         true
% 47.37/6.54  --eq_ax_congr_red                       true
% 47.37/6.54  --pure_diseq_elim                       true
% 47.37/6.54  --brand_transform                       false
% 47.37/6.54  --non_eq_to_eq                          false
% 47.37/6.54  --prep_def_merge                        true
% 47.37/6.54  --prep_def_merge_prop_impl              false
% 47.37/6.54  --prep_def_merge_mbd                    true
% 47.37/6.54  --prep_def_merge_tr_red                 false
% 47.37/6.54  --prep_def_merge_tr_cl                  false
% 47.37/6.54  --smt_preprocessing                     true
% 47.37/6.54  --smt_ac_axioms                         fast
% 47.37/6.54  --preprocessed_out                      false
% 47.37/6.54  --preprocessed_stats                    false
% 47.37/6.54  
% 47.37/6.54  ------ Abstraction refinement Options
% 47.37/6.54  
% 47.37/6.54  --abstr_ref                             []
% 47.37/6.54  --abstr_ref_prep                        false
% 47.37/6.54  --abstr_ref_until_sat                   false
% 47.37/6.54  --abstr_ref_sig_restrict                funpre
% 47.37/6.54  --abstr_ref_af_restrict_to_split_sk     false
% 47.37/6.54  --abstr_ref_under                       []
% 47.37/6.54  
% 47.37/6.54  ------ SAT Options
% 47.37/6.54  
% 47.37/6.54  --sat_mode                              false
% 47.37/6.54  --sat_fm_restart_options                ""
% 47.37/6.54  --sat_gr_def                            false
% 47.37/6.54  --sat_epr_types                         true
% 47.37/6.54  --sat_non_cyclic_types                  false
% 47.37/6.54  --sat_finite_models                     false
% 47.37/6.54  --sat_fm_lemmas                         false
% 47.37/6.54  --sat_fm_prep                           false
% 47.37/6.54  --sat_fm_uc_incr                        true
% 47.37/6.54  --sat_out_model                         small
% 47.37/6.54  --sat_out_clauses                       false
% 47.37/6.54  
% 47.37/6.54  ------ QBF Options
% 47.37/6.54  
% 47.37/6.54  --qbf_mode                              false
% 47.37/6.54  --qbf_elim_univ                         false
% 47.37/6.54  --qbf_dom_inst                          none
% 47.37/6.54  --qbf_dom_pre_inst                      false
% 47.37/6.54  --qbf_sk_in                             false
% 47.37/6.54  --qbf_pred_elim                         true
% 47.37/6.54  --qbf_split                             512
% 47.37/6.54  
% 47.37/6.54  ------ BMC1 Options
% 47.37/6.54  
% 47.37/6.54  --bmc1_incremental                      false
% 47.37/6.54  --bmc1_axioms                           reachable_all
% 47.37/6.54  --bmc1_min_bound                        0
% 47.37/6.54  --bmc1_max_bound                        -1
% 47.37/6.54  --bmc1_max_bound_default                -1
% 47.37/6.54  --bmc1_symbol_reachability              true
% 47.37/6.54  --bmc1_property_lemmas                  false
% 47.37/6.54  --bmc1_k_induction                      false
% 47.37/6.54  --bmc1_non_equiv_states                 false
% 47.37/6.54  --bmc1_deadlock                         false
% 47.37/6.54  --bmc1_ucm                              false
% 47.37/6.54  --bmc1_add_unsat_core                   none
% 47.37/6.54  --bmc1_unsat_core_children              false
% 47.37/6.54  --bmc1_unsat_core_extrapolate_axioms    false
% 47.37/6.54  --bmc1_out_stat                         full
% 47.37/6.54  --bmc1_ground_init                      false
% 47.37/6.54  --bmc1_pre_inst_next_state              false
% 47.37/6.54  --bmc1_pre_inst_state                   false
% 47.37/6.54  --bmc1_pre_inst_reach_state             false
% 47.37/6.54  --bmc1_out_unsat_core                   false
% 47.37/6.54  --bmc1_aig_witness_out                  false
% 47.37/6.54  --bmc1_verbose                          false
% 47.37/6.54  --bmc1_dump_clauses_tptp                false
% 47.37/6.54  --bmc1_dump_unsat_core_tptp             false
% 47.37/6.54  --bmc1_dump_file                        -
% 47.37/6.54  --bmc1_ucm_expand_uc_limit              128
% 47.37/6.54  --bmc1_ucm_n_expand_iterations          6
% 47.37/6.54  --bmc1_ucm_extend_mode                  1
% 47.37/6.54  --bmc1_ucm_init_mode                    2
% 47.37/6.54  --bmc1_ucm_cone_mode                    none
% 47.37/6.54  --bmc1_ucm_reduced_relation_type        0
% 47.37/6.54  --bmc1_ucm_relax_model                  4
% 47.37/6.54  --bmc1_ucm_full_tr_after_sat            true
% 47.37/6.54  --bmc1_ucm_expand_neg_assumptions       false
% 47.37/6.54  --bmc1_ucm_layered_model                none
% 47.37/6.54  --bmc1_ucm_max_lemma_size               10
% 47.37/6.54  
% 47.37/6.54  ------ AIG Options
% 47.37/6.54  
% 47.37/6.54  --aig_mode                              false
% 47.37/6.54  
% 47.37/6.54  ------ Instantiation Options
% 47.37/6.54  
% 47.37/6.54  --instantiation_flag                    true
% 47.37/6.54  --inst_sos_flag                         true
% 47.37/6.54  --inst_sos_phase                        true
% 47.37/6.54  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 47.37/6.54  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 47.37/6.54  --inst_lit_sel_side                     none
% 47.37/6.54  --inst_solver_per_active                1400
% 47.37/6.54  --inst_solver_calls_frac                1.
% 47.37/6.54  --inst_passive_queue_type               priority_queues
% 47.37/6.54  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 47.37/6.54  --inst_passive_queues_freq              [25;2]
% 47.37/6.54  --inst_dismatching                      true
% 47.37/6.54  --inst_eager_unprocessed_to_passive     true
% 47.37/6.54  --inst_prop_sim_given                   true
% 47.37/6.54  --inst_prop_sim_new                     false
% 47.37/6.54  --inst_subs_new                         false
% 47.37/6.54  --inst_eq_res_simp                      false
% 47.37/6.54  --inst_subs_given                       false
% 47.37/6.54  --inst_orphan_elimination               true
% 47.37/6.54  --inst_learning_loop_flag               true
% 47.37/6.54  --inst_learning_start                   3000
% 47.37/6.54  --inst_learning_factor                  2
% 47.37/6.54  --inst_start_prop_sim_after_learn       3
% 47.37/6.54  --inst_sel_renew                        solver
% 47.37/6.54  --inst_lit_activity_flag                true
% 47.37/6.54  --inst_restr_to_given                   false
% 47.37/6.54  --inst_activity_threshold               500
% 47.37/6.54  --inst_out_proof                        true
% 47.37/6.54  
% 47.37/6.54  ------ Resolution Options
% 47.37/6.54  
% 47.37/6.54  --resolution_flag                       false
% 47.37/6.54  --res_lit_sel                           adaptive
% 47.37/6.54  --res_lit_sel_side                      none
% 47.37/6.54  --res_ordering                          kbo
% 47.37/6.54  --res_to_prop_solver                    active
% 47.37/6.54  --res_prop_simpl_new                    false
% 47.37/6.54  --res_prop_simpl_given                  true
% 47.37/6.54  --res_passive_queue_type                priority_queues
% 47.37/6.54  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 47.37/6.54  --res_passive_queues_freq               [15;5]
% 47.37/6.54  --res_forward_subs                      full
% 47.37/6.54  --res_backward_subs                     full
% 47.37/6.54  --res_forward_subs_resolution           true
% 47.37/6.54  --res_backward_subs_resolution          true
% 47.37/6.54  --res_orphan_elimination                true
% 47.37/6.54  --res_time_limit                        2.
% 47.37/6.54  --res_out_proof                         true
% 47.37/6.54  
% 47.37/6.54  ------ Superposition Options
% 47.37/6.54  
% 47.37/6.54  --superposition_flag                    true
% 47.37/6.54  --sup_passive_queue_type                priority_queues
% 47.37/6.54  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 47.37/6.54  --sup_passive_queues_freq               [8;1;4]
% 47.37/6.54  --demod_completeness_check              fast
% 47.37/6.54  --demod_use_ground                      true
% 47.37/6.54  --sup_to_prop_solver                    passive
% 47.37/6.54  --sup_prop_simpl_new                    true
% 47.37/6.54  --sup_prop_simpl_given                  true
% 47.37/6.54  --sup_fun_splitting                     true
% 47.37/6.54  --sup_smt_interval                      50000
% 47.37/6.54  
% 47.37/6.54  ------ Superposition Simplification Setup
% 47.37/6.54  
% 47.37/6.54  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 47.37/6.54  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 47.37/6.54  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 47.37/6.54  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 47.37/6.54  --sup_full_triv                         [TrivRules;PropSubs]
% 47.37/6.54  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 47.37/6.54  --sup_full_bw                           [BwDemod;BwSubsumption]
% 47.37/6.54  --sup_immed_triv                        [TrivRules]
% 47.37/6.54  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 47.37/6.54  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 47.37/6.54  --sup_immed_bw_main                     []
% 47.37/6.54  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 47.37/6.54  --sup_input_triv                        [Unflattening;TrivRules]
% 47.37/6.54  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 47.37/6.54  --sup_input_bw                          []
% 47.37/6.54  
% 47.37/6.54  ------ Combination Options
% 47.37/6.54  
% 47.37/6.54  --comb_res_mult                         3
% 47.37/6.54  --comb_sup_mult                         2
% 47.37/6.54  --comb_inst_mult                        10
% 47.37/6.54  
% 47.37/6.54  ------ Debug Options
% 47.37/6.54  
% 47.37/6.54  --dbg_backtrace                         false
% 47.37/6.54  --dbg_dump_prop_clauses                 false
% 47.37/6.54  --dbg_dump_prop_clauses_file            -
% 47.37/6.54  --dbg_out_stat                          false
% 47.37/6.54  
% 47.37/6.54  
% 47.37/6.54  
% 47.37/6.54  
% 47.37/6.54  ------ Proving...
% 47.37/6.54  
% 47.37/6.54  
% 47.37/6.54  % SZS status Theorem for theBenchmark.p
% 47.37/6.54  
% 47.37/6.54  % SZS output start CNFRefutation for theBenchmark.p
% 47.37/6.54  
% 47.37/6.54  fof(f16,conjecture,(
% 47.37/6.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))))),
% 47.37/6.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.37/6.54  
% 47.37/6.54  fof(f17,negated_conjecture,(
% 47.37/6.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))))),
% 47.37/6.54    inference(negated_conjecture,[],[f16])).
% 47.37/6.54  
% 47.37/6.54  fof(f45,plain,(
% 47.37/6.54    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 47.37/6.54    inference(ennf_transformation,[],[f17])).
% 47.37/6.54  
% 47.37/6.54  fof(f46,plain,(
% 47.37/6.54    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 47.37/6.54    inference(flattening,[],[f45])).
% 47.37/6.54  
% 47.37/6.54  fof(f53,plain,(
% 47.37/6.54    ? [X0] : (? [X1] : ((((~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1))) | ~v3_pre_topc(X1,X0)) & ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 47.37/6.54    inference(nnf_transformation,[],[f46])).
% 47.37/6.54  
% 47.37/6.54  fof(f54,plain,(
% 47.37/6.54    ? [X0] : (? [X1] : ((~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1)) | ~v3_pre_topc(X1,X0)) & ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 47.37/6.54    inference(flattening,[],[f53])).
% 47.37/6.54  
% 47.37/6.54  fof(f56,plain,(
% 47.37/6.54    ( ! [X0] : (? [X1] : ((~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1)) | ~v3_pre_topc(X1,X0)) & ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((~m1_subset_1(k7_tmap_1(X0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2))))) | ~v5_pre_topc(k7_tmap_1(X0,sK2),X0,k6_tmap_1(X0,sK2)) | ~v1_funct_2(k7_tmap_1(X0,sK2),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2))) | ~v1_funct_1(k7_tmap_1(X0,sK2)) | ~v3_pre_topc(sK2,X0)) & ((m1_subset_1(k7_tmap_1(X0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2))))) & v5_pre_topc(k7_tmap_1(X0,sK2),X0,k6_tmap_1(X0,sK2)) & v1_funct_2(k7_tmap_1(X0,sK2),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2))) & v1_funct_1(k7_tmap_1(X0,sK2))) | v3_pre_topc(sK2,X0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 47.37/6.54    introduced(choice_axiom,[])).
% 47.37/6.54  
% 47.37/6.54  fof(f55,plain,(
% 47.37/6.54    ? [X0] : (? [X1] : ((~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1)) | ~v3_pre_topc(X1,X0)) & ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~m1_subset_1(k7_tmap_1(sK1,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X1))))) | ~v5_pre_topc(k7_tmap_1(sK1,X1),sK1,k6_tmap_1(sK1,X1)) | ~v1_funct_2(k7_tmap_1(sK1,X1),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X1))) | ~v1_funct_1(k7_tmap_1(sK1,X1)) | ~v3_pre_topc(X1,sK1)) & ((m1_subset_1(k7_tmap_1(sK1,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X1))))) & v5_pre_topc(k7_tmap_1(sK1,X1),sK1,k6_tmap_1(sK1,X1)) & v1_funct_2(k7_tmap_1(sK1,X1),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X1))) & v1_funct_1(k7_tmap_1(sK1,X1))) | v3_pre_topc(X1,sK1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 47.37/6.54    introduced(choice_axiom,[])).
% 47.37/6.54  
% 47.37/6.54  fof(f57,plain,(
% 47.37/6.54    ((~m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) | ~v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) | ~v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) | ~v1_funct_1(k7_tmap_1(sK1,sK2)) | ~v3_pre_topc(sK2,sK1)) & ((m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) & v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) & v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) & v1_funct_1(k7_tmap_1(sK1,sK2))) | v3_pre_topc(sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 47.37/6.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f54,f56,f55])).
% 47.37/6.54  
% 47.37/6.54  fof(f95,plain,(
% 47.37/6.54    m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) | v3_pre_topc(sK2,sK1)),
% 47.37/6.54    inference(cnf_transformation,[],[f57])).
% 47.37/6.54  
% 47.37/6.54  fof(f91,plain,(
% 47.37/6.54    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 47.37/6.54    inference(cnf_transformation,[],[f57])).
% 47.37/6.54  
% 47.37/6.54  fof(f11,axiom,(
% 47.37/6.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 47.37/6.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.37/6.54  
% 47.37/6.54  fof(f35,plain,(
% 47.37/6.54    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 47.37/6.54    inference(ennf_transformation,[],[f11])).
% 47.37/6.54  
% 47.37/6.54  fof(f36,plain,(
% 47.37/6.54    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 47.37/6.54    inference(flattening,[],[f35])).
% 47.37/6.54  
% 47.37/6.54  fof(f79,plain,(
% 47.37/6.54    ( ! [X0,X1] : (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 47.37/6.54    inference(cnf_transformation,[],[f36])).
% 47.37/6.54  
% 47.37/6.54  fof(f88,plain,(
% 47.37/6.54    ~v2_struct_0(sK1)),
% 47.37/6.54    inference(cnf_transformation,[],[f57])).
% 47.37/6.54  
% 47.37/6.54  fof(f89,plain,(
% 47.37/6.54    v2_pre_topc(sK1)),
% 47.37/6.54    inference(cnf_transformation,[],[f57])).
% 47.37/6.54  
% 47.37/6.54  fof(f90,plain,(
% 47.37/6.54    l1_pre_topc(sK1)),
% 47.37/6.54    inference(cnf_transformation,[],[f57])).
% 47.37/6.54  
% 47.37/6.54  fof(f8,axiom,(
% 47.37/6.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_struct_0(X1) = k1_xboole_0 => k2_struct_0(X0) = k1_xboole_0) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v3_pre_topc(X3,X1) => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0))))))))),
% 47.37/6.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.37/6.54  
% 47.37/6.54  fof(f29,plain,(
% 47.37/6.54    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k2_struct_0(X0) != k1_xboole_0 & k2_struct_0(X1) = k1_xboole_0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 47.37/6.54    inference(ennf_transformation,[],[f8])).
% 47.37/6.54  
% 47.37/6.54  fof(f30,plain,(
% 47.37/6.54    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k2_struct_0(X0) != k1_xboole_0 & k2_struct_0(X1) = k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 47.37/6.54    inference(flattening,[],[f29])).
% 47.37/6.54  
% 47.37/6.54  fof(f48,plain,(
% 47.37/6.54    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k2_struct_0(X0) != k1_xboole_0 & k2_struct_0(X1) = k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 47.37/6.54    inference(nnf_transformation,[],[f30])).
% 47.37/6.54  
% 47.37/6.54  fof(f49,plain,(
% 47.37/6.54    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k2_struct_0(X0) != k1_xboole_0 & k2_struct_0(X1) = k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 47.37/6.54    inference(rectify,[],[f48])).
% 47.37/6.54  
% 47.37/6.54  fof(f50,plain,(
% 47.37/6.54    ! [X2,X1,X0] : (? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0) & v3_pre_topc(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 47.37/6.54    introduced(choice_axiom,[])).
% 47.37/6.54  
% 47.37/6.54  fof(f51,plain,(
% 47.37/6.54    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0) & v3_pre_topc(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k2_struct_0(X0) != k1_xboole_0 & k2_struct_0(X1) = k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 47.37/6.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f49,f50])).
% 47.37/6.54  
% 47.37/6.54  fof(f68,plain,(
% 47.37/6.54    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | k2_struct_0(X1) = k1_xboole_0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 47.37/6.54    inference(cnf_transformation,[],[f51])).
% 47.37/6.54  
% 47.37/6.54  fof(f78,plain,(
% 47.37/6.54    ( ! [X0,X1] : (v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 47.37/6.54    inference(cnf_transformation,[],[f36])).
% 47.37/6.54  
% 47.37/6.54  fof(f77,plain,(
% 47.37/6.54    ( ! [X0,X1] : (v1_funct_1(k7_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 47.37/6.54    inference(cnf_transformation,[],[f36])).
% 47.37/6.54  
% 47.37/6.54  fof(f10,axiom,(
% 47.37/6.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))))),
% 47.37/6.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.37/6.54  
% 47.37/6.54  fof(f18,plain,(
% 47.37/6.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))))),
% 47.37/6.54    inference(pure_predicate_removal,[],[f10])).
% 47.37/6.54  
% 47.37/6.54  fof(f33,plain,(
% 47.37/6.54    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 47.37/6.54    inference(ennf_transformation,[],[f18])).
% 47.37/6.54  
% 47.37/6.54  fof(f34,plain,(
% 47.37/6.54    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 47.37/6.54    inference(flattening,[],[f33])).
% 47.37/6.54  
% 47.37/6.54  fof(f76,plain,(
% 47.37/6.54    ( ! [X0,X1] : (l1_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 47.37/6.54    inference(cnf_transformation,[],[f34])).
% 47.37/6.54  
% 47.37/6.54  fof(f4,axiom,(
% 47.37/6.54    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 47.37/6.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.37/6.54  
% 47.37/6.54  fof(f22,plain,(
% 47.37/6.54    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 47.37/6.54    inference(ennf_transformation,[],[f4])).
% 47.37/6.54  
% 47.37/6.54  fof(f61,plain,(
% 47.37/6.54    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 47.37/6.54    inference(cnf_transformation,[],[f22])).
% 47.37/6.54  
% 47.37/6.54  fof(f3,axiom,(
% 47.37/6.54    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 47.37/6.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.37/6.54  
% 47.37/6.54  fof(f21,plain,(
% 47.37/6.54    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 47.37/6.54    inference(ennf_transformation,[],[f3])).
% 47.37/6.54  
% 47.37/6.54  fof(f60,plain,(
% 47.37/6.54    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 47.37/6.54    inference(cnf_transformation,[],[f21])).
% 47.37/6.54  
% 47.37/6.54  fof(f9,axiom,(
% 47.37/6.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,X1)))),
% 47.37/6.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.37/6.54  
% 47.37/6.54  fof(f31,plain,(
% 47.37/6.54    ! [X0] : (! [X1] : (k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 47.37/6.54    inference(ennf_transformation,[],[f9])).
% 47.37/6.54  
% 47.37/6.54  fof(f32,plain,(
% 47.37/6.54    ! [X0] : (! [X1] : (k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 47.37/6.54    inference(flattening,[],[f31])).
% 47.37/6.54  
% 47.37/6.54  fof(f74,plain,(
% 47.37/6.54    ( ! [X0,X1] : (k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 47.37/6.54    inference(cnf_transformation,[],[f32])).
% 47.37/6.54  
% 47.37/6.54  fof(f13,axiom,(
% 47.37/6.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 47.37/6.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.37/6.54  
% 47.37/6.54  fof(f39,plain,(
% 47.37/6.54    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 47.37/6.54    inference(ennf_transformation,[],[f13])).
% 47.37/6.54  
% 47.37/6.54  fof(f40,plain,(
% 47.37/6.54    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 47.37/6.54    inference(flattening,[],[f39])).
% 47.37/6.54  
% 47.37/6.54  fof(f83,plain,(
% 47.37/6.54    ( ! [X0,X1] : (u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 47.37/6.54    inference(cnf_transformation,[],[f40])).
% 47.37/6.54  
% 47.37/6.54  fof(f14,axiom,(
% 47.37/6.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) => (X1 = X2 => v3_pre_topc(X2,k6_tmap_1(X0,X1))))))),
% 47.37/6.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.37/6.54  
% 47.37/6.54  fof(f41,plain,(
% 47.37/6.54    ! [X0] : (! [X1] : (! [X2] : ((v3_pre_topc(X2,k6_tmap_1(X0,X1)) | X1 != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 47.37/6.54    inference(ennf_transformation,[],[f14])).
% 47.37/6.54  
% 47.37/6.54  fof(f42,plain,(
% 47.37/6.54    ! [X0] : (! [X1] : (! [X2] : (v3_pre_topc(X2,k6_tmap_1(X0,X1)) | X1 != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 47.37/6.54    inference(flattening,[],[f41])).
% 47.37/6.54  
% 47.37/6.54  fof(f85,plain,(
% 47.37/6.54    ( ! [X2,X0,X1] : (v3_pre_topc(X2,k6_tmap_1(X0,X1)) | X1 != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 47.37/6.54    inference(cnf_transformation,[],[f42])).
% 47.37/6.54  
% 47.37/6.54  fof(f99,plain,(
% 47.37/6.54    ( ! [X2,X0] : (v3_pre_topc(X2,k6_tmap_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 47.37/6.54    inference(equality_resolution,[],[f85])).
% 47.37/6.54  
% 47.37/6.54  fof(f92,plain,(
% 47.37/6.54    v1_funct_1(k7_tmap_1(sK1,sK2)) | v3_pre_topc(sK2,sK1)),
% 47.37/6.54    inference(cnf_transformation,[],[f57])).
% 47.37/6.54  
% 47.37/6.54  fof(f96,plain,(
% 47.37/6.54    ~m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) | ~v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) | ~v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) | ~v1_funct_1(k7_tmap_1(sK1,sK2)) | ~v3_pre_topc(sK2,sK1)),
% 47.37/6.54    inference(cnf_transformation,[],[f57])).
% 47.37/6.54  
% 47.37/6.54  fof(f2,axiom,(
% 47.37/6.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 47.37/6.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.37/6.54  
% 47.37/6.54  fof(f20,plain,(
% 47.37/6.54    ! [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 47.37/6.54    inference(ennf_transformation,[],[f2])).
% 47.37/6.54  
% 47.37/6.54  fof(f59,plain,(
% 47.37/6.54    ( ! [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 47.37/6.54    inference(cnf_transformation,[],[f20])).
% 47.37/6.54  
% 47.37/6.54  fof(f66,plain,(
% 47.37/6.54    ( ! [X4,X2,X0,X1] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v5_pre_topc(X2,X0,X1) | k2_struct_0(X1) = k1_xboole_0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 47.37/6.54    inference(cnf_transformation,[],[f51])).
% 47.37/6.54  
% 47.37/6.54  fof(f70,plain,(
% 47.37/6.54    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | v3_pre_topc(sK0(X0,X1,X2),X1) | k2_struct_0(X1) = k1_xboole_0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 47.37/6.54    inference(cnf_transformation,[],[f51])).
% 47.37/6.54  
% 47.37/6.54  fof(f94,plain,(
% 47.37/6.54    v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) | v3_pre_topc(sK2,sK1)),
% 47.37/6.54    inference(cnf_transformation,[],[f57])).
% 47.37/6.54  
% 47.37/6.54  fof(f72,plain,(
% 47.37/6.54    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | ~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0) | k2_struct_0(X1) = k1_xboole_0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 47.37/6.54    inference(cnf_transformation,[],[f51])).
% 47.37/6.54  
% 47.37/6.54  fof(f15,axiom,(
% 47.37/6.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1))))),
% 47.37/6.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.37/6.54  
% 47.37/6.54  fof(f43,plain,(
% 47.37/6.54    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 47.37/6.54    inference(ennf_transformation,[],[f15])).
% 47.37/6.54  
% 47.37/6.54  fof(f44,plain,(
% 47.37/6.54    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 47.37/6.54    inference(flattening,[],[f43])).
% 47.37/6.54  
% 47.37/6.54  fof(f52,plain,(
% 47.37/6.54    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 47.37/6.54    inference(nnf_transformation,[],[f44])).
% 47.37/6.54  
% 47.37/6.54  fof(f86,plain,(
% 47.37/6.54    ( ! [X0,X1] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 47.37/6.54    inference(cnf_transformation,[],[f52])).
% 47.37/6.54  
% 47.37/6.54  fof(f7,axiom,(
% 47.37/6.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 47.37/6.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.37/6.54  
% 47.37/6.54  fof(f27,plain,(
% 47.37/6.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 47.37/6.54    inference(ennf_transformation,[],[f7])).
% 47.37/6.54  
% 47.37/6.54  fof(f28,plain,(
% 47.37/6.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 47.37/6.54    inference(flattening,[],[f27])).
% 47.37/6.54  
% 47.37/6.54  fof(f47,plain,(
% 47.37/6.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 47.37/6.54    inference(nnf_transformation,[],[f28])).
% 47.37/6.54  
% 47.37/6.54  fof(f65,plain,(
% 47.37/6.54    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 47.37/6.54    inference(cnf_transformation,[],[f47])).
% 47.37/6.54  
% 47.37/6.54  fof(f97,plain,(
% 47.37/6.54    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 47.37/6.54    inference(equality_resolution,[],[f65])).
% 47.37/6.54  
% 47.37/6.54  fof(f75,plain,(
% 47.37/6.54    ( ! [X0,X1] : (v2_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 47.37/6.54    inference(cnf_transformation,[],[f34])).
% 47.37/6.55  
% 47.37/6.55  fof(f1,axiom,(
% 47.37/6.55    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 47.37/6.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.37/6.55  
% 47.37/6.55  fof(f19,plain,(
% 47.37/6.55    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 47.37/6.55    inference(ennf_transformation,[],[f1])).
% 47.37/6.55  
% 47.37/6.55  fof(f58,plain,(
% 47.37/6.55    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 47.37/6.55    inference(cnf_transformation,[],[f19])).
% 47.37/6.55  
% 47.37/6.55  fof(f71,plain,(
% 47.37/6.55    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | v3_pre_topc(sK0(X0,X1,X2),X1) | k2_struct_0(X0) != k1_xboole_0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 47.37/6.55    inference(cnf_transformation,[],[f51])).
% 47.37/6.55  
% 47.37/6.55  fof(f69,plain,(
% 47.37/6.55    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | k2_struct_0(X0) != k1_xboole_0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 47.37/6.55    inference(cnf_transformation,[],[f51])).
% 47.37/6.55  
% 47.37/6.55  fof(f93,plain,(
% 47.37/6.55    v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) | v3_pre_topc(sK2,sK1)),
% 47.37/6.55    inference(cnf_transformation,[],[f57])).
% 47.37/6.55  
% 47.37/6.55  fof(f67,plain,(
% 47.37/6.55    ( ! [X4,X2,X0,X1] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v5_pre_topc(X2,X0,X1) | k2_struct_0(X0) != k1_xboole_0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 47.37/6.55    inference(cnf_transformation,[],[f51])).
% 47.37/6.55  
% 47.37/6.55  fof(f73,plain,(
% 47.37/6.55    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | ~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0) | k2_struct_0(X0) != k1_xboole_0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 47.37/6.55    inference(cnf_transformation,[],[f51])).
% 47.37/6.55  
% 47.37/6.55  cnf(c_31,negated_conjecture,
% 47.37/6.55      ( v3_pre_topc(sK2,sK1)
% 47.37/6.55      | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) ),
% 47.37/6.55      inference(cnf_transformation,[],[f95]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3384,negated_conjecture,
% 47.37/6.55      ( v3_pre_topc(sK2,sK1)
% 47.37/6.55      | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) ),
% 47.37/6.55      inference(subtyping,[status(esa)],[c_31]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_4328,plain,
% 47.37/6.55      ( v3_pre_topc(sK2,sK1) = iProver_top
% 47.37/6.55      | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) = iProver_top ),
% 47.37/6.55      inference(predicate_to_equality,[status(thm)],[c_3384]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_35,negated_conjecture,
% 47.37/6.55      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 47.37/6.55      inference(cnf_transformation,[],[f91]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_42,plain,
% 47.37/6.55      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 47.37/6.55      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_19,plain,
% 47.37/6.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.37/6.55      | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
% 47.37/6.55      | ~ v2_pre_topc(X1)
% 47.37/6.55      | v2_struct_0(X1)
% 47.37/6.55      | ~ l1_pre_topc(X1) ),
% 47.37/6.55      inference(cnf_transformation,[],[f79]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_38,negated_conjecture,
% 47.37/6.55      ( ~ v2_struct_0(sK1) ),
% 47.37/6.55      inference(cnf_transformation,[],[f88]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_621,plain,
% 47.37/6.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.37/6.55      | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
% 47.37/6.55      | ~ v2_pre_topc(X1)
% 47.37/6.55      | ~ l1_pre_topc(X1)
% 47.37/6.55      | sK1 != X1 ),
% 47.37/6.55      inference(resolution_lifted,[status(thm)],[c_19,c_38]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_622,plain,
% 47.37/6.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.37/6.55      | m1_subset_1(k7_tmap_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0)))))
% 47.37/6.55      | ~ v2_pre_topc(sK1)
% 47.37/6.55      | ~ l1_pre_topc(sK1) ),
% 47.37/6.55      inference(unflattening,[status(thm)],[c_621]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_37,negated_conjecture,
% 47.37/6.55      ( v2_pre_topc(sK1) ),
% 47.37/6.55      inference(cnf_transformation,[],[f89]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_36,negated_conjecture,
% 47.37/6.55      ( l1_pre_topc(sK1) ),
% 47.37/6.55      inference(cnf_transformation,[],[f90]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_626,plain,
% 47.37/6.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.37/6.55      | m1_subset_1(k7_tmap_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0))))) ),
% 47.37/6.55      inference(global_propositional_subsumption,
% 47.37/6.55                [status(thm)],
% 47.37/6.55                [c_622,c_37,c_36]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3366,plain,
% 47.37/6.55      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.37/6.55      | m1_subset_1(k7_tmap_1(sK1,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_55))))) ),
% 47.37/6.55      inference(subtyping,[status(esa)],[c_626]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3521,plain,
% 47.37/6.55      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 47.37/6.55      | m1_subset_1(k7_tmap_1(sK1,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_55))))) = iProver_top ),
% 47.37/6.55      inference(predicate_to_equality,[status(thm)],[c_3366]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3523,plain,
% 47.37/6.55      ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) = iProver_top
% 47.37/6.55      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 47.37/6.55      inference(instantiation,[status(thm)],[c_3521]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_4573,plain,
% 47.37/6.55      ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) = iProver_top ),
% 47.37/6.55      inference(global_propositional_subsumption,
% 47.37/6.55                [status(thm)],
% 47.37/6.55                [c_4328,c_42,c_3523]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_13,plain,
% 47.37/6.55      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 47.37/6.55      | v5_pre_topc(X0,X1,X2)
% 47.37/6.55      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 47.37/6.55      | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
% 47.37/6.55      | ~ v1_funct_1(X0)
% 47.37/6.55      | ~ l1_pre_topc(X1)
% 47.37/6.55      | ~ l1_pre_topc(X2)
% 47.37/6.55      | k2_struct_0(X2) = k1_xboole_0 ),
% 47.37/6.55      inference(cnf_transformation,[],[f68]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3388,plain,
% 47.37/6.55      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58))
% 47.37/6.55      | v5_pre_topc(X0_55,X0_58,X1_58)
% 47.37/6.55      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
% 47.37/6.55      | m1_subset_1(sK0(X0_58,X1_58,X0_55),k1_zfmisc_1(u1_struct_0(X1_58)))
% 47.37/6.55      | ~ v1_funct_1(X0_55)
% 47.37/6.55      | ~ l1_pre_topc(X0_58)
% 47.37/6.55      | ~ l1_pre_topc(X1_58)
% 47.37/6.55      | k2_struct_0(X1_58) = k1_xboole_0 ),
% 47.37/6.55      inference(subtyping,[status(esa)],[c_13]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_4324,plain,
% 47.37/6.55      ( k2_struct_0(X0_58) = k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,u1_struct_0(X1_58),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,X1_58,X0_58) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | m1_subset_1(sK0(X1_58,X0_58,X0_55),k1_zfmisc_1(u1_struct_0(X0_58))) = iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X1_58) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top ),
% 47.37/6.55      inference(predicate_to_equality,[status(thm)],[c_3388]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_4792,plain,
% 47.37/6.55      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 47.37/6.55      | v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
% 47.37/6.55      | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.55      | m1_subset_1(sK0(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2)),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) = iProver_top
% 47.37/6.55      | v1_funct_1(k7_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | l1_pre_topc(sK1) != iProver_top ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_4573,c_4324]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_41,plain,
% 47.37/6.55      ( l1_pre_topc(sK1) = iProver_top ),
% 47.37/6.55      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_20,plain,
% 47.37/6.55      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
% 47.37/6.55      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 47.37/6.55      | ~ v2_pre_topc(X0)
% 47.37/6.55      | v2_struct_0(X0)
% 47.37/6.55      | ~ l1_pre_topc(X0) ),
% 47.37/6.55      inference(cnf_transformation,[],[f78]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_486,plain,
% 47.37/6.55      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
% 47.37/6.55      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 47.37/6.55      | ~ v2_pre_topc(X0)
% 47.37/6.55      | ~ l1_pre_topc(X0)
% 47.37/6.55      | sK1 != X0 ),
% 47.37/6.55      inference(resolution_lifted,[status(thm)],[c_20,c_38]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_487,plain,
% 47.37/6.55      ( v1_funct_2(k7_tmap_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0)))
% 47.37/6.55      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.37/6.55      | ~ v2_pre_topc(sK1)
% 47.37/6.55      | ~ l1_pre_topc(sK1) ),
% 47.37/6.55      inference(unflattening,[status(thm)],[c_486]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_491,plain,
% 47.37/6.55      ( v1_funct_2(k7_tmap_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0)))
% 47.37/6.55      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 47.37/6.55      inference(global_propositional_subsumption,
% 47.37/6.55                [status(thm)],
% 47.37/6.55                [c_487,c_37,c_36]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3373,plain,
% 47.37/6.55      ( v1_funct_2(k7_tmap_1(sK1,X0_55),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_55)))
% 47.37/6.55      | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 47.37/6.55      inference(subtyping,[status(esa)],[c_491]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3500,plain,
% 47.37/6.55      ( v1_funct_2(k7_tmap_1(sK1,X0_55),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_55))) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 47.37/6.55      inference(predicate_to_equality,[status(thm)],[c_3373]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3502,plain,
% 47.37/6.55      ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) = iProver_top
% 47.37/6.55      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 47.37/6.55      inference(instantiation,[status(thm)],[c_3500]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_21,plain,
% 47.37/6.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.37/6.55      | ~ v2_pre_topc(X1)
% 47.37/6.55      | v1_funct_1(k7_tmap_1(X1,X0))
% 47.37/6.55      | v2_struct_0(X1)
% 47.37/6.55      | ~ l1_pre_topc(X1) ),
% 47.37/6.55      inference(cnf_transformation,[],[f77]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_603,plain,
% 47.37/6.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.37/6.55      | ~ v2_pre_topc(X1)
% 47.37/6.55      | v1_funct_1(k7_tmap_1(X1,X0))
% 47.37/6.55      | ~ l1_pre_topc(X1)
% 47.37/6.55      | sK1 != X1 ),
% 47.37/6.55      inference(resolution_lifted,[status(thm)],[c_21,c_38]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_604,plain,
% 47.37/6.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.37/6.55      | ~ v2_pre_topc(sK1)
% 47.37/6.55      | v1_funct_1(k7_tmap_1(sK1,X0))
% 47.37/6.55      | ~ l1_pre_topc(sK1) ),
% 47.37/6.55      inference(unflattening,[status(thm)],[c_603]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_608,plain,
% 47.37/6.55      ( v1_funct_1(k7_tmap_1(sK1,X0))
% 47.37/6.55      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 47.37/6.55      inference(global_propositional_subsumption,
% 47.37/6.55                [status(thm)],
% 47.37/6.55                [c_604,c_37,c_36]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_609,plain,
% 47.37/6.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.37/6.55      | v1_funct_1(k7_tmap_1(sK1,X0)) ),
% 47.37/6.55      inference(renaming,[status(thm)],[c_608]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3367,plain,
% 47.37/6.55      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.37/6.55      | v1_funct_1(k7_tmap_1(sK1,X0_55)) ),
% 47.37/6.55      inference(subtyping,[status(esa)],[c_609]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3518,plain,
% 47.37/6.55      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 47.37/6.55      | v1_funct_1(k7_tmap_1(sK1,X0_55)) = iProver_top ),
% 47.37/6.55      inference(predicate_to_equality,[status(thm)],[c_3367]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3520,plain,
% 47.37/6.55      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 47.37/6.55      | v1_funct_1(k7_tmap_1(sK1,sK2)) = iProver_top ),
% 47.37/6.55      inference(instantiation,[status(thm)],[c_3518]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_17,plain,
% 47.37/6.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.37/6.55      | ~ v2_pre_topc(X1)
% 47.37/6.55      | v2_struct_0(X1)
% 47.37/6.55      | ~ l1_pre_topc(X1)
% 47.37/6.55      | l1_pre_topc(k6_tmap_1(X1,X0)) ),
% 47.37/6.55      inference(cnf_transformation,[],[f76]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_657,plain,
% 47.37/6.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.37/6.55      | ~ v2_pre_topc(X1)
% 47.37/6.55      | ~ l1_pre_topc(X1)
% 47.37/6.55      | l1_pre_topc(k6_tmap_1(X1,X0))
% 47.37/6.55      | sK1 != X1 ),
% 47.37/6.55      inference(resolution_lifted,[status(thm)],[c_17,c_38]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_658,plain,
% 47.37/6.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.37/6.55      | ~ v2_pre_topc(sK1)
% 47.37/6.55      | l1_pre_topc(k6_tmap_1(sK1,X0))
% 47.37/6.55      | ~ l1_pre_topc(sK1) ),
% 47.37/6.55      inference(unflattening,[status(thm)],[c_657]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_662,plain,
% 47.37/6.55      ( l1_pre_topc(k6_tmap_1(sK1,X0))
% 47.37/6.55      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 47.37/6.55      inference(global_propositional_subsumption,
% 47.37/6.55                [status(thm)],
% 47.37/6.55                [c_658,c_37,c_36]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_663,plain,
% 47.37/6.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.37/6.55      | l1_pre_topc(k6_tmap_1(sK1,X0)) ),
% 47.37/6.55      inference(renaming,[status(thm)],[c_662]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3364,plain,
% 47.37/6.55      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.37/6.55      | l1_pre_topc(k6_tmap_1(sK1,X0_55)) ),
% 47.37/6.55      inference(subtyping,[status(esa)],[c_663]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3527,plain,
% 47.37/6.55      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 47.37/6.55      | l1_pre_topc(k6_tmap_1(sK1,X0_55)) = iProver_top ),
% 47.37/6.55      inference(predicate_to_equality,[status(thm)],[c_3364]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3529,plain,
% 47.37/6.55      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 47.37/6.55      | l1_pre_topc(k6_tmap_1(sK1,sK2)) = iProver_top ),
% 47.37/6.55      inference(instantiation,[status(thm)],[c_3527]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_6468,plain,
% 47.37/6.55      ( m1_subset_1(sK0(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2)),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) = iProver_top
% 47.37/6.55      | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.55      | k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0 ),
% 47.37/6.55      inference(global_propositional_subsumption,
% 47.37/6.55                [status(thm)],
% 47.37/6.55                [c_4792,c_41,c_42,c_3502,c_3520,c_3529]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_6469,plain,
% 47.37/6.55      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 47.37/6.55      | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.55      | m1_subset_1(sK0(sK1,k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2)),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) = iProver_top ),
% 47.37/6.55      inference(renaming,[status(thm)],[c_6468]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3379,negated_conjecture,
% 47.37/6.55      ( l1_pre_topc(sK1) ),
% 47.37/6.55      inference(subtyping,[status(esa)],[c_36]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_4333,plain,
% 47.37/6.55      ( l1_pre_topc(sK1) = iProver_top ),
% 47.37/6.55      inference(predicate_to_equality,[status(thm)],[c_3379]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3,plain,
% 47.37/6.55      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 47.37/6.55      inference(cnf_transformation,[],[f61]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_2,plain,
% 47.37/6.55      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 47.37/6.55      inference(cnf_transformation,[],[f60]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_439,plain,
% 47.37/6.55      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 47.37/6.55      inference(resolution,[status(thm)],[c_3,c_2]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3377,plain,
% 47.37/6.55      ( ~ l1_pre_topc(X0_58) | u1_struct_0(X0_58) = k2_struct_0(X0_58) ),
% 47.37/6.55      inference(subtyping,[status(esa)],[c_439]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_4335,plain,
% 47.37/6.55      ( u1_struct_0(X0_58) = k2_struct_0(X0_58)
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top ),
% 47.37/6.55      inference(predicate_to_equality,[status(thm)],[c_3377]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_5702,plain,
% 47.37/6.55      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_4333,c_4335]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3380,negated_conjecture,
% 47.37/6.55      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 47.37/6.55      inference(subtyping,[status(esa)],[c_35]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_4332,plain,
% 47.37/6.55      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 47.37/6.55      inference(predicate_to_equality,[status(thm)],[c_3380]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_16,plain,
% 47.37/6.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.37/6.55      | ~ v2_pre_topc(X1)
% 47.37/6.55      | v2_struct_0(X1)
% 47.37/6.55      | ~ l1_pre_topc(X1)
% 47.37/6.55      | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1)) ),
% 47.37/6.55      inference(cnf_transformation,[],[f74]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_675,plain,
% 47.37/6.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.37/6.55      | ~ v2_pre_topc(X1)
% 47.37/6.55      | ~ l1_pre_topc(X1)
% 47.37/6.55      | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1))
% 47.37/6.55      | sK1 != X1 ),
% 47.37/6.55      inference(resolution_lifted,[status(thm)],[c_16,c_38]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_676,plain,
% 47.37/6.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.37/6.55      | ~ v2_pre_topc(sK1)
% 47.37/6.55      | ~ l1_pre_topc(sK1)
% 47.37/6.55      | k7_tmap_1(sK1,X0) = k6_partfun1(u1_struct_0(sK1)) ),
% 47.37/6.55      inference(unflattening,[status(thm)],[c_675]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_680,plain,
% 47.37/6.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.37/6.55      | k7_tmap_1(sK1,X0) = k6_partfun1(u1_struct_0(sK1)) ),
% 47.37/6.55      inference(global_propositional_subsumption,
% 47.37/6.55                [status(thm)],
% 47.37/6.55                [c_676,c_37,c_36]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3363,plain,
% 47.37/6.55      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.37/6.55      | k7_tmap_1(sK1,X0_55) = k6_partfun1(u1_struct_0(sK1)) ),
% 47.37/6.55      inference(subtyping,[status(esa)],[c_680]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_4349,plain,
% 47.37/6.55      ( k7_tmap_1(sK1,X0_55) = k6_partfun1(u1_struct_0(sK1))
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 47.37/6.55      inference(predicate_to_equality,[status(thm)],[c_3363]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_5471,plain,
% 47.37/6.55      ( k7_tmap_1(sK1,sK2) = k6_partfun1(u1_struct_0(sK1)) ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_4332,c_4349]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_5776,plain,
% 47.37/6.55      ( k7_tmap_1(sK1,sK2) = k6_partfun1(k2_struct_0(sK1)) ),
% 47.37/6.55      inference(demodulation,[status(thm)],[c_5702,c_5471]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_26,plain,
% 47.37/6.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.37/6.55      | ~ v2_pre_topc(X1)
% 47.37/6.55      | v2_struct_0(X1)
% 47.37/6.55      | ~ l1_pre_topc(X1)
% 47.37/6.55      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
% 47.37/6.55      inference(cnf_transformation,[],[f83]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_567,plain,
% 47.37/6.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.37/6.55      | ~ v2_pre_topc(X1)
% 47.37/6.55      | ~ l1_pre_topc(X1)
% 47.37/6.55      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1)
% 47.37/6.55      | sK1 != X1 ),
% 47.37/6.55      inference(resolution_lifted,[status(thm)],[c_26,c_38]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_568,plain,
% 47.37/6.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.37/6.55      | ~ v2_pre_topc(sK1)
% 47.37/6.55      | ~ l1_pre_topc(sK1)
% 47.37/6.55      | u1_struct_0(k6_tmap_1(sK1,X0)) = u1_struct_0(sK1) ),
% 47.37/6.55      inference(unflattening,[status(thm)],[c_567]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_572,plain,
% 47.37/6.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.37/6.55      | u1_struct_0(k6_tmap_1(sK1,X0)) = u1_struct_0(sK1) ),
% 47.37/6.55      inference(global_propositional_subsumption,
% 47.37/6.55                [status(thm)],
% 47.37/6.55                [c_568,c_37,c_36]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3369,plain,
% 47.37/6.55      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.37/6.55      | u1_struct_0(k6_tmap_1(sK1,X0_55)) = u1_struct_0(sK1) ),
% 47.37/6.55      inference(subtyping,[status(esa)],[c_572]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_4343,plain,
% 47.37/6.55      ( u1_struct_0(k6_tmap_1(sK1,X0_55)) = u1_struct_0(sK1)
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 47.37/6.55      inference(predicate_to_equality,[status(thm)],[c_3369]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_5255,plain,
% 47.37/6.55      ( u1_struct_0(k6_tmap_1(sK1,sK2)) = u1_struct_0(sK1) ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_4332,c_4343]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_5778,plain,
% 47.37/6.55      ( u1_struct_0(k6_tmap_1(sK1,sK2)) = k2_struct_0(sK1) ),
% 47.37/6.55      inference(demodulation,[status(thm)],[c_5702,c_5255]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_6472,plain,
% 47.37/6.55      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 47.37/6.55      | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.55      | m1_subset_1(sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
% 47.37/6.55      inference(light_normalisation,[status(thm)],[c_6469,c_5776,c_5778]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_4348,plain,
% 47.37/6.55      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 47.37/6.55      | l1_pre_topc(k6_tmap_1(sK1,X0_55)) = iProver_top ),
% 47.37/6.55      inference(predicate_to_equality,[status(thm)],[c_3364]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_5207,plain,
% 47.37/6.55      ( l1_pre_topc(k6_tmap_1(sK1,sK2)) = iProver_top ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_4332,c_4348]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_5703,plain,
% 47.37/6.55      ( u1_struct_0(k6_tmap_1(sK1,sK2)) = k2_struct_0(k6_tmap_1(sK1,sK2)) ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_5207,c_4335]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_5704,plain,
% 47.37/6.55      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = u1_struct_0(sK1) ),
% 47.37/6.55      inference(light_normalisation,[status(thm)],[c_5703,c_5255]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_5705,plain,
% 47.37/6.55      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k2_struct_0(sK1) ),
% 47.37/6.55      inference(demodulation,[status(thm)],[c_5702,c_5704]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_6473,plain,
% 47.37/6.55      ( k2_struct_0(sK1) = k1_xboole_0
% 47.37/6.55      | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.55      | m1_subset_1(sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
% 47.37/6.55      inference(demodulation,[status(thm)],[c_6472,c_5705]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_5777,plain,
% 47.37/6.55      ( k7_tmap_1(sK1,X0_55) = k6_partfun1(k2_struct_0(sK1))
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 47.37/6.55      inference(demodulation,[status(thm)],[c_5702,c_4349]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_7438,plain,
% 47.37/6.55      ( k2_struct_0(sK1) = k1_xboole_0
% 47.37/6.55      | k7_tmap_1(sK1,sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))) = k6_partfun1(k2_struct_0(sK1))
% 47.37/6.55      | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) = iProver_top ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_6473,c_5777]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3399,plain,( X0_55 = X0_55 ),theory(equality) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3445,plain,
% 47.37/6.55      ( sK2 = sK2 ),
% 47.37/6.55      inference(instantiation,[status(thm)],[c_3399]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_27,plain,
% 47.37/6.55      ( v3_pre_topc(X0,k6_tmap_1(X1,X0))
% 47.37/6.55      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.37/6.55      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X0))))
% 47.37/6.55      | ~ v2_pre_topc(X1)
% 47.37/6.55      | v2_struct_0(X1)
% 47.37/6.55      | ~ l1_pre_topc(X1) ),
% 47.37/6.55      inference(cnf_transformation,[],[f99]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_546,plain,
% 47.37/6.55      ( v3_pre_topc(X0,k6_tmap_1(X1,X0))
% 47.37/6.55      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.37/6.55      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X0))))
% 47.37/6.55      | ~ v2_pre_topc(X1)
% 47.37/6.55      | ~ l1_pre_topc(X1)
% 47.37/6.55      | sK1 != X1 ),
% 47.37/6.55      inference(resolution_lifted,[status(thm)],[c_27,c_38]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_547,plain,
% 47.37/6.55      ( v3_pre_topc(X0,k6_tmap_1(sK1,X0))
% 47.37/6.55      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0))))
% 47.37/6.55      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.37/6.55      | ~ v2_pre_topc(sK1)
% 47.37/6.55      | ~ l1_pre_topc(sK1) ),
% 47.37/6.55      inference(unflattening,[status(thm)],[c_546]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_551,plain,
% 47.37/6.55      ( v3_pre_topc(X0,k6_tmap_1(sK1,X0))
% 47.37/6.55      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0))))
% 47.37/6.55      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 47.37/6.55      inference(global_propositional_subsumption,
% 47.37/6.55                [status(thm)],
% 47.37/6.55                [c_547,c_37,c_36]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3370,plain,
% 47.37/6.55      ( v3_pre_topc(X0_55,k6_tmap_1(sK1,X0_55))
% 47.37/6.55      | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0_55))))
% 47.37/6.55      | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 47.37/6.55      inference(subtyping,[status(esa)],[c_551]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3509,plain,
% 47.37/6.55      ( v3_pre_topc(X0_55,k6_tmap_1(sK1,X0_55)) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0_55)))) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 47.37/6.55      inference(predicate_to_equality,[status(thm)],[c_3370]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3511,plain,
% 47.37/6.55      ( v3_pre_topc(sK2,k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.55      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) != iProver_top
% 47.37/6.55      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 47.37/6.55      inference(instantiation,[status(thm)],[c_3509]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3513,plain,
% 47.37/6.55      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.37/6.55      | u1_struct_0(k6_tmap_1(sK1,sK2)) = u1_struct_0(sK1) ),
% 47.37/6.55      inference(instantiation,[status(thm)],[c_3369]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3411,plain,
% 47.37/6.55      ( ~ m1_subset_1(X0_55,X0_56)
% 47.37/6.55      | m1_subset_1(X1_55,X1_56)
% 47.37/6.55      | X1_56 != X0_56
% 47.37/6.55      | X1_55 != X0_55 ),
% 47.37/6.55      theory(equality) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_4426,plain,
% 47.37/6.55      ( ~ m1_subset_1(X0_55,X0_56)
% 47.37/6.55      | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X1_55))))
% 47.37/6.55      | k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X1_55))) != X0_56
% 47.37/6.55      | X1_55 != X0_55 ),
% 47.37/6.55      inference(instantiation,[status(thm)],[c_3411]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_4448,plain,
% 47.37/6.55      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0_55))))
% 47.37/6.55      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.37/6.55      | k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0_55))) != k1_zfmisc_1(u1_struct_0(sK1))
% 47.37/6.55      | X0_55 != sK2 ),
% 47.37/6.55      inference(instantiation,[status(thm)],[c_4426]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_4449,plain,
% 47.37/6.55      ( k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0_55))) != k1_zfmisc_1(u1_struct_0(sK1))
% 47.37/6.55      | X0_55 != sK2
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0_55)))) = iProver_top
% 47.37/6.55      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 47.37/6.55      inference(predicate_to_equality,[status(thm)],[c_4448]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_4451,plain,
% 47.37/6.55      ( k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2))) != k1_zfmisc_1(u1_struct_0(sK1))
% 47.37/6.55      | sK2 != sK2
% 47.37/6.55      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) = iProver_top
% 47.37/6.55      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 47.37/6.55      inference(instantiation,[status(thm)],[c_4449]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3410,plain,
% 47.37/6.55      ( X0_57 != X1_57 | k1_zfmisc_1(X0_57) = k1_zfmisc_1(X1_57) ),
% 47.37/6.55      theory(equality) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_4504,plain,
% 47.37/6.55      ( u1_struct_0(k6_tmap_1(sK1,X0_55)) != u1_struct_0(sK1)
% 47.37/6.55      | k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0_55))) = k1_zfmisc_1(u1_struct_0(sK1)) ),
% 47.37/6.55      inference(instantiation,[status(thm)],[c_3410]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_4505,plain,
% 47.37/6.55      ( u1_struct_0(k6_tmap_1(sK1,sK2)) != u1_struct_0(sK1)
% 47.37/6.55      | k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2))) = k1_zfmisc_1(u1_struct_0(sK1)) ),
% 47.37/6.55      inference(instantiation,[status(thm)],[c_4504]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_5785,plain,
% 47.37/6.55      ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
% 47.37/6.55      inference(demodulation,[status(thm)],[c_5702,c_4332]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_34,negated_conjecture,
% 47.37/6.55      ( v3_pre_topc(sK2,sK1) | v1_funct_1(k7_tmap_1(sK1,sK2)) ),
% 47.37/6.55      inference(cnf_transformation,[],[f92]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3381,negated_conjecture,
% 47.37/6.55      ( v3_pre_topc(sK2,sK1) | v1_funct_1(k7_tmap_1(sK1,sK2)) ),
% 47.37/6.55      inference(subtyping,[status(esa)],[c_34]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_4331,plain,
% 47.37/6.55      ( v3_pre_topc(sK2,sK1) = iProver_top
% 47.37/6.55      | v1_funct_1(k7_tmap_1(sK1,sK2)) = iProver_top ),
% 47.37/6.55      inference(predicate_to_equality,[status(thm)],[c_3381]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_4491,plain,
% 47.37/6.55      ( v1_funct_1(k7_tmap_1(sK1,sK2)) = iProver_top ),
% 47.37/6.55      inference(global_propositional_subsumption,
% 47.37/6.55                [status(thm)],
% 47.37/6.55                [c_4331,c_42,c_3520]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_5565,plain,
% 47.37/6.55      ( v1_funct_1(k6_partfun1(u1_struct_0(sK1))) = iProver_top ),
% 47.37/6.55      inference(demodulation,[status(thm)],[c_5471,c_4491]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_5899,plain,
% 47.37/6.55      ( v1_funct_1(k6_partfun1(k2_struct_0(sK1))) = iProver_top ),
% 47.37/6.55      inference(light_normalisation,[status(thm)],[c_5565,c_5702]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_30,negated_conjecture,
% 47.37/6.55      ( ~ v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
% 47.37/6.55      | ~ v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
% 47.37/6.55      | ~ v3_pre_topc(sK2,sK1)
% 47.37/6.55      | ~ m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))))
% 47.37/6.55      | ~ v1_funct_1(k7_tmap_1(sK1,sK2)) ),
% 47.37/6.55      inference(cnf_transformation,[],[f96]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3385,negated_conjecture,
% 47.37/6.55      ( ~ v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
% 47.37/6.55      | ~ v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
% 47.37/6.55      | ~ v3_pre_topc(sK2,sK1)
% 47.37/6.55      | ~ m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))))
% 47.37/6.55      | ~ v1_funct_1(k7_tmap_1(sK1,sK2)) ),
% 47.37/6.55      inference(subtyping,[status(esa)],[c_30]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_4327,plain,
% 47.37/6.55      ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
% 47.37/6.55      | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v3_pre_topc(sK2,sK1) != iProver_top
% 47.37/6.55      | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
% 47.37/6.55      | v1_funct_1(k7_tmap_1(sK1,sK2)) != iProver_top ),
% 47.37/6.55      inference(predicate_to_equality,[status(thm)],[c_3385]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3501,plain,
% 47.37/6.55      ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
% 47.37/6.55      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 47.37/6.55      inference(instantiation,[status(thm)],[c_3373]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3519,plain,
% 47.37/6.55      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.37/6.55      | v1_funct_1(k7_tmap_1(sK1,sK2)) ),
% 47.37/6.55      inference(instantiation,[status(thm)],[c_3367]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3522,plain,
% 47.37/6.55      ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))))
% 47.37/6.55      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 47.37/6.55      inference(instantiation,[status(thm)],[c_3366]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3595,negated_conjecture,
% 47.37/6.55      ( ~ v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
% 47.37/6.55      | ~ v3_pre_topc(sK2,sK1) ),
% 47.37/6.55      inference(global_propositional_subsumption,
% 47.37/6.55                [status(thm)],
% 47.37/6.55                [c_3385,c_35,c_30,c_3501,c_3519,c_3522]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3597,plain,
% 47.37/6.55      ( v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v3_pre_topc(sK2,sK1) != iProver_top ),
% 47.37/6.55      inference(predicate_to_equality,[status(thm)],[c_3595]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_4422,plain,
% 47.37/6.55      ( v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v3_pre_topc(sK2,sK1) != iProver_top ),
% 47.37/6.55      inference(global_propositional_subsumption,
% 47.37/6.55                [status(thm)],
% 47.37/6.55                [c_4327,c_3597]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_5566,plain,
% 47.37/6.55      ( v5_pre_topc(k6_partfun1(u1_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v3_pre_topc(sK2,sK1) != iProver_top ),
% 47.37/6.55      inference(demodulation,[status(thm)],[c_5471,c_4422]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_5990,plain,
% 47.37/6.55      ( v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v3_pre_topc(sK2,sK1) != iProver_top ),
% 47.37/6.55      inference(light_normalisation,[status(thm)],[c_5566,c_5702]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_4339,plain,
% 47.37/6.55      ( v1_funct_2(k7_tmap_1(sK1,X0_55),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_55))) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 47.37/6.55      inference(predicate_to_equality,[status(thm)],[c_3373]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_6098,plain,
% 47.37/6.55      ( v1_funct_2(k7_tmap_1(sK1,X0_55),k2_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_55))) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 47.37/6.55      inference(light_normalisation,[status(thm)],[c_4339,c_5702]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_6536,plain,
% 47.37/6.55      ( v1_funct_2(k6_partfun1(k2_struct_0(sK1)),k2_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) = iProver_top
% 47.37/6.55      | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_5776,c_6098]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_6537,plain,
% 47.37/6.55      ( v1_funct_2(k6_partfun1(k2_struct_0(sK1)),k2_struct_0(sK1),k2_struct_0(sK1)) = iProver_top
% 47.37/6.55      | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 47.37/6.55      inference(light_normalisation,[status(thm)],[c_6536,c_5778]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_4346,plain,
% 47.37/6.55      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 47.37/6.55      | m1_subset_1(k7_tmap_1(sK1,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_55))))) = iProver_top ),
% 47.37/6.55      inference(predicate_to_equality,[status(thm)],[c_3366]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_6103,plain,
% 47.37/6.55      ( m1_subset_1(X0_55,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 47.37/6.55      | m1_subset_1(k7_tmap_1(sK1,X0_55),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_55))))) = iProver_top ),
% 47.37/6.55      inference(light_normalisation,[status(thm)],[c_4346,c_5702]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_6535,plain,
% 47.37/6.55      ( m1_subset_1(k6_partfun1(k2_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) = iProver_top
% 47.37/6.55      | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_5776,c_6103]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_6538,plain,
% 47.37/6.55      ( m1_subset_1(k6_partfun1(k2_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) = iProver_top
% 47.37/6.55      | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 47.37/6.55      inference(light_normalisation,[status(thm)],[c_6535,c_5778]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_1,plain,
% 47.37/6.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 47.37/6.55      | k8_relset_1(X1,X1,k6_partfun1(X1),X0) = X0 ),
% 47.37/6.55      inference(cnf_transformation,[],[f59]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3396,plain,
% 47.37/6.55      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(X0_57))
% 47.37/6.55      | k8_relset_1(X0_57,X0_57,k6_partfun1(X0_57),X0_55) = X0_55 ),
% 47.37/6.55      inference(subtyping,[status(esa)],[c_1]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_4316,plain,
% 47.37/6.55      ( k8_relset_1(X0_57,X0_57,k6_partfun1(X0_57),X0_55) = X0_55
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(X0_57)) != iProver_top ),
% 47.37/6.55      inference(predicate_to_equality,[status(thm)],[c_3396]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_4628,plain,
% 47.37/6.55      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k6_partfun1(u1_struct_0(sK1)),sK2) = sK2 ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_4332,c_4316]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_5783,plain,
% 47.37/6.55      ( k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),k6_partfun1(k2_struct_0(sK1)),sK2) = sK2 ),
% 47.37/6.55      inference(demodulation,[status(thm)],[c_5702,c_4628]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_15,plain,
% 47.37/6.55      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 47.37/6.55      | ~ v5_pre_topc(X0,X1,X2)
% 47.37/6.55      | ~ v3_pre_topc(X3,X2)
% 47.37/6.55      | v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
% 47.37/6.55      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 47.37/6.55      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 47.37/6.55      | ~ v1_funct_1(X0)
% 47.37/6.55      | ~ l1_pre_topc(X1)
% 47.37/6.55      | ~ l1_pre_topc(X2)
% 47.37/6.55      | k2_struct_0(X2) = k1_xboole_0 ),
% 47.37/6.55      inference(cnf_transformation,[],[f66]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3386,plain,
% 47.37/6.55      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58))
% 47.37/6.55      | ~ v5_pre_topc(X0_55,X0_58,X1_58)
% 47.37/6.55      | ~ v3_pre_topc(X1_55,X1_58)
% 47.37/6.55      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_55,X1_55),X0_58)
% 47.37/6.55      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
% 47.37/6.55      | ~ m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(X1_58)))
% 47.37/6.55      | ~ v1_funct_1(X0_55)
% 47.37/6.55      | ~ l1_pre_topc(X0_58)
% 47.37/6.55      | ~ l1_pre_topc(X1_58)
% 47.37/6.55      | k2_struct_0(X1_58) = k1_xboole_0 ),
% 47.37/6.55      inference(subtyping,[status(esa)],[c_15]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_4326,plain,
% 47.37/6.55      ( k2_struct_0(X0_58) = k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,u1_struct_0(X1_58),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,X1_58,X0_58) != iProver_top
% 47.37/6.55      | v3_pre_topc(X1_55,X0_58) != iProver_top
% 47.37/6.55      | v3_pre_topc(k8_relset_1(u1_struct_0(X1_58),u1_struct_0(X0_58),X0_55,X1_55),X1_58) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(X0_58))) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X1_58) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top ),
% 47.37/6.55      inference(predicate_to_equality,[status(thm)],[c_3386]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_5352,plain,
% 47.37/6.55      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,X0_58,k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v3_pre_topc(X1_55,k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_58),u1_struct_0(sK1),X0_55,X1_55),X0_58) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
% 47.37/6.55      | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top
% 47.37/6.55      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_5255,c_4326]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_5371,plain,
% 47.37/6.55      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(sK1)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,X0_58,k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v3_pre_topc(X1_55,k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_58),u1_struct_0(sK1),X0_55,X1_55),X0_58) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK1)))) != iProver_top
% 47.37/6.55      | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top
% 47.37/6.55      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 47.37/6.55      inference(light_normalisation,[status(thm)],[c_5352,c_5255]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_10288,plain,
% 47.37/6.55      ( l1_pre_topc(X0_58) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK1)))) != iProver_top
% 47.37/6.55      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_58),u1_struct_0(sK1),X0_55,X1_55),X0_58) = iProver_top
% 47.37/6.55      | v3_pre_topc(X1_55,k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,X0_58,k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(sK1)) != iProver_top
% 47.37/6.55      | k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0 ),
% 47.37/6.55      inference(global_propositional_subsumption,
% 47.37/6.55                [status(thm)],
% 47.37/6.55                [c_5371,c_42,c_3529]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_10289,plain,
% 47.37/6.55      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(sK1)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,X0_58,k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v3_pre_topc(X1_55,k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_58),u1_struct_0(sK1),X0_55,X1_55),X0_58) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK1)))) != iProver_top
% 47.37/6.55      | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top ),
% 47.37/6.55      inference(renaming,[status(thm)],[c_10288]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_10294,plain,
% 47.37/6.55      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,u1_struct_0(X0_58),k2_struct_0(sK1)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,X0_58,k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v3_pre_topc(X1_55,k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_58),k2_struct_0(sK1),X0_55,X1_55),X0_58) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),k2_struct_0(sK1)))) != iProver_top
% 47.37/6.55      | m1_subset_1(X1_55,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top ),
% 47.37/6.55      inference(light_normalisation,[status(thm)],[c_10289,c_5702]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_10295,plain,
% 47.37/6.55      ( k2_struct_0(sK1) = k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,u1_struct_0(X0_58),k2_struct_0(sK1)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,X0_58,k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v3_pre_topc(X1_55,k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_58),k2_struct_0(sK1),X0_55,X1_55),X0_58) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),k2_struct_0(sK1)))) != iProver_top
% 47.37/6.55      | m1_subset_1(X1_55,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top ),
% 47.37/6.55      inference(demodulation,[status(thm)],[c_10294,c_5705]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_10299,plain,
% 47.37/6.55      ( k2_struct_0(sK1) = k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,u1_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v3_pre_topc(X1_55,k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_55,X1_55),sK1) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 47.37/6.55      | m1_subset_1(X1_55,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(sK1) != iProver_top ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_5702,c_10295]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_10304,plain,
% 47.37/6.55      ( k2_struct_0(sK1) = k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v3_pre_topc(X1_55,k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_55,X1_55),sK1) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 47.37/6.55      | m1_subset_1(X1_55,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(sK1) != iProver_top ),
% 47.37/6.55      inference(light_normalisation,[status(thm)],[c_10299,c_5702]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_10650,plain,
% 47.37/6.55      ( v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | m1_subset_1(X1_55,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 47.37/6.55      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_55,X1_55),sK1) = iProver_top
% 47.37/6.55      | v3_pre_topc(X1_55,k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v1_funct_2(X0_55,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 47.37/6.55      | k2_struct_0(sK1) = k1_xboole_0 ),
% 47.37/6.55      inference(global_propositional_subsumption,
% 47.37/6.55                [status(thm)],
% 47.37/6.55                [c_10304,c_41]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_10651,plain,
% 47.37/6.55      ( k2_struct_0(sK1) = k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v3_pre_topc(X1_55,k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_55,X1_55),sK1) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 47.37/6.55      | m1_subset_1(X1_55,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top ),
% 47.37/6.55      inference(renaming,[status(thm)],[c_10650]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_10656,plain,
% 47.37/6.55      ( k2_struct_0(sK1) = k1_xboole_0
% 47.37/6.55      | v1_funct_2(k6_partfun1(k2_struct_0(sK1)),k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 47.37/6.55      | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v3_pre_topc(sK2,k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v3_pre_topc(sK2,sK1) = iProver_top
% 47.37/6.55      | m1_subset_1(k6_partfun1(k2_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 47.37/6.55      | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 47.37/6.55      | v1_funct_1(k6_partfun1(k2_struct_0(sK1))) != iProver_top ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_5783,c_10651]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_14470,plain,
% 47.37/6.55      ( k7_tmap_1(sK1,sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))) = k6_partfun1(k2_struct_0(sK1))
% 47.37/6.55      | k2_struct_0(sK1) = k1_xboole_0 ),
% 47.37/6.55      inference(global_propositional_subsumption,
% 47.37/6.55                [status(thm)],
% 47.37/6.55                [c_7438,c_35,c_42,c_3445,c_3511,c_3513,c_4451,c_4505,
% 47.37/6.55                 c_5785,c_5899,c_5990,c_6537,c_6538,c_10656]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_14471,plain,
% 47.37/6.55      ( k2_struct_0(sK1) = k1_xboole_0
% 47.37/6.55      | k7_tmap_1(sK1,sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))) = k6_partfun1(k2_struct_0(sK1)) ),
% 47.37/6.55      inference(renaming,[status(thm)],[c_14470]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_11,plain,
% 47.37/6.55      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 47.37/6.55      | v5_pre_topc(X0,X1,X2)
% 47.37/6.55      | v3_pre_topc(sK0(X1,X2,X0),X2)
% 47.37/6.55      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 47.37/6.55      | ~ v1_funct_1(X0)
% 47.37/6.55      | ~ l1_pre_topc(X1)
% 47.37/6.55      | ~ l1_pre_topc(X2)
% 47.37/6.55      | k2_struct_0(X2) = k1_xboole_0 ),
% 47.37/6.55      inference(cnf_transformation,[],[f70]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3390,plain,
% 47.37/6.55      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58))
% 47.37/6.55      | v5_pre_topc(X0_55,X0_58,X1_58)
% 47.37/6.55      | v3_pre_topc(sK0(X0_58,X1_58,X0_55),X1_58)
% 47.37/6.55      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
% 47.37/6.55      | ~ v1_funct_1(X0_55)
% 47.37/6.55      | ~ l1_pre_topc(X0_58)
% 47.37/6.55      | ~ l1_pre_topc(X1_58)
% 47.37/6.55      | k2_struct_0(X1_58) = k1_xboole_0 ),
% 47.37/6.55      inference(subtyping,[status(esa)],[c_11]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_4322,plain,
% 47.37/6.55      ( k2_struct_0(X0_58) = k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,u1_struct_0(X1_58),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,X1_58,X0_58) = iProver_top
% 47.37/6.55      | v3_pre_topc(sK0(X1_58,X0_58,X0_55),X0_58) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X1_58) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top ),
% 47.37/6.55      inference(predicate_to_equality,[status(thm)],[c_3390]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_5361,plain,
% 47.37/6.55      ( k2_struct_0(X0_58) = k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
% 47.37/6.55      | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55),X0_58) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top
% 47.37/6.55      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_5255,c_4322]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_5362,plain,
% 47.37/6.55      ( k2_struct_0(X0_58) = k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,u1_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
% 47.37/6.55      | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55),X0_58) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top
% 47.37/6.55      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 47.37/6.55      inference(light_normalisation,[status(thm)],[c_5361,c_5255]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_6829,plain,
% 47.37/6.55      ( l1_pre_topc(X0_58) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55),X0_58) = iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
% 47.37/6.55      | v1_funct_2(X0_55,u1_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | k2_struct_0(X0_58) = k1_xboole_0 ),
% 47.37/6.55      inference(global_propositional_subsumption,
% 47.37/6.55                [status(thm)],
% 47.37/6.55                [c_5362,c_42,c_3529]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_6830,plain,
% 47.37/6.55      ( k2_struct_0(X0_58) = k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,u1_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
% 47.37/6.55      | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55),X0_58) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top ),
% 47.37/6.55      inference(renaming,[status(thm)],[c_6829]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_6835,plain,
% 47.37/6.55      ( k2_struct_0(X0_58) = k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
% 47.37/6.55      | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55),X0_58) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top ),
% 47.37/6.55      inference(light_normalisation,[status(thm)],[c_6830,c_5702]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_6839,plain,
% 47.37/6.55      ( k2_struct_0(k6_tmap_1(sK1,X0_55)) = k1_xboole_0
% 47.37/6.55      | v1_funct_2(k7_tmap_1(sK1,X0_55),k2_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_55))) != iProver_top
% 47.37/6.55      | v5_pre_topc(k7_tmap_1(sK1,X0_55),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_55)) = iProver_top
% 47.37/6.55      | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_55),k7_tmap_1(sK1,X0_55)),k6_tmap_1(sK1,X0_55)) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 47.37/6.55      | v1_funct_1(k7_tmap_1(sK1,X0_55)) != iProver_top
% 47.37/6.55      | l1_pre_topc(k6_tmap_1(sK1,X0_55)) != iProver_top ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_6103,c_6835]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_5780,plain,
% 47.37/6.55      ( m1_subset_1(X0_55,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 47.37/6.55      | l1_pre_topc(k6_tmap_1(sK1,X0_55)) = iProver_top ),
% 47.37/6.55      inference(demodulation,[status(thm)],[c_5702,c_4348]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_4345,plain,
% 47.37/6.55      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 47.37/6.55      | v1_funct_1(k7_tmap_1(sK1,X0_55)) = iProver_top ),
% 47.37/6.55      inference(predicate_to_equality,[status(thm)],[c_3367]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_5782,plain,
% 47.37/6.55      ( m1_subset_1(X0_55,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 47.37/6.55      | v1_funct_1(k7_tmap_1(sK1,X0_55)) = iProver_top ),
% 47.37/6.55      inference(demodulation,[status(thm)],[c_5702,c_4345]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_17497,plain,
% 47.37/6.55      ( k2_struct_0(k6_tmap_1(sK1,X0_55)) = k1_xboole_0
% 47.37/6.55      | v5_pre_topc(k7_tmap_1(sK1,X0_55),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_55)) = iProver_top
% 47.37/6.55      | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_55),k7_tmap_1(sK1,X0_55)),k6_tmap_1(sK1,X0_55)) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 47.37/6.55      inference(global_propositional_subsumption,
% 47.37/6.55                [status(thm)],
% 47.37/6.55                [c_6839,c_5780,c_5782,c_6098]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_17504,plain,
% 47.37/6.55      ( k2_struct_0(k6_tmap_1(sK1,sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))))) = k1_xboole_0
% 47.37/6.55      | k2_struct_0(sK1) = k1_xboole_0
% 47.37/6.55      | v5_pre_topc(k7_tmap_1(sK1,sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))))) = iProver_top
% 47.37/6.55      | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))),k6_partfun1(k2_struct_0(sK1))),k6_tmap_1(sK1,sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))))) = iProver_top
% 47.37/6.55      | m1_subset_1(sK0(sK1,k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_14471,c_17497]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_17503,plain,
% 47.37/6.55      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 47.37/6.55      | v5_pre_topc(k7_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.55      | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.55      | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_5776,c_17497]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_17505,plain,
% 47.37/6.55      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 47.37/6.55      | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.55      | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.55      | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 47.37/6.55      inference(light_normalisation,[status(thm)],[c_17503,c_5776]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_17506,plain,
% 47.37/6.55      ( k2_struct_0(sK1) = k1_xboole_0
% 47.37/6.55      | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.55      | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.55      | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 47.37/6.55      inference(demodulation,[status(thm)],[c_17505,c_5705]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_18235,plain,
% 47.37/6.55      ( v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.55      | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.55      | k2_struct_0(sK1) = k1_xboole_0 ),
% 47.37/6.55      inference(global_propositional_subsumption,
% 47.37/6.55                [status(thm)],
% 47.37/6.55                [c_17506,c_5785]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_18236,plain,
% 47.37/6.55      ( k2_struct_0(sK1) = k1_xboole_0
% 47.37/6.55      | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.55      | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k6_tmap_1(sK1,sK2)) = iProver_top ),
% 47.37/6.55      inference(renaming,[status(thm)],[c_18235]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_32,negated_conjecture,
% 47.37/6.55      ( v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
% 47.37/6.55      | v3_pre_topc(sK2,sK1) ),
% 47.37/6.55      inference(cnf_transformation,[],[f94]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3383,negated_conjecture,
% 47.37/6.55      ( v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2))
% 47.37/6.55      | v3_pre_topc(sK2,sK1) ),
% 47.37/6.55      inference(subtyping,[status(esa)],[c_32]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_4329,plain,
% 47.37/6.55      ( v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.55      | v3_pre_topc(sK2,sK1) = iProver_top ),
% 47.37/6.55      inference(predicate_to_equality,[status(thm)],[c_3383]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_5564,plain,
% 47.37/6.55      ( v5_pre_topc(k6_partfun1(u1_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.55      | v3_pre_topc(sK2,sK1) = iProver_top ),
% 47.37/6.55      inference(demodulation,[status(thm)],[c_5471,c_4329]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_6286,plain,
% 47.37/6.55      ( v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.55      | v3_pre_topc(sK2,sK1) = iProver_top ),
% 47.37/6.55      inference(light_normalisation,[status(thm)],[c_5564,c_5702]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_5348,plain,
% 47.37/6.55      ( m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top ),
% 47.37/6.55      inference(demodulation,[status(thm)],[c_5255,c_4573]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_5562,plain,
% 47.37/6.55      ( m1_subset_1(k6_partfun1(u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top ),
% 47.37/6.55      inference(demodulation,[status(thm)],[c_5471,c_5348]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_7176,plain,
% 47.37/6.55      ( m1_subset_1(k6_partfun1(k2_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) = iProver_top ),
% 47.37/6.55      inference(light_normalisation,[status(thm)],[c_5562,c_5702]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_9,plain,
% 47.37/6.55      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 47.37/6.55      | v5_pre_topc(X0,X1,X2)
% 47.37/6.55      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0)),X1)
% 47.37/6.55      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 47.37/6.55      | ~ v1_funct_1(X0)
% 47.37/6.55      | ~ l1_pre_topc(X1)
% 47.37/6.55      | ~ l1_pre_topc(X2)
% 47.37/6.55      | k2_struct_0(X2) = k1_xboole_0 ),
% 47.37/6.55      inference(cnf_transformation,[],[f72]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3392,plain,
% 47.37/6.55      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58))
% 47.37/6.55      | v5_pre_topc(X0_55,X0_58,X1_58)
% 47.37/6.55      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_55,sK0(X0_58,X1_58,X0_55)),X0_58)
% 47.37/6.55      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
% 47.37/6.55      | ~ v1_funct_1(X0_55)
% 47.37/6.55      | ~ l1_pre_topc(X0_58)
% 47.37/6.55      | ~ l1_pre_topc(X1_58)
% 47.37/6.55      | k2_struct_0(X1_58) = k1_xboole_0 ),
% 47.37/6.55      inference(subtyping,[status(esa)],[c_9]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_4320,plain,
% 47.37/6.55      ( k2_struct_0(X0_58) = k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,u1_struct_0(X1_58),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,X1_58,X0_58) = iProver_top
% 47.37/6.55      | v3_pre_topc(k8_relset_1(u1_struct_0(X1_58),u1_struct_0(X0_58),X0_55,sK0(X1_58,X0_58,X0_55)),X1_58) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X1_58) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top ),
% 47.37/6.55      inference(predicate_to_equality,[status(thm)],[c_3392]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_5801,plain,
% 47.37/6.55      ( k2_struct_0(X0_58) = k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,u1_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,sK1,X0_58) = iProver_top
% 47.37/6.55      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0_58),X0_55,sK0(sK1,X0_58,X0_55)),sK1) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top
% 47.37/6.55      | l1_pre_topc(sK1) != iProver_top ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_5702,c_4320]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_5808,plain,
% 47.37/6.55      ( k2_struct_0(X0_58) = k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,sK1,X0_58) = iProver_top
% 47.37/6.55      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0_58),X0_55,sK0(sK1,X0_58,X0_55)),sK1) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top
% 47.37/6.55      | l1_pre_topc(sK1) != iProver_top ),
% 47.37/6.55      inference(light_normalisation,[status(thm)],[c_5801,c_5702]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_9704,plain,
% 47.37/6.55      ( l1_pre_topc(X0_58) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0_58),X0_55,sK0(sK1,X0_58,X0_55)),sK1) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,sK1,X0_58) = iProver_top
% 47.37/6.55      | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | k2_struct_0(X0_58) = k1_xboole_0 ),
% 47.37/6.55      inference(global_propositional_subsumption,
% 47.37/6.55                [status(thm)],
% 47.37/6.55                [c_5808,c_41]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_9705,plain,
% 47.37/6.55      ( k2_struct_0(X0_58) = k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,sK1,X0_58) = iProver_top
% 47.37/6.55      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0_58),X0_55,sK0(sK1,X0_58,X0_55)),sK1) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top ),
% 47.37/6.55      inference(renaming,[status(thm)],[c_9704]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_9708,plain,
% 47.37/6.55      ( k2_struct_0(sK1) = k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(sK1)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,sK1,sK1) = iProver_top
% 47.37/6.55      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_55,sK0(sK1,sK1,X0_55)),sK1) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(sK1) != iProver_top ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_5702,c_9705]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_9712,plain,
% 47.37/6.55      ( k2_struct_0(sK1) = k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,sK1,sK1) = iProver_top
% 47.37/6.55      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_55,sK0(sK1,sK1,X0_55)),sK1) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(sK1) != iProver_top ),
% 47.37/6.55      inference(light_normalisation,[status(thm)],[c_9708,c_5702]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_9806,plain,
% 47.37/6.55      ( v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 47.37/6.55      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_55,sK0(sK1,sK1,X0_55)),sK1) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,sK1,sK1) = iProver_top
% 47.37/6.55      | v1_funct_2(X0_55,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 47.37/6.55      | k2_struct_0(sK1) = k1_xboole_0 ),
% 47.37/6.55      inference(global_propositional_subsumption,
% 47.37/6.55                [status(thm)],
% 47.37/6.55                [c_9712,c_41]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_9807,plain,
% 47.37/6.55      ( k2_struct_0(sK1) = k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,sK1,sK1) = iProver_top
% 47.37/6.55      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_55,sK0(sK1,sK1,X0_55)),sK1) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top ),
% 47.37/6.55      inference(renaming,[status(thm)],[c_9806]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_10658,plain,
% 47.37/6.55      ( k2_struct_0(sK1) = k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,sK1,sK1) = iProver_top
% 47.37/6.55      | v3_pre_topc(sK0(sK1,sK1,X0_55),k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 47.37/6.55      | m1_subset_1(sK0(sK1,sK1,X0_55),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_10651,c_9807]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_5803,plain,
% 47.37/6.55      ( k2_struct_0(X0_58) = k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,u1_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,sK1,X0_58) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | m1_subset_1(sK0(sK1,X0_58,X0_55),k1_zfmisc_1(u1_struct_0(X0_58))) = iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top
% 47.37/6.55      | l1_pre_topc(sK1) != iProver_top ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_5702,c_4324]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_5806,plain,
% 47.37/6.55      ( k2_struct_0(X0_58) = k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,sK1,X0_58) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | m1_subset_1(sK0(sK1,X0_58,X0_55),k1_zfmisc_1(u1_struct_0(X0_58))) = iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top
% 47.37/6.55      | l1_pre_topc(sK1) != iProver_top ),
% 47.37/6.55      inference(light_normalisation,[status(thm)],[c_5803,c_5702]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_9589,plain,
% 47.37/6.55      ( l1_pre_topc(X0_58) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | m1_subset_1(sK0(sK1,X0_58,X0_55),k1_zfmisc_1(u1_struct_0(X0_58))) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,sK1,X0_58) = iProver_top
% 47.37/6.55      | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | k2_struct_0(X0_58) = k1_xboole_0 ),
% 47.37/6.55      inference(global_propositional_subsumption,
% 47.37/6.55                [status(thm)],
% 47.37/6.55                [c_5806,c_41]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_9590,plain,
% 47.37/6.55      ( k2_struct_0(X0_58) = k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,sK1,X0_58) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | m1_subset_1(sK0(sK1,X0_58,X0_55),k1_zfmisc_1(u1_struct_0(X0_58))) = iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top ),
% 47.37/6.55      inference(renaming,[status(thm)],[c_9589]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_9594,plain,
% 47.37/6.55      ( k2_struct_0(sK1) = k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(sK1)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,sK1,sK1) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 47.37/6.55      | m1_subset_1(sK0(sK1,sK1,X0_55),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(sK1) != iProver_top ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_5702,c_9590]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_9598,plain,
% 47.37/6.55      ( k2_struct_0(sK1) = k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,sK1,sK1) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 47.37/6.55      | m1_subset_1(sK0(sK1,sK1,X0_55),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(sK1) != iProver_top ),
% 47.37/6.55      inference(light_normalisation,[status(thm)],[c_9594,c_5702]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_9609,plain,
% 47.37/6.55      ( v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | m1_subset_1(sK0(sK1,sK1,X0_55),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,sK1,sK1) = iProver_top
% 47.37/6.55      | v1_funct_2(X0_55,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 47.37/6.55      | k2_struct_0(sK1) = k1_xboole_0 ),
% 47.37/6.55      inference(global_propositional_subsumption,
% 47.37/6.55                [status(thm)],
% 47.37/6.55                [c_9598,c_41]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_9610,plain,
% 47.37/6.55      ( k2_struct_0(sK1) = k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,sK1,sK1) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 47.37/6.55      | m1_subset_1(sK0(sK1,sK1,X0_55),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top ),
% 47.37/6.55      inference(renaming,[status(thm)],[c_9609]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_28047,plain,
% 47.37/6.55      ( m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 47.37/6.55      | v3_pre_topc(sK0(sK1,sK1,X0_55),k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,sK1,sK1) = iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v1_funct_2(X0_55,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 47.37/6.55      | k2_struct_0(sK1) = k1_xboole_0
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top ),
% 47.37/6.55      inference(global_propositional_subsumption,
% 47.37/6.55                [status(thm)],
% 47.37/6.55                [c_10658,c_9610]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_28048,plain,
% 47.37/6.55      ( k2_struct_0(sK1) = k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,sK1,sK1) = iProver_top
% 47.37/6.55      | v3_pre_topc(sK0(sK1,sK1,X0_55),k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top ),
% 47.37/6.55      inference(renaming,[status(thm)],[c_28047]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_28053,plain,
% 47.37/6.55      ( k2_struct_0(sK1) = k1_xboole_0
% 47.37/6.55      | v1_funct_2(k6_partfun1(k2_struct_0(sK1)),k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 47.37/6.55      | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,sK1) = iProver_top
% 47.37/6.55      | v3_pre_topc(sK0(sK1,sK1,k6_partfun1(k2_struct_0(sK1))),k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v1_funct_1(k6_partfun1(k2_struct_0(sK1))) != iProver_top ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_7176,c_28048]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_28058,plain,
% 47.37/6.55      ( v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | k2_struct_0(sK1) = k1_xboole_0 ),
% 47.37/6.55      inference(global_propositional_subsumption,
% 47.37/6.55                [status(thm)],
% 47.37/6.55                [c_28053,c_35,c_42,c_3445,c_3511,c_3513,c_4451,c_4505,
% 47.37/6.55                 c_5785,c_5899,c_5990,c_6537,c_6538,c_10656]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_28059,plain,
% 47.37/6.55      ( k2_struct_0(sK1) = k1_xboole_0
% 47.37/6.55      | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) != iProver_top ),
% 47.37/6.55      inference(renaming,[status(thm)],[c_28058]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_28062,plain,
% 47.37/6.55      ( k2_struct_0(sK1) = k1_xboole_0
% 47.37/6.55      | v3_pre_topc(sK2,sK1) = iProver_top ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_6286,c_28059]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_29,plain,
% 47.37/6.55      ( ~ v3_pre_topc(X0,X1)
% 47.37/6.55      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.37/6.55      | ~ v2_pre_topc(X1)
% 47.37/6.55      | v2_struct_0(X1)
% 47.37/6.55      | ~ l1_pre_topc(X1)
% 47.37/6.55      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,X0) ),
% 47.37/6.55      inference(cnf_transformation,[],[f86]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_504,plain,
% 47.37/6.55      ( ~ v3_pre_topc(X0,X1)
% 47.37/6.55      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.37/6.55      | ~ v2_pre_topc(X1)
% 47.37/6.55      | ~ l1_pre_topc(X1)
% 47.37/6.55      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,X0)
% 47.37/6.55      | sK1 != X1 ),
% 47.37/6.55      inference(resolution_lifted,[status(thm)],[c_29,c_38]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_505,plain,
% 47.37/6.55      ( ~ v3_pre_topc(X0,sK1)
% 47.37/6.55      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.37/6.55      | ~ v2_pre_topc(sK1)
% 47.37/6.55      | ~ l1_pre_topc(sK1)
% 47.37/6.55      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,X0) ),
% 47.37/6.55      inference(unflattening,[status(thm)],[c_504]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_509,plain,
% 47.37/6.55      ( ~ v3_pre_topc(X0,sK1)
% 47.37/6.55      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.37/6.55      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,X0) ),
% 47.37/6.55      inference(global_propositional_subsumption,
% 47.37/6.55                [status(thm)],
% 47.37/6.55                [c_505,c_37,c_36]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3372,plain,
% 47.37/6.55      ( ~ v3_pre_topc(X0_55,sK1)
% 47.37/6.55      | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.37/6.55      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,X0_55) ),
% 47.37/6.55      inference(subtyping,[status(esa)],[c_509]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_4340,plain,
% 47.37/6.55      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,X0_55)
% 47.37/6.55      | v3_pre_topc(X0_55,sK1) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 47.37/6.55      inference(predicate_to_equality,[status(thm)],[c_3372]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_6169,plain,
% 47.37/6.55      ( g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,X0_55)
% 47.37/6.55      | v3_pre_topc(X0_55,sK1) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 47.37/6.55      inference(light_normalisation,[status(thm)],[c_4340,c_5702]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_6173,plain,
% 47.37/6.55      ( g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,sK2)
% 47.37/6.55      | v3_pre_topc(sK2,sK1) != iProver_top ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_5785,c_6169]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_28171,plain,
% 47.37/6.55      ( g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,sK2)
% 47.37/6.55      | k2_struct_0(sK1) = k1_xboole_0 ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_28062,c_6173]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_6,plain,
% 47.37/6.55      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 47.37/6.55      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 47.37/6.55      | v5_pre_topc(X0,X1,X2)
% 47.37/6.55      | ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 47.37/6.55      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 47.37/6.55      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 47.37/6.55      | ~ v2_pre_topc(X2)
% 47.37/6.55      | ~ v2_pre_topc(X1)
% 47.37/6.55      | ~ v1_funct_1(X0)
% 47.37/6.55      | ~ l1_pre_topc(X1)
% 47.37/6.55      | ~ l1_pre_topc(X2) ),
% 47.37/6.55      inference(cnf_transformation,[],[f97]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3395,plain,
% 47.37/6.55      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58))
% 47.37/6.55      | ~ v1_funct_2(X0_55,u1_struct_0(g1_pre_topc(u1_struct_0(X0_58),u1_pre_topc(X0_58))),u1_struct_0(X1_58))
% 47.37/6.55      | v5_pre_topc(X0_55,X0_58,X1_58)
% 47.37/6.55      | ~ v5_pre_topc(X0_55,g1_pre_topc(u1_struct_0(X0_58),u1_pre_topc(X0_58)),X1_58)
% 47.37/6.55      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
% 47.37/6.55      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0_58),u1_pre_topc(X0_58))),u1_struct_0(X1_58))))
% 47.37/6.55      | ~ v2_pre_topc(X1_58)
% 47.37/6.55      | ~ v2_pre_topc(X0_58)
% 47.37/6.55      | ~ v1_funct_1(X0_55)
% 47.37/6.55      | ~ l1_pre_topc(X0_58)
% 47.37/6.55      | ~ l1_pre_topc(X1_58) ),
% 47.37/6.55      inference(subtyping,[status(esa)],[c_6]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_4317,plain,
% 47.37/6.55      ( v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
% 47.37/6.55      | v1_funct_2(X0_55,u1_struct_0(g1_pre_topc(u1_struct_0(X0_58),u1_pre_topc(X0_58))),u1_struct_0(X1_58)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,X0_58,X1_58) = iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,g1_pre_topc(u1_struct_0(X0_58),u1_pre_topc(X0_58)),X1_58) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0_58),u1_pre_topc(X0_58))),u1_struct_0(X1_58)))) != iProver_top
% 47.37/6.55      | v2_pre_topc(X0_58) != iProver_top
% 47.37/6.55      | v2_pre_topc(X1_58) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top
% 47.37/6.55      | l1_pre_topc(X1_58) != iProver_top ),
% 47.37/6.55      inference(predicate_to_equality,[status(thm)],[c_3395]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_5796,plain,
% 47.37/6.55      ( v1_funct_2(X0_55,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v1_funct_2(X0_55,u1_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0_58) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,sK1,X0_58) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | v2_pre_topc(X0_58) != iProver_top
% 47.37/6.55      | v2_pre_topc(sK1) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top
% 47.37/6.55      | l1_pre_topc(sK1) != iProver_top ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_5702,c_4317]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_5813,plain,
% 47.37/6.55      ( v1_funct_2(X0_55,u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X0_58) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,sK1,X0_58) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | v2_pre_topc(X0_58) != iProver_top
% 47.37/6.55      | v2_pre_topc(sK1) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top
% 47.37/6.55      | l1_pre_topc(sK1) != iProver_top ),
% 47.37/6.55      inference(light_normalisation,[status(thm)],[c_5796,c_5702]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_40,plain,
% 47.37/6.55      ( v2_pre_topc(sK1) = iProver_top ),
% 47.37/6.55      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_8135,plain,
% 47.37/6.55      ( l1_pre_topc(X0_58) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | v1_funct_2(X0_55,u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X0_58) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,sK1,X0_58) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | v2_pre_topc(X0_58) != iProver_top ),
% 47.37/6.55      inference(global_propositional_subsumption,
% 47.37/6.55                [status(thm)],
% 47.37/6.55                [c_5813,c_40,c_41]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_8136,plain,
% 47.37/6.55      ( v1_funct_2(X0_55,u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X0_58) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,sK1,X0_58) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | v2_pre_topc(X0_58) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top ),
% 47.37/6.55      inference(renaming,[status(thm)],[c_8135]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_28179,plain,
% 47.37/6.55      ( k2_struct_0(sK1) = k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X0_58) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,sK1,X0_58) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | v2_pre_topc(X0_58) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_28171,c_8136]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_28185,plain,
% 47.37/6.55      ( k2_struct_0(sK1) = k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X0_58) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,sK1,X0_58) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | v2_pre_topc(X0_58) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top ),
% 47.37/6.55      inference(light_normalisation,[status(thm)],[c_28179,c_5778]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_33191,plain,
% 47.37/6.55      ( k2_struct_0(sK1) = k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X0_58) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,sK1,X0_58) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | v2_pre_topc(X0_58) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_28171,c_28185]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_33198,plain,
% 47.37/6.55      ( k2_struct_0(sK1) = k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X0_58) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,sK1,X0_58) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | v2_pre_topc(X0_58) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top ),
% 47.37/6.55      inference(light_normalisation,[status(thm)],[c_33191,c_5778]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_33474,plain,
% 47.37/6.55      ( k2_struct_0(sK1) = k1_xboole_0
% 47.37/6.55      | v1_funct_2(k7_tmap_1(sK1,X0_55),k2_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_55))) != iProver_top
% 47.37/6.55      | v5_pre_topc(k7_tmap_1(sK1,X0_55),g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),k6_tmap_1(sK1,X0_55)) != iProver_top
% 47.37/6.55      | v5_pre_topc(k7_tmap_1(sK1,X0_55),sK1,k6_tmap_1(sK1,X0_55)) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 47.37/6.55      | v2_pre_topc(k6_tmap_1(sK1,X0_55)) != iProver_top
% 47.37/6.55      | v1_funct_1(k7_tmap_1(sK1,X0_55)) != iProver_top
% 47.37/6.55      | l1_pre_topc(k6_tmap_1(sK1,X0_55)) != iProver_top ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_6103,c_33198]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_18,plain,
% 47.37/6.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.37/6.55      | ~ v2_pre_topc(X1)
% 47.37/6.55      | v2_pre_topc(k6_tmap_1(X1,X0))
% 47.37/6.55      | v2_struct_0(X1)
% 47.37/6.55      | ~ l1_pre_topc(X1) ),
% 47.37/6.55      inference(cnf_transformation,[],[f75]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_639,plain,
% 47.37/6.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.37/6.55      | ~ v2_pre_topc(X1)
% 47.37/6.55      | v2_pre_topc(k6_tmap_1(X1,X0))
% 47.37/6.55      | ~ l1_pre_topc(X1)
% 47.37/6.55      | sK1 != X1 ),
% 47.37/6.55      inference(resolution_lifted,[status(thm)],[c_18,c_38]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_640,plain,
% 47.37/6.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.37/6.55      | v2_pre_topc(k6_tmap_1(sK1,X0))
% 47.37/6.55      | ~ v2_pre_topc(sK1)
% 47.37/6.55      | ~ l1_pre_topc(sK1) ),
% 47.37/6.55      inference(unflattening,[status(thm)],[c_639]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_644,plain,
% 47.37/6.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.37/6.55      | v2_pre_topc(k6_tmap_1(sK1,X0)) ),
% 47.37/6.55      inference(global_propositional_subsumption,
% 47.37/6.55                [status(thm)],
% 47.37/6.55                [c_640,c_37,c_36]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3365,plain,
% 47.37/6.55      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.37/6.55      | v2_pre_topc(k6_tmap_1(sK1,X0_55)) ),
% 47.37/6.55      inference(subtyping,[status(esa)],[c_644]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_4347,plain,
% 47.37/6.55      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 47.37/6.55      | v2_pre_topc(k6_tmap_1(sK1,X0_55)) = iProver_top ),
% 47.37/6.55      inference(predicate_to_equality,[status(thm)],[c_3365]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_5781,plain,
% 47.37/6.55      ( m1_subset_1(X0_55,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 47.37/6.55      | v2_pre_topc(k6_tmap_1(sK1,X0_55)) = iProver_top ),
% 47.37/6.55      inference(demodulation,[status(thm)],[c_5702,c_4347]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_34073,plain,
% 47.37/6.55      ( m1_subset_1(X0_55,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 47.37/6.55      | v5_pre_topc(k7_tmap_1(sK1,X0_55),sK1,k6_tmap_1(sK1,X0_55)) = iProver_top
% 47.37/6.55      | v5_pre_topc(k7_tmap_1(sK1,X0_55),g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),k6_tmap_1(sK1,X0_55)) != iProver_top
% 47.37/6.55      | k2_struct_0(sK1) = k1_xboole_0 ),
% 47.37/6.55      inference(global_propositional_subsumption,
% 47.37/6.55                [status(thm)],
% 47.37/6.55                [c_33474,c_5780,c_5781,c_5782,c_6098]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_34074,plain,
% 47.37/6.55      ( k2_struct_0(sK1) = k1_xboole_0
% 47.37/6.55      | v5_pre_topc(k7_tmap_1(sK1,X0_55),g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),k6_tmap_1(sK1,X0_55)) != iProver_top
% 47.37/6.55      | v5_pre_topc(k7_tmap_1(sK1,X0_55),sK1,k6_tmap_1(sK1,X0_55)) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 47.37/6.55      inference(renaming,[status(thm)],[c_34073]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_34081,plain,
% 47.37/6.55      ( k2_struct_0(sK1) = k1_xboole_0
% 47.37/6.55      | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.55      | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_5776,c_34074]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_34084,plain,
% 47.37/6.55      ( k2_struct_0(sK1) = k1_xboole_0
% 47.37/6.55      | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.55      | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 47.37/6.55      inference(light_normalisation,[status(thm)],[c_34081,c_5776]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_34092,plain,
% 47.37/6.55      ( k2_struct_0(sK1) = k1_xboole_0
% 47.37/6.55      | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),k6_tmap_1(sK1,sK2)) != iProver_top ),
% 47.37/6.55      inference(global_propositional_subsumption,
% 47.37/6.55                [status(thm)],
% 47.37/6.55                [c_34084,c_5785,c_28059]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_34097,plain,
% 47.37/6.55      ( k2_struct_0(sK1) = k1_xboole_0
% 47.37/6.55      | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) != iProver_top ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_28171,c_34092]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_5360,plain,
% 47.37/6.55      ( k2_struct_0(X0_58) = k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55),k1_zfmisc_1(u1_struct_0(X0_58))) = iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top
% 47.37/6.55      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_5255,c_4324]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_5363,plain,
% 47.37/6.55      ( k2_struct_0(X0_58) = k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,u1_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55),k1_zfmisc_1(u1_struct_0(X0_58))) = iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top
% 47.37/6.55      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 47.37/6.55      inference(light_normalisation,[status(thm)],[c_5360,c_5255]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_7623,plain,
% 47.37/6.55      ( l1_pre_topc(X0_58) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55),k1_zfmisc_1(u1_struct_0(X0_58))) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
% 47.37/6.55      | v1_funct_2(X0_55,u1_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | k2_struct_0(X0_58) = k1_xboole_0 ),
% 47.37/6.55      inference(global_propositional_subsumption,
% 47.37/6.55                [status(thm)],
% 47.37/6.55                [c_5363,c_42,c_3529]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_7624,plain,
% 47.37/6.55      ( k2_struct_0(X0_58) = k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,u1_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55),k1_zfmisc_1(u1_struct_0(X0_58))) = iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top ),
% 47.37/6.55      inference(renaming,[status(thm)],[c_7623]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_7629,plain,
% 47.37/6.55      ( k2_struct_0(X0_58) = k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55),k1_zfmisc_1(u1_struct_0(X0_58))) = iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top ),
% 47.37/6.55      inference(light_normalisation,[status(thm)],[c_7624,c_5702]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_7635,plain,
% 47.37/6.55      ( k2_struct_0(X0_58) = k1_xboole_0
% 47.37/6.55      | k8_relset_1(u1_struct_0(X0_58),u1_struct_0(X0_58),k6_partfun1(u1_struct_0(X0_58)),sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55)) = sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55)
% 47.37/6.55      | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_7629,c_4316]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_7649,plain,
% 47.37/6.55      ( k2_struct_0(k6_tmap_1(sK1,X0_55)) = k1_xboole_0
% 47.37/6.55      | k8_relset_1(u1_struct_0(k6_tmap_1(sK1,X0_55)),u1_struct_0(k6_tmap_1(sK1,X0_55)),k6_partfun1(u1_struct_0(k6_tmap_1(sK1,X0_55))),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_55),k7_tmap_1(sK1,X0_55))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_55),k7_tmap_1(sK1,X0_55))
% 47.37/6.55      | v1_funct_2(k7_tmap_1(sK1,X0_55),k2_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,X0_55))) != iProver_top
% 47.37/6.55      | v5_pre_topc(k7_tmap_1(sK1,X0_55),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_55)) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 47.37/6.55      | v1_funct_1(k7_tmap_1(sK1,X0_55)) != iProver_top
% 47.37/6.55      | l1_pre_topc(k6_tmap_1(sK1,X0_55)) != iProver_top ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_6103,c_7635]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_12459,plain,
% 47.37/6.55      ( k8_relset_1(u1_struct_0(k6_tmap_1(sK1,X0_55)),u1_struct_0(k6_tmap_1(sK1,X0_55)),k6_partfun1(u1_struct_0(k6_tmap_1(sK1,X0_55))),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_55),k7_tmap_1(sK1,X0_55))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_55),k7_tmap_1(sK1,X0_55))
% 47.37/6.55      | k2_struct_0(k6_tmap_1(sK1,X0_55)) = k1_xboole_0
% 47.37/6.55      | v5_pre_topc(k7_tmap_1(sK1,X0_55),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_55)) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 47.37/6.55      inference(global_propositional_subsumption,
% 47.37/6.55                [status(thm)],
% 47.37/6.55                [c_7649,c_5780,c_5782,c_6098]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_12460,plain,
% 47.37/6.55      ( k2_struct_0(k6_tmap_1(sK1,X0_55)) = k1_xboole_0
% 47.37/6.55      | k8_relset_1(u1_struct_0(k6_tmap_1(sK1,X0_55)),u1_struct_0(k6_tmap_1(sK1,X0_55)),k6_partfun1(u1_struct_0(k6_tmap_1(sK1,X0_55))),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_55),k7_tmap_1(sK1,X0_55))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_55),k7_tmap_1(sK1,X0_55))
% 47.37/6.55      | v5_pre_topc(k7_tmap_1(sK1,X0_55),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_55)) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 47.37/6.55      inference(renaming,[status(thm)],[c_12459]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_12465,plain,
% 47.37/6.55      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 47.37/6.55      | k8_relset_1(u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(k6_tmap_1(sK1,sK2)),k6_partfun1(u1_struct_0(k6_tmap_1(sK1,sK2))),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2))
% 47.37/6.55      | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.55      | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_5776,c_12460]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_12466,plain,
% 47.37/6.55      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 47.37/6.55      | k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),k6_partfun1(k2_struct_0(sK1)),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))
% 47.37/6.55      | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.55      | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 47.37/6.55      inference(light_normalisation,
% 47.37/6.55                [status(thm)],
% 47.37/6.55                [c_12465,c_5776,c_5778]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_0,plain,
% 47.37/6.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 47.37/6.55      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 47.37/6.55      inference(cnf_transformation,[],[f58]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3397,plain,
% 47.37/6.55      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 47.37/6.55      | k8_relset_1(X0_57,X1_57,X0_55,X1_55) = k10_relat_1(X0_55,X1_55) ),
% 47.37/6.55      inference(subtyping,[status(esa)],[c_0]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_4315,plain,
% 47.37/6.55      ( k8_relset_1(X0_57,X1_57,X0_55,X1_55) = k10_relat_1(X0_55,X1_55)
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top ),
% 47.37/6.55      inference(predicate_to_equality,[status(thm)],[c_3397]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_4624,plain,
% 47.37/6.55      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)),k7_tmap_1(sK1,sK2),X0_55) = k10_relat_1(k7_tmap_1(sK1,sK2),X0_55) ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_4573,c_4315]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_5987,plain,
% 47.37/6.55      ( k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),k6_partfun1(k2_struct_0(sK1)),X0_55) = k10_relat_1(k6_partfun1(k2_struct_0(sK1)),X0_55) ),
% 47.37/6.55      inference(light_normalisation,
% 47.37/6.55                [status(thm)],
% 47.37/6.55                [c_4624,c_4624,c_5702,c_5776,c_5778]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_12467,plain,
% 47.37/6.55      ( k2_struct_0(sK1) = k1_xboole_0
% 47.37/6.55      | k10_relat_1(k6_partfun1(k2_struct_0(sK1)),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))
% 47.37/6.55      | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.55      | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 47.37/6.55      inference(demodulation,[status(thm)],[c_12466,c_5705,c_5987]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_16483,plain,
% 47.37/6.55      ( v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.55      | k10_relat_1(k6_partfun1(k2_struct_0(sK1)),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))
% 47.37/6.55      | k2_struct_0(sK1) = k1_xboole_0 ),
% 47.37/6.55      inference(global_propositional_subsumption,
% 47.37/6.55                [status(thm)],
% 47.37/6.55                [c_12467,c_5785]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_16484,plain,
% 47.37/6.55      ( k2_struct_0(sK1) = k1_xboole_0
% 47.37/6.55      | k10_relat_1(k6_partfun1(k2_struct_0(sK1)),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))
% 47.37/6.55      | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top ),
% 47.37/6.55      inference(renaming,[status(thm)],[c_16483]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_59499,plain,
% 47.37/6.55      ( k2_struct_0(sK1) = k1_xboole_0
% 47.37/6.55      | k10_relat_1(k6_partfun1(k2_struct_0(sK1)),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))) ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_16484,c_34097]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_5358,plain,
% 47.37/6.55      ( k2_struct_0(X0_58) = k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
% 47.37/6.55      | v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0_58),X0_55,sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55)),k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top
% 47.37/6.55      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_5255,c_4320]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_5365,plain,
% 47.37/6.55      ( k2_struct_0(X0_58) = k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,u1_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
% 47.37/6.55      | v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0_58),X0_55,sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55)),k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top
% 47.37/6.55      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 47.37/6.55      inference(light_normalisation,[status(thm)],[c_5358,c_5255]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_8511,plain,
% 47.37/6.55      ( l1_pre_topc(X0_58) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0_58),X0_55,sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55)),k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
% 47.37/6.55      | v1_funct_2(X0_55,u1_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | k2_struct_0(X0_58) = k1_xboole_0 ),
% 47.37/6.55      inference(global_propositional_subsumption,
% 47.37/6.55                [status(thm)],
% 47.37/6.55                [c_5365,c_42,c_3529]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_8512,plain,
% 47.37/6.55      ( k2_struct_0(X0_58) = k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,u1_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
% 47.37/6.55      | v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0_58),X0_55,sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55)),k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top ),
% 47.37/6.55      inference(renaming,[status(thm)],[c_8511]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_8517,plain,
% 47.37/6.55      ( k2_struct_0(X0_58) = k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
% 47.37/6.55      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0_58),X0_55,sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55)),k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top ),
% 47.37/6.55      inference(light_normalisation,[status(thm)],[c_8512,c_5702]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_8522,plain,
% 47.37/6.55      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.55      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_55,sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_55)),k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_5778,c_8517]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_8523,plain,
% 47.37/6.55      ( k2_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.55      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_55,sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_55)),k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 47.37/6.55      inference(light_normalisation,[status(thm)],[c_8522,c_5778]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_8524,plain,
% 47.37/6.55      ( k2_struct_0(sK1) = k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.55      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_55,sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_55)),k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 47.37/6.55      inference(demodulation,[status(thm)],[c_8523,c_5705]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_23462,plain,
% 47.37/6.55      ( v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 47.37/6.55      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_55,sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_55)),k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.55      | v1_funct_2(X0_55,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 47.37/6.55      | k2_struct_0(sK1) = k1_xboole_0 ),
% 47.37/6.55      inference(global_propositional_subsumption,
% 47.37/6.55                [status(thm)],
% 47.37/6.55                [c_8524,c_42,c_3529]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_23463,plain,
% 47.37/6.55      ( k2_struct_0(sK1) = k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.55      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0_55,sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_55)),k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top ),
% 47.37/6.55      inference(renaming,[status(thm)],[c_23462]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_23469,plain,
% 47.37/6.55      ( k2_struct_0(sK1) = k1_xboole_0
% 47.37/6.55      | v1_funct_2(k6_partfun1(k2_struct_0(sK1)),k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 47.37/6.55      | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.55      | v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK1)),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))),k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | m1_subset_1(k6_partfun1(k2_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 47.37/6.55      | v1_funct_1(k6_partfun1(k2_struct_0(sK1))) != iProver_top ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_5987,c_23463]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_29663,plain,
% 47.37/6.55      ( k2_struct_0(sK1) = k1_xboole_0
% 47.37/6.55      | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.55      | v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK1)),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1)))),k6_tmap_1(sK1,sK2)) != iProver_top ),
% 47.37/6.55      inference(global_propositional_subsumption,
% 47.37/6.55                [status(thm)],
% 47.37/6.55                [c_23469,c_5785,c_5899,c_6537,c_6538]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_89212,plain,
% 47.37/6.55      ( k2_struct_0(sK1) = k1_xboole_0
% 47.37/6.55      | v5_pre_topc(k6_partfun1(k2_struct_0(sK1)),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.55      | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k2_struct_0(sK1))),k6_tmap_1(sK1,sK2)) != iProver_top ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_59499,c_29663]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_89489,plain,
% 47.37/6.55      ( k2_struct_0(sK1) = k1_xboole_0 ),
% 47.37/6.55      inference(global_propositional_subsumption,
% 47.37/6.55                [status(thm)],
% 47.37/6.55                [c_17504,c_18236,c_34097,c_89212]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_10,plain,
% 47.37/6.55      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 47.37/6.55      | v5_pre_topc(X0,X1,X2)
% 47.37/6.55      | v3_pre_topc(sK0(X1,X2,X0),X2)
% 47.37/6.55      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 47.37/6.55      | ~ v1_funct_1(X0)
% 47.37/6.55      | ~ l1_pre_topc(X1)
% 47.37/6.55      | ~ l1_pre_topc(X2)
% 47.37/6.55      | k2_struct_0(X1) != k1_xboole_0 ),
% 47.37/6.55      inference(cnf_transformation,[],[f71]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3391,plain,
% 47.37/6.55      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58))
% 47.37/6.55      | v5_pre_topc(X0_55,X0_58,X1_58)
% 47.37/6.55      | v3_pre_topc(sK0(X0_58,X1_58,X0_55),X1_58)
% 47.37/6.55      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
% 47.37/6.55      | ~ v1_funct_1(X0_55)
% 47.37/6.55      | ~ l1_pre_topc(X0_58)
% 47.37/6.55      | ~ l1_pre_topc(X1_58)
% 47.37/6.55      | k2_struct_0(X0_58) != k1_xboole_0 ),
% 47.37/6.55      inference(subtyping,[status(esa)],[c_10]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_4321,plain,
% 47.37/6.55      ( k2_struct_0(X0_58) != k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,X0_58,X1_58) = iProver_top
% 47.37/6.55      | v3_pre_topc(sK0(X0_58,X1_58,X0_55),X1_58) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top
% 47.37/6.55      | l1_pre_topc(X1_58) != iProver_top ),
% 47.37/6.55      inference(predicate_to_equality,[status(thm)],[c_3391]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_6518,plain,
% 47.37/6.55      ( k2_struct_0(sK1) != k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
% 47.37/6.55      | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55),X0_58) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top
% 47.37/6.55      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_5705,c_4321]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_6519,plain,
% 47.37/6.55      ( k2_struct_0(sK1) != k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
% 47.37/6.55      | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55),X0_58) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top
% 47.37/6.55      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 47.37/6.55      inference(light_normalisation,[status(thm)],[c_6518,c_5778]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_10963,plain,
% 47.37/6.55      ( l1_pre_topc(X0_58) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55),X0_58) = iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
% 47.37/6.55      | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | k2_struct_0(sK1) != k1_xboole_0 ),
% 47.37/6.55      inference(global_propositional_subsumption,
% 47.37/6.55                [status(thm)],
% 47.37/6.55                [c_6519,c_42,c_3529]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_10964,plain,
% 47.37/6.55      ( k2_struct_0(sK1) != k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
% 47.37/6.55      | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55),X0_58) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top ),
% 47.37/6.55      inference(renaming,[status(thm)],[c_10963]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_89982,plain,
% 47.37/6.55      ( k1_xboole_0 != k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,k1_xboole_0,u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
% 47.37/6.55      | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55),X0_58) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top ),
% 47.37/6.55      inference(demodulation,[status(thm)],[c_89489,c_10964]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_90040,plain,
% 47.37/6.55      ( v1_funct_2(X0_55,k1_xboole_0,u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
% 47.37/6.55      | v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55),X0_58) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top ),
% 47.37/6.55      inference(equality_resolution_simp,[status(thm)],[c_89982]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_90024,plain,
% 47.37/6.55      ( k7_tmap_1(sK1,sK2) = k6_partfun1(k1_xboole_0) ),
% 47.37/6.55      inference(demodulation,[status(thm)],[c_89489,c_5776]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_90032,plain,
% 47.37/6.55      ( m1_subset_1(X0_55,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 47.37/6.55      | m1_subset_1(k7_tmap_1(sK1,X0_55),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,X0_55))))) = iProver_top ),
% 47.37/6.55      inference(demodulation,[status(thm)],[c_89489,c_6103]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_12,plain,
% 47.37/6.55      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 47.37/6.55      | v5_pre_topc(X0,X1,X2)
% 47.37/6.55      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 47.37/6.55      | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
% 47.37/6.55      | ~ v1_funct_1(X0)
% 47.37/6.55      | ~ l1_pre_topc(X1)
% 47.37/6.55      | ~ l1_pre_topc(X2)
% 47.37/6.55      | k2_struct_0(X1) != k1_xboole_0 ),
% 47.37/6.55      inference(cnf_transformation,[],[f69]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3389,plain,
% 47.37/6.55      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58))
% 47.37/6.55      | v5_pre_topc(X0_55,X0_58,X1_58)
% 47.37/6.55      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
% 47.37/6.55      | m1_subset_1(sK0(X0_58,X1_58,X0_55),k1_zfmisc_1(u1_struct_0(X1_58)))
% 47.37/6.55      | ~ v1_funct_1(X0_55)
% 47.37/6.55      | ~ l1_pre_topc(X0_58)
% 47.37/6.55      | ~ l1_pre_topc(X1_58)
% 47.37/6.55      | k2_struct_0(X0_58) != k1_xboole_0 ),
% 47.37/6.55      inference(subtyping,[status(esa)],[c_12]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_4323,plain,
% 47.37/6.55      ( k2_struct_0(X0_58) != k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,X0_58,X1_58) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
% 47.37/6.55      | m1_subset_1(sK0(X0_58,X1_58,X0_55),k1_zfmisc_1(u1_struct_0(X1_58))) = iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top
% 47.37/6.55      | l1_pre_topc(X1_58) != iProver_top ),
% 47.37/6.55      inference(predicate_to_equality,[status(thm)],[c_3389]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_6517,plain,
% 47.37/6.55      ( k2_struct_0(sK1) != k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55),k1_zfmisc_1(u1_struct_0(X0_58))) = iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top
% 47.37/6.55      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_5705,c_4323]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_6520,plain,
% 47.37/6.55      ( k2_struct_0(sK1) != k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55),k1_zfmisc_1(u1_struct_0(X0_58))) = iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top
% 47.37/6.55      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 47.37/6.55      inference(light_normalisation,[status(thm)],[c_6517,c_5778]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_11153,plain,
% 47.37/6.55      ( l1_pre_topc(X0_58) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55),k1_zfmisc_1(u1_struct_0(X0_58))) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
% 47.37/6.55      | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | k2_struct_0(sK1) != k1_xboole_0 ),
% 47.37/6.55      inference(global_propositional_subsumption,
% 47.37/6.55                [status(thm)],
% 47.37/6.55                [c_6520,c_42,c_3529]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_11154,plain,
% 47.37/6.55      ( k2_struct_0(sK1) != k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55),k1_zfmisc_1(u1_struct_0(X0_58))) = iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top ),
% 47.37/6.55      inference(renaming,[status(thm)],[c_11153]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_89981,plain,
% 47.37/6.55      ( k1_xboole_0 != k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,k1_xboole_0,u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55),k1_zfmisc_1(u1_struct_0(X0_58))) = iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top ),
% 47.37/6.55      inference(demodulation,[status(thm)],[c_89489,c_11154]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_90041,plain,
% 47.37/6.55      ( v1_funct_2(X0_55,k1_xboole_0,u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | m1_subset_1(sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55),k1_zfmisc_1(u1_struct_0(X0_58))) = iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top ),
% 47.37/6.55      inference(equality_resolution_simp,[status(thm)],[c_89981]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_126577,plain,
% 47.37/6.55      ( k8_relset_1(u1_struct_0(X0_58),u1_struct_0(X0_58),k6_partfun1(u1_struct_0(X0_58)),sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55)) = sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55)
% 47.37/6.55      | v1_funct_2(X0_55,k1_xboole_0,u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_90041,c_4316]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_127525,plain,
% 47.37/6.55      ( k8_relset_1(u1_struct_0(k6_tmap_1(sK1,X0_55)),u1_struct_0(k6_tmap_1(sK1,X0_55)),k6_partfun1(u1_struct_0(k6_tmap_1(sK1,X0_55))),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_55),k7_tmap_1(sK1,X0_55))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_55),k7_tmap_1(sK1,X0_55))
% 47.37/6.55      | v1_funct_2(k7_tmap_1(sK1,X0_55),k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,X0_55))) != iProver_top
% 47.37/6.55      | v5_pre_topc(k7_tmap_1(sK1,X0_55),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_55)) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 47.37/6.55      | v1_funct_1(k7_tmap_1(sK1,X0_55)) != iProver_top
% 47.37/6.55      | l1_pre_topc(k6_tmap_1(sK1,X0_55)) != iProver_top ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_90032,c_126577]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_90012,plain,
% 47.37/6.55      ( m1_subset_1(X0_55,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 47.37/6.55      | v1_funct_1(k7_tmap_1(sK1,X0_55)) = iProver_top ),
% 47.37/6.55      inference(demodulation,[status(thm)],[c_89489,c_5782]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_90014,plain,
% 47.37/6.55      ( m1_subset_1(X0_55,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 47.37/6.55      | l1_pre_topc(k6_tmap_1(sK1,X0_55)) = iProver_top ),
% 47.37/6.55      inference(demodulation,[status(thm)],[c_89489,c_5780]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_90033,plain,
% 47.37/6.55      ( v1_funct_2(k7_tmap_1(sK1,X0_55),k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,X0_55))) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 47.37/6.55      inference(demodulation,[status(thm)],[c_89489,c_6098]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_128142,plain,
% 47.37/6.55      ( k8_relset_1(u1_struct_0(k6_tmap_1(sK1,X0_55)),u1_struct_0(k6_tmap_1(sK1,X0_55)),k6_partfun1(u1_struct_0(k6_tmap_1(sK1,X0_55))),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_55),k7_tmap_1(sK1,X0_55))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_55),k7_tmap_1(sK1,X0_55))
% 47.37/6.55      | v5_pre_topc(k7_tmap_1(sK1,X0_55),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_55)) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 47.37/6.55      inference(global_propositional_subsumption,
% 47.37/6.55                [status(thm)],
% 47.37/6.55                [c_127525,c_90012,c_90014,c_90033]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_128148,plain,
% 47.37/6.55      ( k8_relset_1(u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(k6_tmap_1(sK1,sK2)),k6_partfun1(u1_struct_0(k6_tmap_1(sK1,sK2))),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2))
% 47.37/6.55      | v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.55      | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_90024,c_128142]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_90023,plain,
% 47.37/6.55      ( u1_struct_0(k6_tmap_1(sK1,sK2)) = k1_xboole_0 ),
% 47.37/6.55      inference(demodulation,[status(thm)],[c_89489,c_5778]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_128162,plain,
% 47.37/6.55      ( k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k1_xboole_0))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k1_xboole_0))
% 47.37/6.55      | v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.55      | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 47.37/6.55      inference(light_normalisation,
% 47.37/6.55                [status(thm)],
% 47.37/6.55                [c_128148,c_90023,c_90024]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_90035,plain,
% 47.37/6.55      ( k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),X0_55) = k10_relat_1(k6_partfun1(k1_xboole_0),X0_55) ),
% 47.37/6.55      inference(demodulation,[status(thm)],[c_89489,c_5987]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_128163,plain,
% 47.37/6.55      ( k10_relat_1(k6_partfun1(k1_xboole_0),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k1_xboole_0))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k1_xboole_0))
% 47.37/6.55      | v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.55      | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 47.37/6.55      inference(demodulation,[status(thm)],[c_128162,c_90035]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3401,plain,( X0_57 = X0_57 ),theory(equality) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3447,plain,
% 47.37/6.55      ( k1_xboole_0 = k1_xboole_0 ),
% 47.37/6.55      inference(instantiation,[status(thm)],[c_3401]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3495,plain,
% 47.37/6.55      ( ~ l1_pre_topc(sK1) | u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 47.37/6.55      inference(instantiation,[status(thm)],[c_3377]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3531,plain,
% 47.37/6.55      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.37/6.55      | k7_tmap_1(sK1,sK2) = k6_partfun1(u1_struct_0(sK1)) ),
% 47.37/6.55      inference(instantiation,[status(thm)],[c_3363]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_4469,plain,
% 47.37/6.55      ( m1_subset_1(X0_55,X0_56)
% 47.37/6.55      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.37/6.55      | X0_56 != k1_zfmisc_1(u1_struct_0(sK1))
% 47.37/6.55      | X0_55 != sK2 ),
% 47.37/6.55      inference(instantiation,[status(thm)],[c_3411]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_4523,plain,
% 47.37/6.55      ( m1_subset_1(X0_55,k1_zfmisc_1(X0_57))
% 47.37/6.55      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.37/6.55      | k1_zfmisc_1(X0_57) != k1_zfmisc_1(u1_struct_0(sK1))
% 47.37/6.55      | X0_55 != sK2 ),
% 47.37/6.55      inference(instantiation,[status(thm)],[c_4469]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_4524,plain,
% 47.37/6.55      ( k1_zfmisc_1(X0_57) != k1_zfmisc_1(u1_struct_0(sK1))
% 47.37/6.55      | X0_55 != sK2
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(X0_57)) = iProver_top
% 47.37/6.55      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 47.37/6.55      inference(predicate_to_equality,[status(thm)],[c_4523]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_4526,plain,
% 47.37/6.55      ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(u1_struct_0(sK1))
% 47.37/6.55      | sK2 != sK2
% 47.37/6.55      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 47.37/6.55      | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 47.37/6.55      inference(instantiation,[status(thm)],[c_4524]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3404,plain,
% 47.37/6.55      ( X0_55 != X1_55 | X2_55 != X1_55 | X2_55 = X0_55 ),
% 47.37/6.55      theory(equality) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_4485,plain,
% 47.37/6.55      ( X0_55 != X1_55
% 47.37/6.55      | X0_55 = k7_tmap_1(sK1,sK2)
% 47.37/6.55      | k7_tmap_1(sK1,sK2) != X1_55 ),
% 47.37/6.55      inference(instantiation,[status(thm)],[c_3404]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_4529,plain,
% 47.37/6.55      ( X0_55 = k7_tmap_1(sK1,sK2)
% 47.37/6.55      | X0_55 != k6_partfun1(u1_struct_0(sK1))
% 47.37/6.55      | k7_tmap_1(sK1,sK2) != k6_partfun1(u1_struct_0(sK1)) ),
% 47.37/6.55      inference(instantiation,[status(thm)],[c_4485]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_4662,plain,
% 47.37/6.55      ( k7_tmap_1(sK1,sK2) != k6_partfun1(u1_struct_0(sK1))
% 47.37/6.55      | k6_partfun1(u1_struct_0(sK1)) = k7_tmap_1(sK1,sK2)
% 47.37/6.55      | k6_partfun1(u1_struct_0(sK1)) != k6_partfun1(u1_struct_0(sK1)) ),
% 47.37/6.55      inference(instantiation,[status(thm)],[c_4529]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_4705,plain,
% 47.37/6.55      ( X0_57 != u1_struct_0(sK1)
% 47.37/6.55      | k1_zfmisc_1(X0_57) = k1_zfmisc_1(u1_struct_0(sK1)) ),
% 47.37/6.55      inference(instantiation,[status(thm)],[c_3410]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_4706,plain,
% 47.37/6.55      ( k1_xboole_0 != u1_struct_0(sK1)
% 47.37/6.55      | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(u1_struct_0(sK1)) ),
% 47.37/6.55      inference(instantiation,[status(thm)],[c_4705]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_4800,plain,
% 47.37/6.55      ( k6_partfun1(u1_struct_0(sK1)) = k6_partfun1(u1_struct_0(sK1)) ),
% 47.37/6.55      inference(instantiation,[status(thm)],[c_3399]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3412,plain,
% 47.37/6.55      ( X0_57 != X1_57 | k6_partfun1(X0_57) = k6_partfun1(X1_57) ),
% 47.37/6.55      theory(equality) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_4808,plain,
% 47.37/6.55      ( X0_57 != u1_struct_0(sK1)
% 47.37/6.55      | k6_partfun1(X0_57) = k6_partfun1(u1_struct_0(sK1)) ),
% 47.37/6.55      inference(instantiation,[status(thm)],[c_3412]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_4809,plain,
% 47.37/6.55      ( k1_xboole_0 != u1_struct_0(sK1)
% 47.37/6.55      | k6_partfun1(k1_xboole_0) = k6_partfun1(u1_struct_0(sK1)) ),
% 47.37/6.55      inference(instantiation,[status(thm)],[c_4808]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3405,plain,
% 47.37/6.55      ( X0_57 != X1_57 | X2_57 != X1_57 | X2_57 = X0_57 ),
% 47.37/6.55      theory(equality) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_5049,plain,
% 47.37/6.55      ( k2_struct_0(sK1) != X0_57
% 47.37/6.55      | k1_xboole_0 != X0_57
% 47.37/6.55      | k1_xboole_0 = k2_struct_0(sK1) ),
% 47.37/6.55      inference(instantiation,[status(thm)],[c_3405]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_5050,plain,
% 47.37/6.55      ( k2_struct_0(sK1) != k1_xboole_0
% 47.37/6.55      | k1_xboole_0 = k2_struct_0(sK1)
% 47.37/6.55      | k1_xboole_0 != k1_xboole_0 ),
% 47.37/6.55      inference(instantiation,[status(thm)],[c_5049]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3419,plain,
% 47.37/6.55      ( ~ v1_funct_1(X0_55) | v1_funct_1(X1_55) | X1_55 != X0_55 ),
% 47.37/6.55      theory(equality) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_4687,plain,
% 47.37/6.55      ( v1_funct_1(X0_55)
% 47.37/6.55      | ~ v1_funct_1(k7_tmap_1(sK1,X1_55))
% 47.37/6.55      | X0_55 != k7_tmap_1(sK1,X1_55) ),
% 47.37/6.55      inference(instantiation,[status(thm)],[c_3419]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_5276,plain,
% 47.37/6.55      ( ~ v1_funct_1(k7_tmap_1(sK1,X0_55))
% 47.37/6.55      | v1_funct_1(k6_partfun1(u1_struct_0(sK1)))
% 47.37/6.55      | k6_partfun1(u1_struct_0(sK1)) != k7_tmap_1(sK1,X0_55) ),
% 47.37/6.55      inference(instantiation,[status(thm)],[c_4687]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_5287,plain,
% 47.37/6.55      ( k6_partfun1(u1_struct_0(sK1)) != k7_tmap_1(sK1,X0_55)
% 47.37/6.55      | v1_funct_1(k7_tmap_1(sK1,X0_55)) != iProver_top
% 47.37/6.55      | v1_funct_1(k6_partfun1(u1_struct_0(sK1))) = iProver_top ),
% 47.37/6.55      inference(predicate_to_equality,[status(thm)],[c_5276]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_5289,plain,
% 47.37/6.55      ( k6_partfun1(u1_struct_0(sK1)) != k7_tmap_1(sK1,sK2)
% 47.37/6.55      | v1_funct_1(k7_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v1_funct_1(k6_partfun1(u1_struct_0(sK1))) = iProver_top ),
% 47.37/6.55      inference(instantiation,[status(thm)],[c_5287]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_5909,plain,
% 47.37/6.55      ( v1_funct_1(X0_55)
% 47.37/6.55      | ~ v1_funct_1(k6_partfun1(u1_struct_0(sK1)))
% 47.37/6.55      | X0_55 != k6_partfun1(u1_struct_0(sK1)) ),
% 47.37/6.55      inference(instantiation,[status(thm)],[c_3419]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_6244,plain,
% 47.37/6.55      ( v1_funct_1(k6_partfun1(X0_57))
% 47.37/6.55      | ~ v1_funct_1(k6_partfun1(u1_struct_0(sK1)))
% 47.37/6.55      | k6_partfun1(X0_57) != k6_partfun1(u1_struct_0(sK1)) ),
% 47.37/6.55      inference(instantiation,[status(thm)],[c_5909]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_6245,plain,
% 47.37/6.55      ( k6_partfun1(X0_57) != k6_partfun1(u1_struct_0(sK1))
% 47.37/6.55      | v1_funct_1(k6_partfun1(X0_57)) = iProver_top
% 47.37/6.55      | v1_funct_1(k6_partfun1(u1_struct_0(sK1))) != iProver_top ),
% 47.37/6.55      inference(predicate_to_equality,[status(thm)],[c_6244]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_6247,plain,
% 47.37/6.55      ( k6_partfun1(k1_xboole_0) != k6_partfun1(u1_struct_0(sK1))
% 47.37/6.55      | v1_funct_1(k6_partfun1(u1_struct_0(sK1))) != iProver_top
% 47.37/6.55      | v1_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
% 47.37/6.55      inference(instantiation,[status(thm)],[c_6245]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_5250,plain,
% 47.37/6.55      ( X0_57 != X1_57
% 47.37/6.55      | X0_57 = u1_struct_0(sK1)
% 47.37/6.55      | u1_struct_0(sK1) != X1_57 ),
% 47.37/6.55      inference(instantiation,[status(thm)],[c_3405]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_7125,plain,
% 47.37/6.55      ( X0_57 = u1_struct_0(sK1)
% 47.37/6.55      | X0_57 != k2_struct_0(sK1)
% 47.37/6.55      | u1_struct_0(sK1) != k2_struct_0(sK1) ),
% 47.37/6.55      inference(instantiation,[status(thm)],[c_5250]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_7126,plain,
% 47.37/6.55      ( u1_struct_0(sK1) != k2_struct_0(sK1)
% 47.37/6.55      | k1_xboole_0 = u1_struct_0(sK1)
% 47.37/6.55      | k1_xboole_0 != k2_struct_0(sK1) ),
% 47.37/6.55      inference(instantiation,[status(thm)],[c_7125]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_90015,plain,
% 47.37/6.55      ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 47.37/6.55      inference(demodulation,[status(thm)],[c_89489,c_7176]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_33,negated_conjecture,
% 47.37/6.55      ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
% 47.37/6.55      | v3_pre_topc(sK2,sK1) ),
% 47.37/6.55      inference(cnf_transformation,[],[f93]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3382,negated_conjecture,
% 47.37/6.55      ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2)))
% 47.37/6.55      | v3_pre_topc(sK2,sK1) ),
% 47.37/6.55      inference(subtyping,[status(esa)],[c_33]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_4330,plain,
% 47.37/6.55      ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) = iProver_top
% 47.37/6.55      | v3_pre_topc(sK2,sK1) = iProver_top ),
% 47.37/6.55      inference(predicate_to_equality,[status(thm)],[c_3382]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_4568,plain,
% 47.37/6.55      ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK1,sK2))) = iProver_top ),
% 47.37/6.55      inference(global_propositional_subsumption,
% 47.37/6.55                [status(thm)],
% 47.37/6.55                [c_4330,c_42,c_3502]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_5349,plain,
% 47.37/6.55      ( v1_funct_2(k7_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(sK1)) = iProver_top ),
% 47.37/6.55      inference(demodulation,[status(thm)],[c_5255,c_4568]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_5563,plain,
% 47.37/6.55      ( v1_funct_2(k6_partfun1(u1_struct_0(sK1)),u1_struct_0(sK1),u1_struct_0(sK1)) = iProver_top ),
% 47.37/6.55      inference(demodulation,[status(thm)],[c_5471,c_5349]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_7066,plain,
% 47.37/6.55      ( v1_funct_2(k6_partfun1(k2_struct_0(sK1)),k2_struct_0(sK1),k2_struct_0(sK1)) = iProver_top ),
% 47.37/6.55      inference(light_normalisation,[status(thm)],[c_5563,c_5702]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_90017,plain,
% 47.37/6.55      ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) = iProver_top ),
% 47.37/6.55      inference(demodulation,[status(thm)],[c_89489,c_7066]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_90034,plain,
% 47.37/6.55      ( v5_pre_topc(k6_partfun1(k1_xboole_0),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v3_pre_topc(sK2,sK1) != iProver_top ),
% 47.37/6.55      inference(demodulation,[status(thm)],[c_89489,c_5990]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_90016,plain,
% 47.37/6.55      ( k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK2) = sK2 ),
% 47.37/6.55      inference(demodulation,[status(thm)],[c_89489,c_5783]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_14,plain,
% 47.37/6.55      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 47.37/6.55      | ~ v5_pre_topc(X0,X1,X2)
% 47.37/6.55      | ~ v3_pre_topc(X3,X2)
% 47.37/6.55      | v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
% 47.37/6.55      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 47.37/6.55      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 47.37/6.55      | ~ v1_funct_1(X0)
% 47.37/6.55      | ~ l1_pre_topc(X1)
% 47.37/6.55      | ~ l1_pre_topc(X2)
% 47.37/6.55      | k2_struct_0(X1) != k1_xboole_0 ),
% 47.37/6.55      inference(cnf_transformation,[],[f67]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3387,plain,
% 47.37/6.55      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58))
% 47.37/6.55      | ~ v5_pre_topc(X0_55,X0_58,X1_58)
% 47.37/6.55      | ~ v3_pre_topc(X1_55,X1_58)
% 47.37/6.55      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_55,X1_55),X0_58)
% 47.37/6.55      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
% 47.37/6.55      | ~ m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(X1_58)))
% 47.37/6.55      | ~ v1_funct_1(X0_55)
% 47.37/6.55      | ~ l1_pre_topc(X0_58)
% 47.37/6.55      | ~ l1_pre_topc(X1_58)
% 47.37/6.55      | k2_struct_0(X0_58) != k1_xboole_0 ),
% 47.37/6.55      inference(subtyping,[status(esa)],[c_14]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_4325,plain,
% 47.37/6.55      ( k2_struct_0(X0_58) != k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,X0_58,X1_58) != iProver_top
% 47.37/6.55      | v3_pre_topc(X1_55,X1_58) != iProver_top
% 47.37/6.55      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_55,X1_55),X0_58) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
% 47.37/6.55      | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(X1_58))) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top
% 47.37/6.55      | l1_pre_topc(X1_58) != iProver_top ),
% 47.37/6.55      inference(predicate_to_equality,[status(thm)],[c_3387]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_90177,plain,
% 47.37/6.55      ( v1_funct_2(X0_55,u1_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,sK1,X0_58) != iProver_top
% 47.37/6.55      | v3_pre_topc(X1_55,X0_58) != iProver_top
% 47.37/6.55      | v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0_58),X0_55,X1_55),sK1) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(X0_58))) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top
% 47.37/6.55      | l1_pre_topc(sK1) != iProver_top ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_89489,c_4325]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_90039,plain,
% 47.37/6.55      ( u1_struct_0(sK1) = k1_xboole_0 ),
% 47.37/6.55      inference(demodulation,[status(thm)],[c_89489,c_5702]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_90184,plain,
% 47.37/6.55      ( v1_funct_2(X0_55,k1_xboole_0,u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,sK1,X0_58) != iProver_top
% 47.37/6.55      | v3_pre_topc(X1_55,X0_58) != iProver_top
% 47.37/6.55      | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X0_58),X0_55,X1_55),sK1) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(X0_58))) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top
% 47.37/6.55      | l1_pre_topc(sK1) != iProver_top ),
% 47.37/6.55      inference(light_normalisation,[status(thm)],[c_90177,c_90039]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_93374,plain,
% 47.37/6.55      ( l1_pre_topc(X0_58) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(X0_58))) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X0_58),X0_55,X1_55),sK1) = iProver_top
% 47.37/6.55      | v3_pre_topc(X1_55,X0_58) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,sK1,X0_58) != iProver_top
% 47.37/6.55      | v1_funct_2(X0_55,k1_xboole_0,u1_struct_0(X0_58)) != iProver_top ),
% 47.37/6.55      inference(global_propositional_subsumption,
% 47.37/6.55                [status(thm)],
% 47.37/6.55                [c_90184,c_41]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_93375,plain,
% 47.37/6.55      ( v1_funct_2(X0_55,k1_xboole_0,u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,sK1,X0_58) != iProver_top
% 47.37/6.55      | v3_pre_topc(X1_55,X0_58) != iProver_top
% 47.37/6.55      | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X0_58),X0_55,X1_55),sK1) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(X0_58))) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top ),
% 47.37/6.55      inference(renaming,[status(thm)],[c_93374]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_93379,plain,
% 47.37/6.55      ( v1_funct_2(X0_55,k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v3_pre_topc(X1_55,k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0_55,X1_55),sK1) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
% 47.37/6.55      | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_90023,c_93375]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_93381,plain,
% 47.37/6.55      ( v1_funct_2(X0_55,k1_xboole_0,k1_xboole_0) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v3_pre_topc(X1_55,k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0_55,X1_55),sK1) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 47.37/6.55      | m1_subset_1(X1_55,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 47.37/6.55      inference(light_normalisation,[status(thm)],[c_93379,c_90023]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_97184,plain,
% 47.37/6.55      ( v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | m1_subset_1(X1_55,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 47.37/6.55      | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0_55,X1_55),sK1) = iProver_top
% 47.37/6.55      | v3_pre_topc(X1_55,k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v1_funct_2(X0_55,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 47.37/6.55      inference(global_propositional_subsumption,
% 47.37/6.55                [status(thm)],
% 47.37/6.55                [c_93381,c_42,c_3529]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_97185,plain,
% 47.37/6.55      ( v1_funct_2(X0_55,k1_xboole_0,k1_xboole_0) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v3_pre_topc(X1_55,k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0_55,X1_55),sK1) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 47.37/6.55      | m1_subset_1(X1_55,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top ),
% 47.37/6.55      inference(renaming,[status(thm)],[c_97184]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_97190,plain,
% 47.37/6.55      ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) != iProver_top
% 47.37/6.55      | v5_pre_topc(k6_partfun1(k1_xboole_0),sK1,k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v3_pre_topc(sK2,k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v3_pre_topc(sK2,sK1) = iProver_top
% 47.37/6.55      | m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 47.37/6.55      | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 47.37/6.55      | v1_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_90016,c_97185]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_90028,plain,
% 47.37/6.55      ( v5_pre_topc(k6_partfun1(k1_xboole_0),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.55      | v3_pre_topc(sK2,sK1) = iProver_top ),
% 47.37/6.55      inference(demodulation,[status(thm)],[c_89489,c_6286]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_97361,plain,
% 47.37/6.55      ( v3_pre_topc(sK2,sK1) = iProver_top ),
% 47.37/6.55      inference(global_propositional_subsumption,
% 47.37/6.55                [status(thm)],
% 47.37/6.55                [c_97190,c_36,c_35,c_42,c_3445,c_3447,c_3495,c_3511,
% 47.37/6.55                 c_3513,c_3520,c_3531,c_4451,c_4505,c_4526,c_4662,c_4706,
% 47.37/6.55                 c_4800,c_4809,c_5050,c_5289,c_6247,c_7126,c_18236,
% 47.37/6.55                 c_34097,c_89212,c_90015,c_90017,c_90028]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_90009,plain,
% 47.37/6.55      ( g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)) = k6_tmap_1(sK1,sK2)
% 47.37/6.55      | v3_pre_topc(sK2,sK1) != iProver_top ),
% 47.37/6.55      inference(demodulation,[status(thm)],[c_89489,c_6173]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_97365,plain,
% 47.37/6.55      ( g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)) = k6_tmap_1(sK1,sK2) ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_97361,c_90009]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_5359,plain,
% 47.37/6.55      ( v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
% 47.37/6.55      | v1_funct_2(X0_55,u1_struct_0(g1_pre_topc(u1_struct_0(X0_58),u1_pre_topc(X0_58))),u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,X0_58,k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,g1_pre_topc(u1_struct_0(X0_58),u1_pre_topc(X0_58)),k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0_58),u1_pre_topc(X0_58))),u1_struct_0(sK1)))) != iProver_top
% 47.37/6.55      | v2_pre_topc(X0_58) != iProver_top
% 47.37/6.55      | v2_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top
% 47.37/6.55      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_5255,c_4317]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_5364,plain,
% 47.37/6.55      ( v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(sK1)) != iProver_top
% 47.37/6.55      | v1_funct_2(X0_55,u1_struct_0(g1_pre_topc(u1_struct_0(X0_58),u1_pre_topc(X0_58))),u1_struct_0(sK1)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,X0_58,k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,g1_pre_topc(u1_struct_0(X0_58),u1_pre_topc(X0_58)),k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK1)))) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0_58),u1_pre_topc(X0_58))),u1_struct_0(sK1)))) != iProver_top
% 47.37/6.55      | v2_pre_topc(X0_58) != iProver_top
% 47.37/6.55      | v2_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top
% 47.37/6.55      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 47.37/6.55      inference(light_normalisation,[status(thm)],[c_5359,c_5255]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3524,plain,
% 47.37/6.55      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 47.37/6.55      | v2_pre_topc(k6_tmap_1(sK1,X0_55)) = iProver_top ),
% 47.37/6.55      inference(predicate_to_equality,[status(thm)],[c_3365]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3526,plain,
% 47.37/6.55      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 47.37/6.55      | v2_pre_topc(k6_tmap_1(sK1,sK2)) = iProver_top ),
% 47.37/6.55      inference(instantiation,[status(thm)],[c_3524]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_8311,plain,
% 47.37/6.55      ( l1_pre_topc(X0_58) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(sK1)) != iProver_top
% 47.37/6.55      | v1_funct_2(X0_55,u1_struct_0(g1_pre_topc(u1_struct_0(X0_58),u1_pre_topc(X0_58))),u1_struct_0(sK1)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,X0_58,k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,g1_pre_topc(u1_struct_0(X0_58),u1_pre_topc(X0_58)),k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK1)))) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0_58),u1_pre_topc(X0_58))),u1_struct_0(sK1)))) != iProver_top
% 47.37/6.55      | v2_pre_topc(X0_58) != iProver_top ),
% 47.37/6.55      inference(global_propositional_subsumption,
% 47.37/6.55                [status(thm)],
% 47.37/6.55                [c_5364,c_42,c_3526,c_3529]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_8312,plain,
% 47.37/6.55      ( v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(sK1)) != iProver_top
% 47.37/6.55      | v1_funct_2(X0_55,u1_struct_0(g1_pre_topc(u1_struct_0(X0_58),u1_pre_topc(X0_58))),u1_struct_0(sK1)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,X0_58,k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,g1_pre_topc(u1_struct_0(X0_58),u1_pre_topc(X0_58)),k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK1)))) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0_58),u1_pre_topc(X0_58))),u1_struct_0(sK1)))) != iProver_top
% 47.37/6.55      | v2_pre_topc(X0_58) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top ),
% 47.37/6.55      inference(renaming,[status(thm)],[c_8311]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_8317,plain,
% 47.37/6.55      ( v1_funct_2(X0_55,u1_struct_0(X0_58),k2_struct_0(sK1)) != iProver_top
% 47.37/6.55      | v1_funct_2(X0_55,u1_struct_0(g1_pre_topc(u1_struct_0(X0_58),u1_pre_topc(X0_58))),k2_struct_0(sK1)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,X0_58,k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,g1_pre_topc(u1_struct_0(X0_58),u1_pre_topc(X0_58)),k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),k2_struct_0(sK1)))) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0_58),u1_pre_topc(X0_58))),k2_struct_0(sK1)))) != iProver_top
% 47.37/6.55      | v2_pre_topc(X0_58) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top ),
% 47.37/6.55      inference(light_normalisation,[status(thm)],[c_8312,c_5702]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_8321,plain,
% 47.37/6.55      ( v1_funct_2(X0_55,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k2_struct_0(sK1)) != iProver_top
% 47.37/6.55      | v1_funct_2(X0_55,u1_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),k2_struct_0(sK1)))) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 47.37/6.55      | v2_pre_topc(sK1) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(sK1) != iProver_top ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_5702,c_8317]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_8326,plain,
% 47.37/6.55      ( v1_funct_2(X0_55,u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),k2_struct_0(sK1)) != iProver_top
% 47.37/6.55      | v1_funct_2(X0_55,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),k2_struct_0(sK1)))) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 47.37/6.55      | v2_pre_topc(sK1) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(sK1) != iProver_top ),
% 47.37/6.55      inference(light_normalisation,[status(thm)],[c_8321,c_5702]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_8504,plain,
% 47.37/6.55      ( v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | v1_funct_2(X0_55,u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),k2_struct_0(sK1)) != iProver_top
% 47.37/6.55      | v1_funct_2(X0_55,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),k2_struct_0(sK1)))) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top ),
% 47.37/6.55      inference(global_propositional_subsumption,
% 47.37/6.55                [status(thm)],
% 47.37/6.55                [c_8326,c_40,c_41]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_8505,plain,
% 47.37/6.55      ( v1_funct_2(X0_55,u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),k2_struct_0(sK1)) != iProver_top
% 47.37/6.55      | v1_funct_2(X0_55,k2_struct_0(sK1),k2_struct_0(sK1)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),k2_struct_0(sK1)))) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top ),
% 47.37/6.55      inference(renaming,[status(thm)],[c_8504]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_89997,plain,
% 47.37/6.55      ( v1_funct_2(X0_55,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),k1_xboole_0) != iProver_top
% 47.37/6.55      | v1_funct_2(X0_55,k1_xboole_0,k1_xboole_0) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)),k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),k1_xboole_0))) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top ),
% 47.37/6.55      inference(demodulation,[status(thm)],[c_89489,c_8505]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_97368,plain,
% 47.37/6.55      ( v1_funct_2(X0_55,u1_struct_0(k6_tmap_1(sK1,sK2)),k1_xboole_0) != iProver_top
% 47.37/6.55      | v1_funct_2(X0_55,k1_xboole_0,k1_xboole_0) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)),k1_xboole_0))) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top ),
% 47.37/6.55      inference(demodulation,[status(thm)],[c_97365,c_89997]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_97377,plain,
% 47.37/6.55      ( v1_funct_2(X0_55,k1_xboole_0,k1_xboole_0) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top ),
% 47.37/6.55      inference(light_normalisation,[status(thm)],[c_97368,c_90023]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_128151,plain,
% 47.37/6.55      ( k8_relset_1(u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(k6_tmap_1(sK1,sK2)),k6_partfun1(u1_struct_0(k6_tmap_1(sK1,sK2))),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k7_tmap_1(sK1,sK2))
% 47.37/6.55      | v1_funct_2(k7_tmap_1(sK1,sK2),k1_xboole_0,k1_xboole_0) != iProver_top
% 47.37/6.55      | v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.55      | m1_subset_1(k7_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 47.37/6.55      | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 47.37/6.55      | v1_funct_1(k7_tmap_1(sK1,sK2)) != iProver_top ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_128142,c_97377]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_128158,plain,
% 47.37/6.55      ( k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k1_xboole_0))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k1_xboole_0))
% 47.37/6.55      | v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) != iProver_top
% 47.37/6.55      | v5_pre_topc(k6_partfun1(k1_xboole_0),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.55      | m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 47.37/6.55      | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 47.37/6.55      | v1_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top ),
% 47.37/6.55      inference(light_normalisation,
% 47.37/6.55                [status(thm)],
% 47.37/6.55                [c_128151,c_90023,c_90024]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_128159,plain,
% 47.37/6.55      ( k10_relat_1(k6_partfun1(k1_xboole_0),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k1_xboole_0))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k1_xboole_0))
% 47.37/6.55      | v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) != iProver_top
% 47.37/6.55      | v5_pre_topc(k6_partfun1(k1_xboole_0),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.55      | m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 47.37/6.55      | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 47.37/6.55      | v1_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top ),
% 47.37/6.55      inference(demodulation,[status(thm)],[c_128158,c_90035]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_128703,plain,
% 47.37/6.55      ( k10_relat_1(k6_partfun1(k1_xboole_0),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k1_xboole_0))) = sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k1_xboole_0)) ),
% 47.37/6.55      inference(global_propositional_subsumption,
% 47.37/6.55                [status(thm)],
% 47.37/6.55                [c_128163,c_36,c_35,c_42,c_3445,c_3447,c_3495,c_3511,
% 47.37/6.55                 c_3513,c_3520,c_3531,c_4451,c_4505,c_4526,c_4662,c_4706,
% 47.37/6.55                 c_4800,c_4809,c_5050,c_5289,c_6247,c_7126,c_18236,
% 47.37/6.55                 c_34097,c_89212,c_90015,c_90017,c_90028,c_90034,c_97190,
% 47.37/6.55                 c_128159]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_8,plain,
% 47.37/6.55      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 47.37/6.55      | v5_pre_topc(X0,X1,X2)
% 47.37/6.55      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0)),X1)
% 47.37/6.55      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 47.37/6.55      | ~ v1_funct_1(X0)
% 47.37/6.55      | ~ l1_pre_topc(X1)
% 47.37/6.55      | ~ l1_pre_topc(X2)
% 47.37/6.55      | k2_struct_0(X1) != k1_xboole_0 ),
% 47.37/6.55      inference(cnf_transformation,[],[f73]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_3393,plain,
% 47.37/6.55      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58))
% 47.37/6.55      | v5_pre_topc(X0_55,X0_58,X1_58)
% 47.37/6.55      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_55,sK0(X0_58,X1_58,X0_55)),X0_58)
% 47.37/6.55      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
% 47.37/6.55      | ~ v1_funct_1(X0_55)
% 47.37/6.55      | ~ l1_pre_topc(X0_58)
% 47.37/6.55      | ~ l1_pre_topc(X1_58)
% 47.37/6.55      | k2_struct_0(X0_58) != k1_xboole_0 ),
% 47.37/6.55      inference(subtyping,[status(esa)],[c_8]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_4319,plain,
% 47.37/6.55      ( k2_struct_0(X0_58) != k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,X0_58,X1_58) = iProver_top
% 47.37/6.55      | v3_pre_topc(k8_relset_1(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_55,sK0(X0_58,X1_58,X0_55)),X0_58) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top
% 47.37/6.55      | l1_pre_topc(X1_58) != iProver_top ),
% 47.37/6.55      inference(predicate_to_equality,[status(thm)],[c_3393]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_6516,plain,
% 47.37/6.55      ( k2_struct_0(sK1) != k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
% 47.37/6.55      | v3_pre_topc(k8_relset_1(u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(X0_58),X0_55,sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55)),k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top
% 47.37/6.55      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 47.37/6.55      inference(superposition,[status(thm)],[c_5705,c_4319]) ).
% 47.37/6.55  
% 47.37/6.55  cnf(c_6521,plain,
% 47.37/6.55      ( k2_struct_0(sK1) != k1_xboole_0
% 47.37/6.55      | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.55      | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
% 47.37/6.55      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0_58),X0_55,sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55)),k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.55      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.55      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.55      | l1_pre_topc(X0_58) != iProver_top
% 47.37/6.55      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 47.37/6.56      inference(light_normalisation,[status(thm)],[c_6516,c_5778]) ).
% 47.37/6.56  
% 47.37/6.56  cnf(c_11334,plain,
% 47.37/6.56      ( l1_pre_topc(X0_58) != iProver_top
% 47.37/6.56      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.56      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.56      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0_58),X0_55,sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55)),k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.56      | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
% 47.37/6.56      | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.56      | k2_struct_0(sK1) != k1_xboole_0 ),
% 47.37/6.56      inference(global_propositional_subsumption,
% 47.37/6.56                [status(thm)],
% 47.37/6.56                [c_6521,c_42,c_3529]) ).
% 47.37/6.56  
% 47.37/6.56  cnf(c_11335,plain,
% 47.37/6.56      ( k2_struct_0(sK1) != k1_xboole_0
% 47.37/6.56      | v1_funct_2(X0_55,k2_struct_0(sK1),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.56      | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
% 47.37/6.56      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),u1_struct_0(X0_58),X0_55,sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55)),k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.56      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.56      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.56      | l1_pre_topc(X0_58) != iProver_top ),
% 47.37/6.56      inference(renaming,[status(thm)],[c_11334]) ).
% 47.37/6.56  
% 47.37/6.56  cnf(c_89980,plain,
% 47.37/6.56      ( k1_xboole_0 != k1_xboole_0
% 47.37/6.56      | v1_funct_2(X0_55,k1_xboole_0,u1_struct_0(X0_58)) != iProver_top
% 47.37/6.56      | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
% 47.37/6.56      | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X0_58),X0_55,sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55)),k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.56      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.56      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.56      | l1_pre_topc(X0_58) != iProver_top ),
% 47.37/6.56      inference(demodulation,[status(thm)],[c_89489,c_11335]) ).
% 47.37/6.56  
% 47.37/6.56  cnf(c_90042,plain,
% 47.37/6.56      ( v1_funct_2(X0_55,k1_xboole_0,u1_struct_0(X0_58)) != iProver_top
% 47.37/6.56      | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) = iProver_top
% 47.37/6.56      | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X0_58),X0_55,sK0(k6_tmap_1(sK1,sK2),X0_58,X0_55)),k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.56      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.56      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.56      | l1_pre_topc(X0_58) != iProver_top ),
% 47.37/6.56      inference(equality_resolution_simp,[status(thm)],[c_89980]) ).
% 47.37/6.56  
% 47.37/6.56  cnf(c_119637,plain,
% 47.37/6.56      ( v1_funct_2(X0_55,k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
% 47.37/6.56      | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.56      | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0_55,sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_55)),k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.56      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
% 47.37/6.56      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.56      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 47.37/6.56      inference(superposition,[status(thm)],[c_90023,c_90042]) ).
% 47.37/6.56  
% 47.37/6.56  cnf(c_119640,plain,
% 47.37/6.56      ( v1_funct_2(X0_55,k1_xboole_0,k1_xboole_0) != iProver_top
% 47.37/6.56      | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.56      | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0_55,sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_55)),k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.56      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 47.37/6.56      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.56      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 47.37/6.56      inference(light_normalisation,[status(thm)],[c_119637,c_90023]) ).
% 47.37/6.56  
% 47.37/6.56  cnf(c_119896,plain,
% 47.37/6.56      ( v1_funct_1(X0_55) != iProver_top
% 47.37/6.56      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 47.37/6.56      | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0_55,sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_55)),k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.56      | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.56      | v1_funct_2(X0_55,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 47.37/6.56      inference(global_propositional_subsumption,
% 47.37/6.56                [status(thm)],
% 47.37/6.56                [c_119640,c_42,c_3529]) ).
% 47.37/6.56  
% 47.37/6.56  cnf(c_119897,plain,
% 47.37/6.56      ( v1_funct_2(X0_55,k1_xboole_0,k1_xboole_0) != iProver_top
% 47.37/6.56      | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.56      | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X0_55,sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),X0_55)),k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.56      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 47.37/6.56      | v1_funct_1(X0_55) != iProver_top ),
% 47.37/6.56      inference(renaming,[status(thm)],[c_119896]) ).
% 47.37/6.56  
% 47.37/6.56  cnf(c_119902,plain,
% 47.37/6.56      ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) != iProver_top
% 47.37/6.56      | v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.56      | v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k1_xboole_0))),k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.56      | m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 47.37/6.56      | v1_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top ),
% 47.37/6.56      inference(superposition,[status(thm)],[c_90035,c_119897]) ).
% 47.37/6.56  
% 47.37/6.56  cnf(c_90000,plain,
% 47.37/6.56      ( v1_funct_2(X0_55,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.56      | v1_funct_2(X0_55,k1_xboole_0,u1_struct_0(X0_58)) != iProver_top
% 47.37/6.56      | v5_pre_topc(X0_55,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)),X0_58) != iProver_top
% 47.37/6.56      | v5_pre_topc(X0_55,sK1,X0_58) = iProver_top
% 47.37/6.56      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.56      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.56      | v2_pre_topc(X0_58) != iProver_top
% 47.37/6.56      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.56      | l1_pre_topc(X0_58) != iProver_top ),
% 47.37/6.56      inference(demodulation,[status(thm)],[c_89489,c_8136]) ).
% 47.37/6.56  
% 47.37/6.56  cnf(c_97366,plain,
% 47.37/6.56      ( v1_funct_2(X0_55,u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(X0_58)) != iProver_top
% 47.37/6.56      | v1_funct_2(X0_55,k1_xboole_0,u1_struct_0(X0_58)) != iProver_top
% 47.37/6.56      | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) != iProver_top
% 47.37/6.56      | v5_pre_topc(X0_55,sK1,X0_58) = iProver_top
% 47.37/6.56      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)),u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.56      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.56      | v2_pre_topc(X0_58) != iProver_top
% 47.37/6.56      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.56      | l1_pre_topc(X0_58) != iProver_top ),
% 47.37/6.56      inference(demodulation,[status(thm)],[c_97365,c_90000]) ).
% 47.37/6.56  
% 47.37/6.56  cnf(c_97379,plain,
% 47.37/6.56      ( v1_funct_2(X0_55,k1_xboole_0,u1_struct_0(X0_58)) != iProver_top
% 47.37/6.56      | v5_pre_topc(X0_55,k6_tmap_1(sK1,sK2),X0_58) != iProver_top
% 47.37/6.56      | v5_pre_topc(X0_55,sK1,X0_58) = iProver_top
% 47.37/6.56      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0_58)))) != iProver_top
% 47.37/6.56      | v2_pre_topc(X0_58) != iProver_top
% 47.37/6.56      | v1_funct_1(X0_55) != iProver_top
% 47.37/6.56      | l1_pre_topc(X0_58) != iProver_top ),
% 47.37/6.56      inference(light_normalisation,[status(thm)],[c_97366,c_90023]) ).
% 47.37/6.56  
% 47.37/6.56  cnf(c_98045,plain,
% 47.37/6.56      ( v1_funct_2(k7_tmap_1(sK1,X0_55),k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,X0_55))) != iProver_top
% 47.37/6.56      | v5_pre_topc(k7_tmap_1(sK1,X0_55),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_55)) != iProver_top
% 47.37/6.56      | v5_pre_topc(k7_tmap_1(sK1,X0_55),sK1,k6_tmap_1(sK1,X0_55)) = iProver_top
% 47.37/6.56      | m1_subset_1(X0_55,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 47.37/6.56      | v2_pre_topc(k6_tmap_1(sK1,X0_55)) != iProver_top
% 47.37/6.56      | v1_funct_1(k7_tmap_1(sK1,X0_55)) != iProver_top
% 47.37/6.56      | l1_pre_topc(k6_tmap_1(sK1,X0_55)) != iProver_top ),
% 47.37/6.56      inference(superposition,[status(thm)],[c_90032,c_97379]) ).
% 47.37/6.56  
% 47.37/6.56  cnf(c_90013,plain,
% 47.37/6.56      ( m1_subset_1(X0_55,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 47.37/6.56      | v2_pre_topc(k6_tmap_1(sK1,X0_55)) = iProver_top ),
% 47.37/6.56      inference(demodulation,[status(thm)],[c_89489,c_5781]) ).
% 47.37/6.56  
% 47.37/6.56  cnf(c_98470,plain,
% 47.37/6.56      ( m1_subset_1(X0_55,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 47.37/6.56      | v5_pre_topc(k7_tmap_1(sK1,X0_55),sK1,k6_tmap_1(sK1,X0_55)) = iProver_top
% 47.37/6.56      | v5_pre_topc(k7_tmap_1(sK1,X0_55),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_55)) != iProver_top ),
% 47.37/6.56      inference(global_propositional_subsumption,
% 47.37/6.56                [status(thm)],
% 47.37/6.56                [c_98045,c_90012,c_90013,c_90014,c_90033]) ).
% 47.37/6.56  
% 47.37/6.56  cnf(c_98471,plain,
% 47.37/6.56      ( v5_pre_topc(k7_tmap_1(sK1,X0_55),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,X0_55)) != iProver_top
% 47.37/6.56      | v5_pre_topc(k7_tmap_1(sK1,X0_55),sK1,k6_tmap_1(sK1,X0_55)) = iProver_top
% 47.37/6.56      | m1_subset_1(X0_55,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 47.37/6.56      inference(renaming,[status(thm)],[c_98470]) ).
% 47.37/6.56  
% 47.37/6.56  cnf(c_98478,plain,
% 47.37/6.56      ( v5_pre_topc(k7_tmap_1(sK1,sK2),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.56      | v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.56      | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 47.37/6.56      inference(superposition,[status(thm)],[c_90024,c_98471]) ).
% 47.37/6.56  
% 47.37/6.56  cnf(c_98479,plain,
% 47.37/6.56      ( v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.56      | v5_pre_topc(k6_partfun1(k1_xboole_0),sK1,k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.56      | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 47.37/6.56      inference(light_normalisation,[status(thm)],[c_98478,c_90024]) ).
% 47.37/6.56  
% 47.37/6.56  cnf(c_119905,plain,
% 47.37/6.56      ( v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k1_xboole_0))),k6_tmap_1(sK1,sK2)) != iProver_top ),
% 47.37/6.56      inference(global_propositional_subsumption,
% 47.37/6.56                [status(thm)],
% 47.37/6.56                [c_119902,c_36,c_35,c_42,c_3445,c_3447,c_3495,c_3511,
% 47.37/6.56                 c_3513,c_3520,c_3531,c_4451,c_4505,c_4526,c_4662,c_4706,
% 47.37/6.56                 c_4800,c_4809,c_5050,c_5289,c_6247,c_7126,c_18236,
% 47.37/6.56                 c_34097,c_89212,c_90015,c_90017,c_90028,c_90034,c_97190,
% 47.37/6.56                 c_98479]) ).
% 47.37/6.56  
% 47.37/6.56  cnf(c_128705,plain,
% 47.37/6.56      ( v3_pre_topc(sK0(k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2),k6_partfun1(k1_xboole_0)),k6_tmap_1(sK1,sK2)) != iProver_top ),
% 47.37/6.56      inference(demodulation,[status(thm)],[c_128703,c_119905]) ).
% 47.37/6.56  
% 47.37/6.56  cnf(c_134575,plain,
% 47.37/6.56      ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,sK2))) != iProver_top
% 47.37/6.56      | v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.56      | m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK1,sK2))))) != iProver_top
% 47.37/6.56      | v1_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
% 47.37/6.56      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 47.37/6.56      inference(superposition,[status(thm)],[c_90040,c_128705]) ).
% 47.37/6.56  
% 47.37/6.56  cnf(c_134576,plain,
% 47.37/6.56      ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) != iProver_top
% 47.37/6.56      | v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK1,sK2),k6_tmap_1(sK1,sK2)) = iProver_top
% 47.37/6.56      | m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 47.37/6.56      | v1_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
% 47.37/6.56      | l1_pre_topc(k6_tmap_1(sK1,sK2)) != iProver_top ),
% 47.37/6.56      inference(light_normalisation,[status(thm)],[c_134575,c_90023]) ).
% 47.37/6.56  
% 47.37/6.56  cnf(c_87665,plain,
% 47.37/6.56      ( X0_57 != k2_struct_0(sK1)
% 47.37/6.56      | k6_partfun1(X0_57) = k6_partfun1(k2_struct_0(sK1)) ),
% 47.37/6.56      inference(instantiation,[status(thm)],[c_3412]) ).
% 47.37/6.56  
% 47.37/6.56  cnf(c_87667,plain,
% 47.37/6.56      ( k1_xboole_0 != k2_struct_0(sK1)
% 47.37/6.56      | k6_partfun1(k1_xboole_0) = k6_partfun1(k2_struct_0(sK1)) ),
% 47.37/6.56      inference(instantiation,[status(thm)],[c_87665]) ).
% 47.37/6.56  
% 47.37/6.56  cnf(c_60951,plain,
% 47.37/6.56      ( X0_55 != X1_55
% 47.37/6.56      | X0_55 = k7_tmap_1(sK1,sK2)
% 47.37/6.56      | k7_tmap_1(sK1,sK2) != X1_55 ),
% 47.37/6.56      inference(instantiation,[status(thm)],[c_3404]) ).
% 47.37/6.56  
% 47.37/6.56  cnf(c_66552,plain,
% 47.37/6.56      ( X0_55 = k7_tmap_1(sK1,sK2)
% 47.37/6.56      | X0_55 != k6_partfun1(k2_struct_0(sK1))
% 47.37/6.56      | k7_tmap_1(sK1,sK2) != k6_partfun1(k2_struct_0(sK1)) ),
% 47.37/6.56      inference(instantiation,[status(thm)],[c_60951]) ).
% 47.37/6.56  
% 47.37/6.56  cnf(c_78478,plain,
% 47.37/6.56      ( k7_tmap_1(sK1,sK2) != k6_partfun1(k2_struct_0(sK1))
% 47.37/6.56      | k6_partfun1(X0_57) = k7_tmap_1(sK1,sK2)
% 47.37/6.56      | k6_partfun1(X0_57) != k6_partfun1(k2_struct_0(sK1)) ),
% 47.37/6.56      inference(instantiation,[status(thm)],[c_66552]) ).
% 47.37/6.56  
% 47.37/6.56  cnf(c_78479,plain,
% 47.37/6.56      ( k7_tmap_1(sK1,sK2) != k6_partfun1(k2_struct_0(sK1))
% 47.37/6.56      | k6_partfun1(k1_xboole_0) = k7_tmap_1(sK1,sK2)
% 47.37/6.56      | k6_partfun1(k1_xboole_0) != k6_partfun1(k2_struct_0(sK1)) ),
% 47.37/6.56      inference(instantiation,[status(thm)],[c_78478]) ).
% 47.37/6.56  
% 47.37/6.56  cnf(c_64333,plain,
% 47.37/6.56      ( u1_struct_0(k6_tmap_1(sK1,X0_55)) != X0_57
% 47.37/6.56      | k1_xboole_0 != X0_57
% 47.37/6.56      | k1_xboole_0 = u1_struct_0(k6_tmap_1(sK1,X0_55)) ),
% 47.37/6.56      inference(instantiation,[status(thm)],[c_3405]) ).
% 47.37/6.56  
% 47.37/6.56  cnf(c_66094,plain,
% 47.37/6.56      ( u1_struct_0(k6_tmap_1(sK1,sK2)) != k2_struct_0(sK1)
% 47.37/6.56      | k1_xboole_0 = u1_struct_0(k6_tmap_1(sK1,sK2))
% 47.37/6.56      | k1_xboole_0 != k2_struct_0(sK1) ),
% 47.37/6.56      inference(instantiation,[status(thm)],[c_64333]) ).
% 47.37/6.56  
% 47.37/6.56  cnf(c_4677,plain,
% 47.37/6.56      ( v1_funct_1(X0_55)
% 47.37/6.56      | ~ v1_funct_1(k7_tmap_1(sK1,sK2))
% 47.37/6.56      | X0_55 != k7_tmap_1(sK1,sK2) ),
% 47.37/6.56      inference(instantiation,[status(thm)],[c_3419]) ).
% 47.37/6.56  
% 47.37/6.56  cnf(c_14850,plain,
% 47.37/6.56      ( ~ v1_funct_1(k7_tmap_1(sK1,sK2))
% 47.37/6.56      | v1_funct_1(k6_partfun1(X0_57))
% 47.37/6.56      | k6_partfun1(X0_57) != k7_tmap_1(sK1,sK2) ),
% 47.37/6.56      inference(instantiation,[status(thm)],[c_4677]) ).
% 47.37/6.56  
% 47.37/6.56  cnf(c_14861,plain,
% 47.37/6.56      ( k6_partfun1(X0_57) != k7_tmap_1(sK1,sK2)
% 47.37/6.56      | v1_funct_1(k7_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.56      | v1_funct_1(k6_partfun1(X0_57)) = iProver_top ),
% 47.37/6.56      inference(predicate_to_equality,[status(thm)],[c_14850]) ).
% 47.37/6.56  
% 47.37/6.56  cnf(c_14863,plain,
% 47.37/6.56      ( k6_partfun1(k1_xboole_0) != k7_tmap_1(sK1,sK2)
% 47.37/6.56      | v1_funct_1(k7_tmap_1(sK1,sK2)) != iProver_top
% 47.37/6.56      | v1_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
% 47.37/6.56      inference(instantiation,[status(thm)],[c_14861]) ).
% 47.37/6.56  
% 47.37/6.56  cnf(c_5432,plain,
% 47.37/6.56      ( X0_57 != u1_struct_0(k6_tmap_1(sK1,X0_55))
% 47.37/6.56      | k1_zfmisc_1(X0_57) = k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0_55))) ),
% 47.37/6.56      inference(instantiation,[status(thm)],[c_3410]) ).
% 47.37/6.56  
% 47.37/6.56  cnf(c_5433,plain,
% 47.37/6.56      ( k1_xboole_0 != u1_struct_0(k6_tmap_1(sK1,sK2))
% 47.37/6.56      | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2))) ),
% 47.37/6.56      inference(instantiation,[status(thm)],[c_5432]) ).
% 47.37/6.56  
% 47.37/6.56  cnf(c_4629,plain,
% 47.37/6.56      ( m1_subset_1(X0_55,X0_56)
% 47.37/6.56      | ~ m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X1_55))))
% 47.37/6.56      | X0_56 != k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X1_55)))
% 47.37/6.56      | X0_55 != X1_55 ),
% 47.37/6.56      inference(instantiation,[status(thm)],[c_3411]) ).
% 47.37/6.56  
% 47.37/6.56  cnf(c_4777,plain,
% 47.37/6.56      ( m1_subset_1(X0_55,k1_zfmisc_1(X0_57))
% 47.37/6.56      | ~ m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X1_55))))
% 47.37/6.56      | k1_zfmisc_1(X0_57) != k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X1_55)))
% 47.37/6.56      | X0_55 != X1_55 ),
% 47.37/6.56      inference(instantiation,[status(thm)],[c_4629]) ).
% 47.37/6.56  
% 47.37/6.56  cnf(c_4778,plain,
% 47.37/6.56      ( k1_zfmisc_1(X0_57) != k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0_55)))
% 47.37/6.56      | X1_55 != X0_55
% 47.37/6.56      | m1_subset_1(X1_55,k1_zfmisc_1(X0_57)) = iProver_top
% 47.37/6.56      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,X0_55)))) != iProver_top ),
% 47.37/6.56      inference(predicate_to_equality,[status(thm)],[c_4777]) ).
% 47.37/6.56  
% 47.37/6.56  cnf(c_4780,plain,
% 47.37/6.56      ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))
% 47.37/6.56      | sK2 != sK2
% 47.37/6.56      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK1,sK2)))) != iProver_top
% 47.37/6.56      | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 47.37/6.56      inference(instantiation,[status(thm)],[c_4778]) ).
% 47.37/6.56  
% 47.37/6.56  cnf(contradiction,plain,
% 47.37/6.56      ( $false ),
% 47.37/6.56      inference(minisat,
% 47.37/6.56                [status(thm)],
% 47.37/6.56                [c_134576,c_98479,c_97361,c_90034,c_90017,c_90015,
% 47.37/6.56                 c_89489,c_87667,c_78479,c_66094,c_14863,c_5778,c_5776,
% 47.37/6.56                 c_5433,c_5050,c_4780,c_4505,c_4451,c_3529,c_3520,c_3513,
% 47.37/6.56                 c_3447,c_3445,c_42,c_35]) ).
% 47.37/6.56  
% 47.37/6.56  
% 47.37/6.56  % SZS output end CNFRefutation for theBenchmark.p
% 47.37/6.56  
% 47.37/6.56  ------                               Statistics
% 47.37/6.56  
% 47.37/6.56  ------ General
% 47.37/6.56  
% 47.37/6.56  abstr_ref_over_cycles:                  0
% 47.37/6.56  abstr_ref_under_cycles:                 0
% 47.37/6.56  gc_basic_clause_elim:                   0
% 47.37/6.56  forced_gc_time:                         0
% 47.37/6.56  parsing_time:                           0.009
% 47.37/6.56  unif_index_cands_time:                  0.
% 47.37/6.56  unif_index_add_time:                    0.
% 47.37/6.56  orderings_time:                         0.
% 47.37/6.56  out_proof_time:                         0.062
% 47.37/6.56  total_time:                             5.808
% 47.37/6.56  num_of_symbols:                         66
% 47.37/6.56  num_of_terms:                           61030
% 47.37/6.56  
% 47.37/6.56  ------ Preprocessing
% 47.37/6.56  
% 47.37/6.56  num_of_splits:                          0
% 47.37/6.56  num_of_split_atoms:                     0
% 47.37/6.56  num_of_reused_defs:                     0
% 47.37/6.56  num_eq_ax_congr_red:                    24
% 47.37/6.56  num_of_sem_filtered_clauses:            1
% 47.37/6.56  num_of_subtypes:                        5
% 47.37/6.56  monotx_restored_types:                  0
% 47.37/6.56  sat_num_of_epr_types:                   0
% 47.37/6.56  sat_num_of_non_cyclic_types:            0
% 47.37/6.56  sat_guarded_non_collapsed_types:        1
% 47.37/6.56  num_pure_diseq_elim:                    0
% 47.37/6.56  simp_replaced_by:                       0
% 47.37/6.56  res_preprocessed:                       199
% 47.37/6.56  prep_upred:                             0
% 47.37/6.56  prep_unflattend:                        74
% 47.37/6.56  smt_new_axioms:                         0
% 47.37/6.56  pred_elim_cands:                        7
% 47.37/6.56  pred_elim:                              3
% 47.37/6.56  pred_elim_cl:                           4
% 47.37/6.56  pred_elim_cycles:                       5
% 47.37/6.56  merged_defs:                            4
% 47.37/6.56  merged_defs_ncl:                        0
% 47.37/6.56  bin_hyper_res:                          4
% 47.37/6.56  prep_cycles:                            4
% 47.37/6.56  pred_elim_time:                         0.053
% 47.37/6.56  splitting_time:                         0.
% 47.37/6.56  sem_filter_time:                        0.
% 47.37/6.56  monotx_time:                            0.
% 47.37/6.56  subtype_inf_time:                       0.
% 47.37/6.56  
% 47.37/6.56  ------ Problem properties
% 47.37/6.56  
% 47.37/6.56  clauses:                                35
% 47.37/6.56  conjectures:                            8
% 47.37/6.56  epr:                                    2
% 47.37/6.56  horn:                                   25
% 47.37/6.56  ground:                                 11
% 47.37/6.56  unary:                                  6
% 47.37/6.56  binary:                                 15
% 47.37/6.56  lits:                                   140
% 47.37/6.56  lits_eq:                                16
% 47.37/6.56  fd_pure:                                0
% 47.37/6.56  fd_pseudo:                              0
% 47.37/6.56  fd_cond:                                0
% 47.37/6.56  fd_pseudo_cond:                         0
% 47.37/6.56  ac_symbols:                             0
% 47.37/6.56  
% 47.37/6.56  ------ Propositional Solver
% 47.37/6.56  
% 47.37/6.56  prop_solver_calls:                      51
% 47.37/6.56  prop_fast_solver_calls:                 22000
% 47.37/6.56  smt_solver_calls:                       0
% 47.37/6.56  smt_fast_solver_calls:                  0
% 47.37/6.56  prop_num_of_clauses:                    37020
% 47.37/6.56  prop_preprocess_simplified:             102149
% 47.37/6.56  prop_fo_subsumed:                       5812
% 47.37/6.56  prop_solver_time:                       0.
% 47.37/6.56  smt_solver_time:                        0.
% 47.37/6.56  smt_fast_solver_time:                   0.
% 47.37/6.56  prop_fast_solver_time:                  0.
% 47.37/6.56  prop_unsat_core_time:                   0.003
% 47.37/6.56  
% 47.37/6.56  ------ QBF
% 47.37/6.56  
% 47.37/6.56  qbf_q_res:                              0
% 47.37/6.56  qbf_num_tautologies:                    0
% 47.37/6.56  qbf_prep_cycles:                        0
% 47.37/6.56  
% 47.37/6.56  ------ BMC1
% 47.37/6.56  
% 47.37/6.56  bmc1_current_bound:                     -1
% 47.37/6.56  bmc1_last_solved_bound:                 -1
% 47.37/6.56  bmc1_unsat_core_size:                   -1
% 47.37/6.56  bmc1_unsat_core_parents_size:           -1
% 47.37/6.56  bmc1_merge_next_fun:                    0
% 47.37/6.56  bmc1_unsat_core_clauses_time:           0.
% 47.37/6.56  
% 47.37/6.56  ------ Instantiation
% 47.37/6.56  
% 47.37/6.56  inst_num_of_clauses:                    7710
% 47.37/6.56  inst_num_in_passive:                    3141
% 47.37/6.56  inst_num_in_active:                     4750
% 47.37/6.56  inst_num_in_unprocessed:                1738
% 47.37/6.56  inst_num_of_loops:                      6419
% 47.37/6.56  inst_num_of_learning_restarts:          1
% 47.37/6.56  inst_num_moves_active_passive:          1655
% 47.37/6.56  inst_lit_activity:                      0
% 47.37/6.56  inst_lit_activity_moves:                1
% 47.37/6.56  inst_num_tautologies:                   0
% 47.37/6.56  inst_num_prop_implied:                  0
% 47.37/6.56  inst_num_existing_simplified:           0
% 47.37/6.56  inst_num_eq_res_simplified:             0
% 47.37/6.56  inst_num_child_elim:                    0
% 47.37/6.56  inst_num_of_dismatching_blockings:      17077
% 47.37/6.56  inst_num_of_non_proper_insts:           19942
% 47.37/6.56  inst_num_of_duplicates:                 0
% 47.37/6.56  inst_inst_num_from_inst_to_res:         0
% 47.37/6.56  inst_dismatching_checking_time:         0.
% 47.37/6.56  
% 47.37/6.56  ------ Resolution
% 47.37/6.56  
% 47.37/6.56  res_num_of_clauses:                     62
% 47.37/6.56  res_num_in_passive:                     62
% 47.37/6.56  res_num_in_active:                      0
% 47.37/6.56  res_num_of_loops:                       203
% 47.37/6.56  res_forward_subset_subsumed:            742
% 47.37/6.56  res_backward_subset_subsumed:           0
% 47.37/6.56  res_forward_subsumed:                   0
% 47.37/6.56  res_backward_subsumed:                  0
% 47.37/6.56  res_forward_subsumption_resolution:     0
% 47.37/6.56  res_backward_subsumption_resolution:    0
% 47.37/6.56  res_clause_to_clause_subsumption:       8734
% 47.37/6.56  res_orphan_elimination:                 0
% 47.37/6.56  res_tautology_del:                      2368
% 47.37/6.56  res_num_eq_res_simplified:              0
% 47.37/6.56  res_num_sel_changes:                    0
% 47.37/6.56  res_moves_from_active_to_pass:          0
% 47.37/6.56  
% 47.37/6.56  ------ Superposition
% 47.37/6.56  
% 47.37/6.56  sup_time_total:                         0.
% 47.37/6.56  sup_time_generating:                    0.
% 47.37/6.56  sup_time_sim_full:                      0.
% 47.37/6.56  sup_time_sim_immed:                     0.
% 47.37/6.56  
% 47.37/6.56  sup_num_of_clauses:                     478
% 47.37/6.56  sup_num_in_active:                      313
% 47.37/6.56  sup_num_in_passive:                     165
% 47.37/6.56  sup_num_of_loops:                       1282
% 47.37/6.56  sup_fw_superposition:                   2052
% 47.37/6.56  sup_bw_superposition:                   1272
% 47.37/6.56  sup_immediate_simplified:               866
% 47.37/6.56  sup_given_eliminated:                   16
% 47.37/6.56  comparisons_done:                       0
% 47.37/6.56  comparisons_avoided:                    1413
% 47.37/6.56  
% 47.37/6.56  ------ Simplifications
% 47.37/6.56  
% 47.37/6.56  
% 47.37/6.56  sim_fw_subset_subsumed:                 142
% 47.37/6.56  sim_bw_subset_subsumed:                 779
% 47.37/6.56  sim_fw_subsumed:                        179
% 47.37/6.56  sim_bw_subsumed:                        82
% 47.37/6.56  sim_fw_subsumption_res:                 0
% 47.37/6.56  sim_bw_subsumption_res:                 0
% 47.37/6.56  sim_tautology_del:                      103
% 47.37/6.56  sim_eq_tautology_del:                   485
% 47.37/6.56  sim_eq_res_simp:                        4
% 47.37/6.56  sim_fw_demodulated:                     98
% 47.37/6.56  sim_bw_demodulated:                     582
% 47.37/6.56  sim_light_normalised:                   623
% 47.37/6.56  sim_joinable_taut:                      0
% 47.37/6.56  sim_joinable_simp:                      0
% 47.37/6.56  sim_ac_normalised:                      0
% 47.37/6.56  sim_smt_subsumption:                    0
% 47.37/6.56  
%------------------------------------------------------------------------------
