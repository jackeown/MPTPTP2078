%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:13 EST 2020

% Result     : Theorem 4.08s
% Output     : CNFRefutation 4.08s
% Verified   : 
% Statistics : Number of formulae       :  374 (86226 expanded)
%              Number of clauses        :  273 (21225 expanded)
%              Number of leaves         :   20 (18636 expanded)
%              Depth                    :   40
%              Number of atoms          : 1900 (848959 expanded)
%              Number of equality atoms :  564 (38681 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    9 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f99,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f16,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f61,plain,(
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
    inference(nnf_transformation,[],[f46])).

fof(f62,plain,(
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
    inference(flattening,[],[f61])).

fof(f64,plain,(
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

fof(f63,plain,
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

fof(f65,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f62,f64,f63])).

fof(f112,plain,
    ( m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f65])).

fof(f104,plain,(
    m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f65])).

fof(f103,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f65])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f101,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f65])).

fof(f102,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f65])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f48,plain,(
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
    inference(rectify,[],[f47])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k6_tmap_1(X0,X3) != X2
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k6_tmap_1(X0,sK0(X0,X1,X2)) != X2
        & u1_struct_0(X1) = sK0(X0,X1,X2)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f48,f49])).

fof(f70,plain,(
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
    inference(cnf_transformation,[],[f50])).

fof(f114,plain,(
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
    inference(equality_resolution,[],[f70])).

fof(f115,plain,(
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
    inference(equality_resolution,[],[f114])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f86,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f87,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f91,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f100,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f52,plain,(
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
    inference(rectify,[],[f51])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2)))
        & u1_struct_0(X1) = sK1(X0,X1,X2)
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f52,f53])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k9_tmap_1(X0,X1) = X2
      | u1_struct_0(X1) = sK1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

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
     => r1_funct_2(X0,X1,X2,X3,X4,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f21])).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k9_tmap_1(X0,X1) = X2
      | ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f66,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k9_tmap_1(X0,X1) = X2
      | m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f90,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f88,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k9_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f89,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f74,plain,(
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
    inference(cnf_transformation,[],[f54])).

fof(f116,plain,(
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
    inference(equality_resolution,[],[f74])).

fof(f117,plain,(
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
    inference(equality_resolution,[],[f116])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f12])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f59,plain,(
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
    inference(nnf_transformation,[],[f40])).

fof(f60,plain,(
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
    inference(flattening,[],[f59])).

fof(f97,plain,(
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
    inference(cnf_transformation,[],[f60])).

fof(f109,plain,
    ( v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4))
    | v1_tsep_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f65])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f55,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f56,plain,(
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
    inference(rectify,[],[f55])).

fof(f57,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK2(X0,X1),X0)
        & u1_struct_0(X1) = sK2(X0,X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f56,f57])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(sK2(X0,X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f95,plain,(
    ! [X0,X1] :
      ( v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f113,plain,
    ( ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4))
    | ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
    | ~ m1_pre_topc(sK4,sK3)
    | ~ v1_tsep_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f65])).

fof(f78,plain,(
    ! [X0,X3,X1] :
      ( v3_pre_topc(X3,X0)
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f118,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f78])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | u1_struct_0(X1) = sK2(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_33,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_36,negated_conjecture,
    ( m1_pre_topc(sK4,sK3)
    | m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_44,negated_conjecture,
    ( m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_286,negated_conjecture,
    ( m1_pre_topc(sK4,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_36,c_44])).

cnf(c_1914,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK4 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_286])).

cnf(c_1915,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1914])).

cnf(c_45,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1917,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1915,c_45])).

cnf(c_4232,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subtyping,[status(esa)],[c_1917])).

cnf(c_5003,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4232])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_47,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_3644,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_47])).

cnf(c_3645,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | k7_tmap_1(sK3,X0) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_3644])).

cnf(c_46,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_3649,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k7_tmap_1(sK3,X0) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3645,c_46,c_45])).

cnf(c_4206,plain,
    ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK3)))
    | k7_tmap_1(sK3,X0_58) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_3649])).

cnf(c_5028,plain,
    ( k7_tmap_1(sK3,X0_58) = k6_partfun1(u1_struct_0(sK3))
    | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4206])).

cnf(c_5860,plain,
    ( k7_tmap_1(sK3,u1_struct_0(sK4)) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(superposition,[status(thm)],[c_5003,c_5028])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_3626,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_47])).

cnf(c_3627,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_3626])).

cnf(c_3631,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3627,c_46,c_45])).

cnf(c_4207,plain,
    ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k7_tmap_1(sK3,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0_58))))) ),
    inference(subtyping,[status(esa)],[c_3631])).

cnf(c_5027,plain,
    ( m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK3,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0_58))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4207])).

cnf(c_6907,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))))) = iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5860,c_5027])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(k8_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(k8_tmap_1(X1,X0))
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_21,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_20,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k8_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_19,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_353,plain,
    ( ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7,c_33,c_21,c_20,c_19])).

cnf(c_354,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(renaming,[status(thm)],[c_353])).

cnf(c_1892,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k6_tmap_1(X0,u1_struct_0(X1)) = k8_tmap_1(X0,X1)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_354,c_286])).

cnf(c_1893,plain,
    ( ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_1892])).

cnf(c_1895,plain,
    ( k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1893,c_47,c_46,c_45])).

cnf(c_4233,plain,
    ( k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4) ),
    inference(subtyping,[status(esa)],[c_1895])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_3572,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_47])).

cnf(c_3573,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | u1_struct_0(k6_tmap_1(sK3,X0)) = u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_3572])).

cnf(c_3577,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | u1_struct_0(k6_tmap_1(sK3,X0)) = u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3573,c_46,c_45])).

cnf(c_4210,plain,
    ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK3)))
    | u1_struct_0(k6_tmap_1(sK3,X0_58)) = u1_struct_0(sK3) ),
    inference(subtyping,[status(esa)],[c_3577])).

cnf(c_5024,plain,
    ( u1_struct_0(k6_tmap_1(sK3,X0_58)) = u1_struct_0(sK3)
    | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4210])).

cnf(c_5719,plain,
    ( u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))) = u1_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_5003,c_5024])).

cnf(c_5721,plain,
    ( u1_struct_0(k8_tmap_1(sK3,sK4)) = u1_struct_0(sK3) ),
    inference(light_normalisation,[status(thm)],[c_5719,c_4233])).

cnf(c_6916,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) = iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6907,c_4233,c_5721])).

cnf(c_50,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_34,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_61,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_63,plain,
    ( m1_pre_topc(sK3,sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_61])).

cnf(c_64,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_66,plain,
    ( m1_pre_topc(sK3,sK3) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_64])).

cnf(c_1637,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | X1 != X0
    | X1 != X2
    | k6_tmap_1(X0,u1_struct_0(X2)) = k8_tmap_1(X0,X2) ),
    inference(resolution_lifted,[status(thm)],[c_354,c_34])).

cnf(c_1638,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k6_tmap_1(X0,u1_struct_0(X0)) = k8_tmap_1(X0,X0) ),
    inference(unflattening,[status(thm)],[c_1637])).

cnf(c_3371,plain,
    ( ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k6_tmap_1(X0,u1_struct_0(X0)) = k8_tmap_1(X0,X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1638,c_47])).

cnf(c_3372,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | k6_tmap_1(sK3,u1_struct_0(sK3)) = k8_tmap_1(sK3,sK3) ),
    inference(unflattening,[status(thm)],[c_3371])).

cnf(c_62,plain,
    ( m1_pre_topc(sK3,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_65,plain,
    ( ~ m1_pre_topc(sK3,sK3)
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_101,plain,
    ( ~ m1_pre_topc(sK3,sK3)
    | v1_pre_topc(k8_tmap_1(sK3,sK3))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_104,plain,
    ( ~ m1_pre_topc(sK3,sK3)
    | v2_pre_topc(k8_tmap_1(sK3,sK3))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_107,plain,
    ( ~ m1_pre_topc(sK3,sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | l1_pre_topc(k8_tmap_1(sK3,sK3))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_143,plain,
    ( ~ m1_pre_topc(sK3,sK3)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_pre_topc(k8_tmap_1(sK3,sK3))
    | ~ v2_pre_topc(k8_tmap_1(sK3,sK3))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(k8_tmap_1(sK3,sK3))
    | ~ l1_pre_topc(sK3)
    | k6_tmap_1(sK3,u1_struct_0(sK3)) = k8_tmap_1(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_3374,plain,
    ( k6_tmap_1(sK3,u1_struct_0(sK3)) = k8_tmap_1(sK3,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3372,c_47,c_46,c_45,c_62,c_65,c_101,c_104,c_107,c_143])).

cnf(c_4216,plain,
    ( k6_tmap_1(sK3,u1_struct_0(sK3)) = k8_tmap_1(sK3,sK3) ),
    inference(subtyping,[status(esa)],[c_3374])).

cnf(c_6365,plain,
    ( m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))))) = iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4216,c_5027])).

cnf(c_1670,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | X2 != X1
    | X2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_34])).

cnf(c_1671,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_1670])).

cnf(c_3865,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1671,c_45])).

cnf(c_3866,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unflattening,[status(thm)],[c_3865])).

cnf(c_4197,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subtyping,[status(esa)],[c_3866])).

cnf(c_5033,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4197])).

cnf(c_5717,plain,
    ( u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3))) = u1_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_5033,c_5024])).

cnf(c_5728,plain,
    ( u1_struct_0(k8_tmap_1(sK3,sK3)) = u1_struct_0(sK3) ),
    inference(light_normalisation,[status(thm)],[c_5717,c_4216])).

cnf(c_5858,plain,
    ( k7_tmap_1(sK3,u1_struct_0(sK3)) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(superposition,[status(thm)],[c_5033,c_5028])).

cnf(c_6374,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) = iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6365,c_5728,c_5858])).

cnf(c_7000,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6916,c_50,c_63,c_66,c_6374])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK1(X1,X2,X0) = u1_struct_0(X2)
    | k9_tmap_1(X1,X2) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2125,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | X3 != X1
    | X3 != X2
    | sK1(X1,X2,X0) = u1_struct_0(X2)
    | k9_tmap_1(X1,X2) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_34])).

cnf(c_2126,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK1(X1,X1,X0) = u1_struct_0(X1)
    | k9_tmap_1(X1,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_2125])).

cnf(c_3468,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | sK1(X1,X1,X0) = u1_struct_0(X1)
    | k9_tmap_1(X1,X1) = X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2126,c_47])).

cnf(c_3469,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(sK3)
    | sK1(sK3,sK3,X0) = u1_struct_0(sK3)
    | k9_tmap_1(sK3,sK3) = X0 ),
    inference(unflattening,[status(thm)],[c_3468])).

cnf(c_3473,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
    | sK1(sK3,sK3,X0) = u1_struct_0(sK3)
    | k9_tmap_1(sK3,sK3) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3469,c_46,c_45])).

cnf(c_3474,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
    | ~ v1_funct_1(X0)
    | sK1(sK3,sK3,X0) = u1_struct_0(sK3)
    | k9_tmap_1(sK3,sK3) = X0 ),
    inference(renaming,[status(thm)],[c_3473])).

cnf(c_4212,plain,
    ( ~ v1_funct_2(X0_58,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
    | ~ v1_funct_1(X0_58)
    | sK1(sK3,sK3,X0_58) = u1_struct_0(sK3)
    | k9_tmap_1(sK3,sK3) = X0_58 ),
    inference(subtyping,[status(esa)],[c_3474])).

cnf(c_5022,plain,
    ( sK1(sK3,sK3,X0_58) = u1_struct_0(sK3)
    | k9_tmap_1(sK3,sK3) = X0_58
    | v1_funct_2(X0_58,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))) != iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))))) != iProver_top
    | v1_funct_1(X0_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4212])).

cnf(c_6771,plain,
    ( sK1(sK3,sK3,X0_58) = u1_struct_0(sK3)
    | k9_tmap_1(sK3,sK3) = X0_58
    | v1_funct_2(X0_58,u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X0_58) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5022,c_5728])).

cnf(c_7007,plain,
    ( sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3))) = u1_struct_0(sK3)
    | k9_tmap_1(sK3,sK3) = k6_partfun1(u1_struct_0(sK3))
    | v1_funct_2(k6_partfun1(u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
    | v1_funct_1(k6_partfun1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7000,c_6771])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k7_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_3608,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k7_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_47])).

cnf(c_3609,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | v1_funct_1(k7_tmap_1(sK3,X0))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_3608])).

cnf(c_3613,plain,
    ( v1_funct_1(k7_tmap_1(sK3,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3609,c_46,c_45])).

cnf(c_3614,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_funct_1(k7_tmap_1(sK3,X0)) ),
    inference(renaming,[status(thm)],[c_3613])).

cnf(c_4208,plain,
    ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_funct_1(k7_tmap_1(sK3,X0_58)) ),
    inference(subtyping,[status(esa)],[c_3614])).

cnf(c_5026,plain,
    ( m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK3,X0_58)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4208])).

cnf(c_5700,plain,
    ( v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5033,c_5026])).

cnf(c_5988,plain,
    ( v1_funct_1(k6_partfun1(u1_struct_0(sK3))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5858,c_5700])).

cnf(c_17,plain,
    ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_3450,plain,
    ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_47])).

cnf(c_3451,plain,
    ( v1_funct_2(k7_tmap_1(sK3,X0),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_3450])).

cnf(c_3455,plain,
    ( v1_funct_2(k7_tmap_1(sK3,X0),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3451,c_46,c_45])).

cnf(c_4213,plain,
    ( v1_funct_2(k7_tmap_1(sK3,X0_58),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0_58)))
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subtyping,[status(esa)],[c_3455])).

cnf(c_5021,plain,
    ( v1_funct_2(k7_tmap_1(sK3,X0_58),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0_58))) = iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4213])).

cnf(c_6344,plain,
    ( v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))) = iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4216,c_5021])).

cnf(c_6353,plain,
    ( v1_funct_2(k6_partfun1(u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6344,c_5728,c_5858])).

cnf(c_9052,plain,
    ( sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3))) = u1_struct_0(sK3)
    | k9_tmap_1(sK3,sK3) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7007,c_50,c_63,c_66,c_5988,c_6353])).

cnf(c_2,plain,
    ( r1_funct_2(X0,X1,X2,X3,X4,X4)
    | ~ v1_funct_2(X5,X2,X3)
    | ~ v1_funct_2(X4,X0,X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_8,plain,
    ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2)))
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k9_tmap_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1521,plain,
    ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2)))
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X3)
    | X3 != X1
    | X3 != X0
    | k9_tmap_1(X0,X1) = X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_34])).

cnf(c_1522,plain,
    ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X0,X1))),X1,k7_tmap_1(X0,sK1(X0,X0,X1)))
    | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k9_tmap_1(X0,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_1521])).

cnf(c_3379,plain,
    ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X0,X1))),X1,k7_tmap_1(X0,sK1(X0,X0,X1)))
    | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(X1)
    | ~ l1_pre_topc(X0)
    | k9_tmap_1(X0,X0) = X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1522,c_47])).

cnf(c_3380,plain,
    ( ~ r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X0))),X0,k7_tmap_1(sK3,sK1(sK3,sK3,X0)))
    | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(sK3)
    | k9_tmap_1(sK3,sK3) = X0 ),
    inference(unflattening,[status(thm)],[c_3379])).

cnf(c_3384,plain,
    ( ~ v1_funct_1(X0)
    | ~ r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X0))),X0,k7_tmap_1(sK3,sK1(sK3,sK3,X0)))
    | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
    | k9_tmap_1(sK3,sK3) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3380,c_46,c_45])).

cnf(c_3385,plain,
    ( ~ r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X0))),X0,k7_tmap_1(sK3,sK1(sK3,sK3,X0)))
    | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
    | ~ v1_funct_1(X0)
    | k9_tmap_1(sK3,sK3) = X0 ),
    inference(renaming,[status(thm)],[c_3384])).

cnf(c_3984,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X5)
    | ~ v1_funct_2(X6,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X6)
    | v1_xboole_0(X5)
    | v1_xboole_0(X2)
    | X6 != X3
    | k9_tmap_1(sK3,sK3) = X6
    | k7_tmap_1(sK3,sK1(sK3,sK3,X6)) != X3
    | u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X6))) != X2
    | u1_struct_0(k8_tmap_1(sK3,sK3)) != X5
    | u1_struct_0(sK3) != X1
    | u1_struct_0(sK3) != X4 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_3385])).

cnf(c_3985,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X1))))
    | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X1))))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X1))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK3)))
    | k9_tmap_1(sK3,sK3) = X1
    | k7_tmap_1(sK3,sK1(sK3,sK3,X1)) != X1 ),
    inference(unflattening,[status(thm)],[c_3984])).

cnf(c_4190,plain,
    ( ~ v1_funct_2(X0_58,u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X1_58))))
    | ~ v1_funct_2(X1_58,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X1_58))))))
    | ~ m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
    | ~ v1_funct_1(X0_58)
    | ~ v1_funct_1(X1_58)
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X1_58))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK3)))
    | k9_tmap_1(sK3,sK3) = X1_58
    | k7_tmap_1(sK3,sK1(sK3,sK3,X1_58)) != X1_58 ),
    inference(subtyping,[status(esa)],[c_3985])).

cnf(c_5040,plain,
    ( k9_tmap_1(sK3,sK3) = X0_58
    | k7_tmap_1(sK3,sK1(sK3,sK3,X0_58)) != X0_58
    | v1_funct_2(X1_58,u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X0_58)))) != iProver_top
    | v1_funct_2(X0_58,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))) != iProver_top
    | m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X0_58)))))) != iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))))) != iProver_top
    | v1_funct_1(X0_58) != iProver_top
    | v1_funct_1(X1_58) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X0_58)))) = iProver_top
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4190])).

cnf(c_5813,plain,
    ( k9_tmap_1(sK3,sK3) = X0_58
    | k7_tmap_1(sK3,sK1(sK3,sK3,X0_58)) != X0_58
    | v1_funct_2(X1_58,u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X0_58)))) != iProver_top
    | v1_funct_2(X0_58,u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X0_58)))))) != iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X1_58) != iProver_top
    | v1_funct_1(X0_58) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X0_58)))) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5728,c_5040])).

cnf(c_48,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_1,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f67])).

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

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_163,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_165,plain,
    ( l1_pre_topc(sK3) != iProver_top
    | l1_struct_0(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_163])).

cnf(c_6957,plain,
    ( v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X0_58)))) = iProver_top
    | v1_funct_1(X0_58) != iProver_top
    | v1_funct_1(X1_58) != iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X0_58)))))) != iProver_top
    | v1_funct_2(X0_58,u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(X1_58,u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X0_58)))) != iProver_top
    | k7_tmap_1(sK3,sK1(sK3,sK3,X0_58)) != X0_58
    | k9_tmap_1(sK3,sK3) = X0_58 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5813,c_48,c_50,c_162,c_165])).

cnf(c_6958,plain,
    ( k9_tmap_1(sK3,sK3) = X0_58
    | k7_tmap_1(sK3,sK1(sK3,sK3,X0_58)) != X0_58
    | v1_funct_2(X1_58,u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X0_58)))) != iProver_top
    | v1_funct_2(X0_58,u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X0_58)))))) != iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X1_58) != iProver_top
    | v1_funct_1(X0_58) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X0_58)))) = iProver_top ),
    inference(renaming,[status(thm)],[c_6957])).

cnf(c_9056,plain,
    ( k9_tmap_1(sK3,sK3) = k6_partfun1(u1_struct_0(sK3))
    | k7_tmap_1(sK3,u1_struct_0(sK3)) != k6_partfun1(u1_struct_0(sK3))
    | v1_funct_2(X0_58,u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))) != iProver_top
    | v1_funct_2(k6_partfun1(u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))))) != iProver_top
    | m1_subset_1(k6_partfun1(u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X0_58) != iProver_top
    | v1_funct_1(k6_partfun1(u1_struct_0(sK3))) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_9052,c_6958])).

cnf(c_9057,plain,
    ( k9_tmap_1(sK3,sK3) = k6_partfun1(u1_struct_0(sK3))
    | k6_partfun1(u1_struct_0(sK3)) != k6_partfun1(u1_struct_0(sK3))
    | v1_funct_2(X0_58,u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))) != iProver_top
    | v1_funct_2(k6_partfun1(u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))))) != iProver_top
    | m1_subset_1(k6_partfun1(u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X0_58) != iProver_top
    | v1_funct_1(k6_partfun1(u1_struct_0(sK3))) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9056,c_5858])).

cnf(c_9058,plain,
    ( k9_tmap_1(sK3,sK3) = k6_partfun1(u1_struct_0(sK3))
    | v1_funct_2(X0_58,u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))) != iProver_top
    | v1_funct_2(k6_partfun1(u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))))) != iProver_top
    | m1_subset_1(k6_partfun1(u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X0_58) != iProver_top
    | v1_funct_1(k6_partfun1(u1_struct_0(sK3))) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_9057])).

cnf(c_12822,plain,
    ( v1_funct_1(X0_58) != iProver_top
    | v1_funct_2(X0_58,u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))) != iProver_top
    | k9_tmap_1(sK3,sK3) = k6_partfun1(u1_struct_0(sK3))
    | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))))) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9058,c_50,c_63,c_66,c_5988,c_6353,c_6374])).

cnf(c_12823,plain,
    ( k9_tmap_1(sK3,sK3) = k6_partfun1(u1_struct_0(sK3))
    | v1_funct_2(X0_58,u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))) != iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))))) != iProver_top
    | v1_funct_1(X0_58) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))) = iProver_top ),
    inference(renaming,[status(thm)],[c_12822])).

cnf(c_12836,plain,
    ( k9_tmap_1(sK3,sK3) = k6_partfun1(u1_struct_0(sK3))
    | v1_funct_2(X0_58,u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))) != iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3)))))) != iProver_top
    | v1_funct_1(X0_58) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_9052,c_12823])).

cnf(c_12842,plain,
    ( k9_tmap_1(sK3,sK3) = k6_partfun1(u1_struct_0(sK3))
    | v1_funct_2(X0_58,u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))) != iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X0_58) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12836,c_4216,c_5728])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k9_tmap_1(X1,X2) = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2095,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | X3 != X1
    | X3 != X2
    | k9_tmap_1(X1,X2) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_34])).

cnf(c_2096,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))))
    | m1_subset_1(sK1(X1,X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k9_tmap_1(X1,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_2095])).

cnf(c_3495,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))))
    | m1_subset_1(sK1(X1,X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | k9_tmap_1(X1,X1) = X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2096,c_47])).

cnf(c_3496,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
    | m1_subset_1(sK1(sK3,sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(sK3)
    | k9_tmap_1(sK3,sK3) = X0 ),
    inference(unflattening,[status(thm)],[c_3495])).

cnf(c_3500,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
    | m1_subset_1(sK1(sK3,sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | k9_tmap_1(sK3,sK3) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3496,c_46,c_45])).

cnf(c_3501,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
    | m1_subset_1(sK1(sK3,sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_funct_1(X0)
    | k9_tmap_1(sK3,sK3) = X0 ),
    inference(renaming,[status(thm)],[c_3500])).

cnf(c_4211,plain,
    ( ~ v1_funct_2(X0_58,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
    | m1_subset_1(sK1(sK3,sK3,X0_58),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_funct_1(X0_58)
    | k9_tmap_1(sK3,sK3) = X0_58 ),
    inference(subtyping,[status(esa)],[c_3501])).

cnf(c_5023,plain,
    ( k9_tmap_1(sK3,sK3) = X0_58
    | v1_funct_2(X0_58,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))) != iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))))) != iProver_top
    | m1_subset_1(sK1(sK3,sK3,X0_58),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | v1_funct_1(X0_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4211])).

cnf(c_6865,plain,
    ( k9_tmap_1(sK3,sK3) = X0_58
    | v1_funct_2(X0_58,u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK1(sK3,sK3,X0_58),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | v1_funct_1(X0_58) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5023,c_5728])).

cnf(c_7005,plain,
    ( k9_tmap_1(sK3,sK3) = k6_partfun1(u1_struct_0(sK3))
    | v1_funct_2(k6_partfun1(u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | v1_funct_1(k6_partfun1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7000,c_6865])).

cnf(c_9531,plain,
    ( m1_subset_1(sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | k9_tmap_1(sK3,sK3) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7005,c_50,c_63,c_66,c_5988,c_6353])).

cnf(c_9532,plain,
    ( k9_tmap_1(sK3,sK3) = k6_partfun1(u1_struct_0(sK3))
    | m1_subset_1(sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(renaming,[status(thm)],[c_9531])).

cnf(c_9539,plain,
    ( k9_tmap_1(sK3,sK3) = k6_partfun1(u1_struct_0(sK3))
    | k7_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(superposition,[status(thm)],[c_9532,c_5028])).

cnf(c_9610,plain,
    ( k9_tmap_1(sK3,sK3) = k6_partfun1(u1_struct_0(sK3))
    | v1_funct_2(k6_partfun1(u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))) = iProver_top
    | m1_subset_1(sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9539,c_5021])).

cnf(c_10684,plain,
    ( v1_funct_2(k6_partfun1(u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))) = iProver_top
    | k9_tmap_1(sK3,sK3) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9610,c_9532])).

cnf(c_10685,plain,
    ( k9_tmap_1(sK3,sK3) = k6_partfun1(u1_struct_0(sK3))
    | v1_funct_2(k6_partfun1(u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))) = iProver_top ),
    inference(renaming,[status(thm)],[c_10684])).

cnf(c_9609,plain,
    ( k9_tmap_1(sK3,sK3) = k6_partfun1(u1_struct_0(sK3))
    | m1_subset_1(sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(k6_partfun1(u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_9539,c_5027])).

cnf(c_11621,plain,
    ( k9_tmap_1(sK3,sK3) = k6_partfun1(u1_struct_0(sK3))
    | m1_subset_1(k6_partfun1(u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9609,c_9532])).

cnf(c_12834,plain,
    ( k9_tmap_1(sK3,sK3) = k6_partfun1(u1_struct_0(sK3))
    | v1_funct_2(k6_partfun1(u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))) != iProver_top
    | v1_funct_1(k6_partfun1(u1_struct_0(sK3))) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_11621,c_12823])).

cnf(c_12872,plain,
    ( k9_tmap_1(sK3,sK3) = k6_partfun1(u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12842,c_5988,c_10685,c_12834])).

cnf(c_12879,plain,
    ( k9_tmap_1(sK3,sK3) = k6_partfun1(u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_9052,c_12872])).

cnf(c_12882,plain,
    ( k9_tmap_1(sK3,sK3) = k6_partfun1(u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12879,c_4216,c_5728])).

cnf(c_13015,plain,
    ( k9_tmap_1(sK3,sK3) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12882,c_48,c_50,c_162,c_165])).

cnf(c_22,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(k9_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X0)))))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1940,plain,
    ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_286])).

cnf(c_1941,plain,
    ( m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1940])).

cnf(c_1943,plain,
    ( m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1941,c_47,c_46,c_45])).

cnf(c_4230,plain,
    ( m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) ),
    inference(subtyping,[status(esa)],[c_1943])).

cnf(c_5005,plain,
    ( m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4230])).

cnf(c_5778,plain,
    ( m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5721,c_5005])).

cnf(c_7130,plain,
    ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK3,sK4)
    | v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK1(sK3,sK3,k9_tmap_1(sK3,sK4)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | v1_funct_1(k9_tmap_1(sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5778,c_6865])).

cnf(c_49,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_24,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k9_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1927,plain,
    ( ~ v2_pre_topc(X0)
    | v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_286])).

cnf(c_1928,plain,
    ( ~ v2_pre_topc(sK3)
    | v1_funct_1(k9_tmap_1(sK3,sK4))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1927])).

cnf(c_1929,plain,
    ( v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(k9_tmap_1(sK3,sK4)) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1928])).

cnf(c_23,plain,
    ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1585,plain,
    ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_286])).

cnf(c_1586,plain,
    ( v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1585])).

cnf(c_1588,plain,
    ( v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1586,c_47,c_46,c_45])).

cnf(c_4234,plain,
    ( v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) ),
    inference(subtyping,[status(esa)],[c_1588])).

cnf(c_5002,plain,
    ( v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4234])).

cnf(c_5780,plain,
    ( v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5721,c_5002])).

cnf(c_11388,plain,
    ( m1_subset_1(sK1(sK3,sK3,k9_tmap_1(sK3,sK4)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | k9_tmap_1(sK3,sK3) = k9_tmap_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7130,c_48,c_49,c_50,c_1929,c_5780])).

cnf(c_11389,plain,
    ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK3,sK4)
    | m1_subset_1(sK1(sK3,sK3,k9_tmap_1(sK3,sK4)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(renaming,[status(thm)],[c_11388])).

cnf(c_11395,plain,
    ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK3,sK4))) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(superposition,[status(thm)],[c_11389,c_5028])).

cnf(c_1930,plain,
    ( v1_funct_1(k9_tmap_1(sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1928,c_47,c_46,c_45])).

cnf(c_11,plain,
    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
    | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_343,plain,
    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_23])).

cnf(c_1551,plain,
    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
    | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_343,c_286])).

cnf(c_1552,plain,
    ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1551])).

cnf(c_1554,plain,
    ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1552,c_47,c_46,c_45])).

cnf(c_1555,plain,
    ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4)) ),
    inference(renaming,[status(thm)],[c_1554])).

cnf(c_1924,plain,
    ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1917,c_1555])).

cnf(c_1937,plain,
    ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1930,c_1924])).

cnf(c_1950,plain,
    ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1943,c_1937])).

cnf(c_4078,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
    | ~ v1_funct_1(X0)
    | k9_tmap_1(sK3,sK4) != X0
    | k9_tmap_1(sK3,sK3) = X0
    | k7_tmap_1(sK3,sK1(sK3,sK3,X0)) != k7_tmap_1(sK3,u1_struct_0(sK4))
    | u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X0))) != u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))
    | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(k8_tmap_1(sK3,sK4))
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(resolution_lifted,[status(thm)],[c_1950,c_3385])).

cnf(c_4079,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
    | k9_tmap_1(sK3,sK3) = k9_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK3,sK4))) != k7_tmap_1(sK3,u1_struct_0(sK4))
    | u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK3,sK4)))) != u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))
    | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(k8_tmap_1(sK3,sK4)) ),
    inference(unflattening,[status(thm)],[c_4078])).

cnf(c_4081,plain,
    ( ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
    | ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
    | k9_tmap_1(sK3,sK3) = k9_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK3,sK4))) != k7_tmap_1(sK3,u1_struct_0(sK4))
    | u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK3,sK4)))) != u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))
    | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(k8_tmap_1(sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4079,c_47,c_46,c_45,c_1928])).

cnf(c_4082,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
    | k9_tmap_1(sK3,sK3) = k9_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK3,sK4))) != k7_tmap_1(sK3,u1_struct_0(sK4))
    | u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK3,sK4)))) != u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))
    | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(k8_tmap_1(sK3,sK4)) ),
    inference(renaming,[status(thm)],[c_4081])).

cnf(c_4187,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
    | k9_tmap_1(sK3,sK3) = k9_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK3,sK4))) != k7_tmap_1(sK3,u1_struct_0(sK4))
    | u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK3,sK4)))) != u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))
    | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(k8_tmap_1(sK3,sK4)) ),
    inference(subtyping,[status(esa)],[c_4082])).

cnf(c_5043,plain,
    ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK3,sK4))) != k7_tmap_1(sK3,u1_struct_0(sK4))
    | u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK3,sK4)))) != u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))
    | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(k8_tmap_1(sK3,sK4))
    | v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))) != iProver_top
    | m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4187])).

cnf(c_5263,plain,
    ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK3,sK4))) != k7_tmap_1(sK3,u1_struct_0(sK4))
    | u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK3,sK4)))) != u1_struct_0(k8_tmap_1(sK3,sK4))
    | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(k8_tmap_1(sK3,sK4))
    | v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))) != iProver_top
    | m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5043,c_4233])).

cnf(c_6622,plain,
    ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK3,sK4))) != k7_tmap_1(sK3,u1_struct_0(sK4))
    | u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK3,sK4)))) != u1_struct_0(sK3)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5263,c_5721,c_5728])).

cnf(c_6623,plain,
    ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK3,sK4))) != k7_tmap_1(sK3,u1_struct_0(sK4))
    | u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK3,sK4)))) != u1_struct_0(sK3)
    | v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_6622])).

cnf(c_6630,plain,
    ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK3,sK4))) != k7_tmap_1(sK3,u1_struct_0(sK4))
    | u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK3,sK4)))) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6623,c_5778,c_5780])).

cnf(c_6900,plain,
    ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK3,sK4))) != k6_partfun1(u1_struct_0(sK3))
    | u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK3,sK4)))) != u1_struct_0(sK3) ),
    inference(demodulation,[status(thm)],[c_5860,c_6630])).

cnf(c_11396,plain,
    ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK3,sK4)
    | u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK3,sK4)))) = u1_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_11389,c_5024])).

cnf(c_11494,plain,
    ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11395,c_6900,c_11396])).

cnf(c_27,plain,
    ( ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
    | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | v3_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k7_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_315,plain,
    ( ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
    | v3_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k7_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_27,c_17])).

cnf(c_39,negated_conjecture,
    ( v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4))
    | v1_tsep_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f109])).

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
    inference(resolution_lifted,[status(thm)],[c_315,c_39])).

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

cnf(c_12,plain,
    ( ~ v3_pre_topc(sK2(X0,X1),X0)
    | v1_tsep_1(X1,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1596,plain,
    ( ~ v3_pre_topc(sK2(X0,X1),X0)
    | v1_tsep_1(X1,X0)
    | ~ l1_pre_topc(X0)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_286])).

cnf(c_1597,plain,
    ( ~ v3_pre_topc(sK2(sK3,sK4),sK3)
    | v1_tsep_1(sK4,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1596])).

cnf(c_1599,plain,
    ( v1_tsep_1(sK4,sK3)
    | ~ v3_pre_topc(sK2(sK3,sK4),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1597,c_45])).

cnf(c_1600,plain,
    ( ~ v3_pre_topc(sK2(sK3,sK4),sK3)
    | v1_tsep_1(sK4,sK3) ),
    inference(renaming,[status(thm)],[c_1599])).

cnf(c_2411,plain,
    ( v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))))
    | ~ v1_funct_1(k7_tmap_1(sK3,X0))
    | sK2(sK3,sK4) != X0
    | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4)
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_623,c_1600])).

cnf(c_2412,plain,
    ( v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(sK2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4))))))
    | ~ v1_funct_1(k7_tmap_1(sK3,sK2(sK3,sK4)))
    | k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,sK2(sK3,sK4)) != k9_tmap_1(sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_2411])).

cnf(c_14,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1986,plain,
    ( v1_tsep_1(X0,X1)
    | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK4 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_286])).

cnf(c_1987,plain,
    ( v1_tsep_1(sK4,sK3)
    | m1_subset_1(sK2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1986])).

cnf(c_2414,plain,
    ( v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4))))))
    | ~ v1_funct_1(k7_tmap_1(sK3,sK2(sK3,sK4)))
    | k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,sK2(sK3,sK4)) != k9_tmap_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2412,c_45,c_1987])).

cnf(c_4225,plain,
    ( v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4))))))
    | ~ v1_funct_1(k7_tmap_1(sK3,sK2(sK3,sK4)))
    | k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,sK2(sK3,sK4)) != k9_tmap_1(sK3,sK4) ),
    inference(subtyping,[status(esa)],[c_2414])).

cnf(c_5010,plain,
    ( k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,sK2(sK3,sK4)) != k9_tmap_1(sK3,sK4)
    | v1_tsep_1(sK4,sK3) = iProver_top
    | m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4)))))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK3,sK2(sK3,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4225])).

cnf(c_4298,plain,
    ( k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,sK2(sK3,sK4)) != k9_tmap_1(sK3,sK4)
    | v1_tsep_1(sK4,sK3) = iProver_top
    | m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4)))))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK3,sK2(sK3,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4225])).

cnf(c_1989,plain,
    ( m1_subset_1(sK2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_tsep_1(sK4,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1987,c_45])).

cnf(c_1990,plain,
    ( v1_tsep_1(sK4,sK3)
    | m1_subset_1(sK2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(renaming,[status(thm)],[c_1989])).

cnf(c_4229,plain,
    ( v1_tsep_1(sK4,sK3)
    | m1_subset_1(sK2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subtyping,[status(esa)],[c_1990])).

cnf(c_5006,plain,
    ( v1_tsep_1(sK4,sK3) = iProver_top
    | m1_subset_1(sK2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4229])).

cnf(c_6661,plain,
    ( v1_tsep_1(sK4,sK3) = iProver_top
    | v1_funct_1(k7_tmap_1(sK3,sK2(sK3,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5006,c_5026])).

cnf(c_6922,plain,
    ( m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4)))))) != iProver_top
    | v1_tsep_1(sK4,sK3) = iProver_top
    | k7_tmap_1(sK3,sK2(sK3,sK4)) != k9_tmap_1(sK3,sK4)
    | k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5010,c_4298,c_6661])).

cnf(c_6923,plain,
    ( k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,sK2(sK3,sK4)) != k9_tmap_1(sK3,sK4)
    | v1_tsep_1(sK4,sK3) = iProver_top
    | m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4)))))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6922])).

cnf(c_11507,plain,
    ( k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,sK2(sK3,sK4)) != k9_tmap_1(sK3,sK3)
    | v1_tsep_1(sK4,sK3) = iProver_top
    | m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4)))))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11494,c_6923])).

cnf(c_13021,plain,
    ( k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,sK2(sK3,sK4)) != k6_partfun1(u1_struct_0(sK3))
    | v1_tsep_1(sK4,sK3) = iProver_top
    | m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4)))))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13015,c_11507])).

cnf(c_29,plain,
    ( v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
    | ~ v3_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_35,negated_conjecture,
    ( ~ v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4))
    | ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ v1_tsep_1(sK4,sK3)
    | ~ m1_pre_topc(sK4,sK3)
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4)) ),
    inference(cnf_transformation,[],[f113])).

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
    inference(resolution_lifted,[status(thm)],[c_29,c_292])).

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

cnf(c_2245,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
    | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1588,c_587])).

cnf(c_2338,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1930,c_2245])).

cnf(c_2344,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1943,c_2338])).

cnf(c_15,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_333,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_33])).

cnf(c_334,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_333])).

cnf(c_1900,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK4 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_334,c_286])).

cnf(c_1901,plain,
    ( v3_pre_topc(u1_struct_0(sK4),sK3)
    | ~ v1_tsep_1(sK4,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1900])).

cnf(c_1903,plain,
    ( ~ v1_tsep_1(sK4,sK3)
    | v3_pre_topc(u1_struct_0(sK4),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1901,c_45])).

cnf(c_1904,plain,
    ( v3_pre_topc(u1_struct_0(sK4),sK3)
    | ~ v1_tsep_1(sK4,sK3) ),
    inference(renaming,[status(thm)],[c_1903])).

cnf(c_2434,plain,
    ( ~ v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4)
    | u1_struct_0(sK4) != X0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_2344,c_1904])).

cnf(c_2435,plain,
    ( ~ v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | k6_tmap_1(sK3,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,u1_struct_0(sK4)) != k9_tmap_1(sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_2434])).

cnf(c_2437,plain,
    ( ~ v1_tsep_1(sK4,sK3)
    | k7_tmap_1(sK3,u1_struct_0(sK4)) != k9_tmap_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2435,c_47,c_46,c_45,c_1893,c_1915])).

cnf(c_4224,plain,
    ( ~ v1_tsep_1(sK4,sK3)
    | k7_tmap_1(sK3,u1_struct_0(sK4)) != k9_tmap_1(sK3,sK4) ),
    inference(subtyping,[status(esa)],[c_2437])).

cnf(c_5011,plain,
    ( k7_tmap_1(sK3,u1_struct_0(sK4)) != k9_tmap_1(sK3,sK4)
    | v1_tsep_1(sK4,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4224])).

cnf(c_7261,plain,
    ( k9_tmap_1(sK3,sK4) != k6_partfun1(u1_struct_0(sK3))
    | v1_tsep_1(sK4,sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5011,c_5860])).

cnf(c_11504,plain,
    ( k9_tmap_1(sK3,sK3) != k6_partfun1(u1_struct_0(sK3))
    | v1_tsep_1(sK4,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11494,c_7261])).

cnf(c_13022,plain,
    ( k6_partfun1(u1_struct_0(sK3)) != k6_partfun1(u1_struct_0(sK3))
    | v1_tsep_1(sK4,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13015,c_11504])).

cnf(c_13070,plain,
    ( v1_tsep_1(sK4,sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_13022])).

cnf(c_13077,plain,
    ( k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,sK2(sK3,sK4)) != k6_partfun1(u1_struct_0(sK3))
    | m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4)))))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_13021,c_13070])).

cnf(c_6659,plain,
    ( k7_tmap_1(sK3,sK2(sK3,sK4)) = k6_partfun1(u1_struct_0(sK3))
    | v1_tsep_1(sK4,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5006,c_5028])).

cnf(c_13863,plain,
    ( k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4)
    | m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4)))))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13077,c_48,c_50,c_162,c_165,c_6659,c_11504,c_12882])).

cnf(c_13,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK2(X1,X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2000,plain,
    ( v1_tsep_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK2(X1,X0) = u1_struct_0(X0)
    | sK4 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_286])).

cnf(c_2001,plain,
    ( v1_tsep_1(sK4,sK3)
    | ~ l1_pre_topc(sK3)
    | sK2(sK3,sK4) = u1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_2000])).

cnf(c_2003,plain,
    ( v1_tsep_1(sK4,sK3)
    | sK2(sK3,sK4) = u1_struct_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2001,c_45])).

cnf(c_4228,plain,
    ( v1_tsep_1(sK4,sK3)
    | sK2(sK3,sK4) = u1_struct_0(sK4) ),
    inference(subtyping,[status(esa)],[c_2003])).

cnf(c_5007,plain,
    ( sK2(sK3,sK4) = u1_struct_0(sK4)
    | v1_tsep_1(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4228])).

cnf(c_13565,plain,
    ( sK2(sK3,sK4) = u1_struct_0(sK4) ),
    inference(superposition,[status(thm)],[c_5007,c_13070])).

cnf(c_13867,plain,
    ( k8_tmap_1(sK3,sK4) != k8_tmap_1(sK3,sK4)
    | m1_subset_1(k6_partfun1(u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13863,c_4233,c_5721,c_5860,c_13565])).

cnf(c_13868,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_13867])).

cnf(c_13870,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_13868,c_7000])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:11:32 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 4.08/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.08/0.99  
% 4.08/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.08/0.99  
% 4.08/0.99  ------  iProver source info
% 4.08/0.99  
% 4.08/0.99  git: date: 2020-06-30 10:37:57 +0100
% 4.08/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.08/0.99  git: non_committed_changes: false
% 4.08/0.99  git: last_make_outside_of_git: false
% 4.08/0.99  
% 4.08/0.99  ------ 
% 4.08/0.99  
% 4.08/0.99  ------ Input Options
% 4.08/0.99  
% 4.08/0.99  --out_options                           all
% 4.08/0.99  --tptp_safe_out                         true
% 4.08/0.99  --problem_path                          ""
% 4.08/0.99  --include_path                          ""
% 4.08/0.99  --clausifier                            res/vclausify_rel
% 4.08/0.99  --clausifier_options                    --mode clausify
% 4.08/0.99  --stdin                                 false
% 4.08/0.99  --stats_out                             all
% 4.08/0.99  
% 4.08/0.99  ------ General Options
% 4.08/0.99  
% 4.08/0.99  --fof                                   false
% 4.08/0.99  --time_out_real                         305.
% 4.08/0.99  --time_out_virtual                      -1.
% 4.08/0.99  --symbol_type_check                     false
% 4.08/0.99  --clausify_out                          false
% 4.08/0.99  --sig_cnt_out                           false
% 4.08/0.99  --trig_cnt_out                          false
% 4.08/0.99  --trig_cnt_out_tolerance                1.
% 4.08/0.99  --trig_cnt_out_sk_spl                   false
% 4.08/0.99  --abstr_cl_out                          false
% 4.08/0.99  
% 4.08/0.99  ------ Global Options
% 4.08/0.99  
% 4.08/0.99  --schedule                              default
% 4.08/0.99  --add_important_lit                     false
% 4.08/0.99  --prop_solver_per_cl                    1000
% 4.08/0.99  --min_unsat_core                        false
% 4.08/0.99  --soft_assumptions                      false
% 4.08/0.99  --soft_lemma_size                       3
% 4.08/0.99  --prop_impl_unit_size                   0
% 4.08/0.99  --prop_impl_unit                        []
% 4.08/0.99  --share_sel_clauses                     true
% 4.08/0.99  --reset_solvers                         false
% 4.08/0.99  --bc_imp_inh                            [conj_cone]
% 4.08/0.99  --conj_cone_tolerance                   3.
% 4.08/0.99  --extra_neg_conj                        none
% 4.08/0.99  --large_theory_mode                     true
% 4.08/0.99  --prolific_symb_bound                   200
% 4.08/0.99  --lt_threshold                          2000
% 4.08/0.99  --clause_weak_htbl                      true
% 4.08/0.99  --gc_record_bc_elim                     false
% 4.08/0.99  
% 4.08/0.99  ------ Preprocessing Options
% 4.08/0.99  
% 4.08/0.99  --preprocessing_flag                    true
% 4.08/0.99  --time_out_prep_mult                    0.1
% 4.08/0.99  --splitting_mode                        input
% 4.08/0.99  --splitting_grd                         true
% 4.08/0.99  --splitting_cvd                         false
% 4.08/0.99  --splitting_cvd_svl                     false
% 4.08/0.99  --splitting_nvd                         32
% 4.08/0.99  --sub_typing                            true
% 4.08/0.99  --prep_gs_sim                           true
% 4.08/0.99  --prep_unflatten                        true
% 4.08/0.99  --prep_res_sim                          true
% 4.08/0.99  --prep_upred                            true
% 4.08/0.99  --prep_sem_filter                       exhaustive
% 4.08/0.99  --prep_sem_filter_out                   false
% 4.08/0.99  --pred_elim                             true
% 4.08/0.99  --res_sim_input                         true
% 4.08/0.99  --eq_ax_congr_red                       true
% 4.08/0.99  --pure_diseq_elim                       true
% 4.08/0.99  --brand_transform                       false
% 4.08/0.99  --non_eq_to_eq                          false
% 4.08/0.99  --prep_def_merge                        true
% 4.08/0.99  --prep_def_merge_prop_impl              false
% 4.08/0.99  --prep_def_merge_mbd                    true
% 4.08/0.99  --prep_def_merge_tr_red                 false
% 4.08/0.99  --prep_def_merge_tr_cl                  false
% 4.08/0.99  --smt_preprocessing                     true
% 4.08/0.99  --smt_ac_axioms                         fast
% 4.08/0.99  --preprocessed_out                      false
% 4.08/0.99  --preprocessed_stats                    false
% 4.08/0.99  
% 4.08/0.99  ------ Abstraction refinement Options
% 4.08/0.99  
% 4.08/0.99  --abstr_ref                             []
% 4.08/0.99  --abstr_ref_prep                        false
% 4.08/0.99  --abstr_ref_until_sat                   false
% 4.08/0.99  --abstr_ref_sig_restrict                funpre
% 4.08/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 4.08/0.99  --abstr_ref_under                       []
% 4.08/0.99  
% 4.08/0.99  ------ SAT Options
% 4.08/0.99  
% 4.08/0.99  --sat_mode                              false
% 4.08/0.99  --sat_fm_restart_options                ""
% 4.08/0.99  --sat_gr_def                            false
% 4.08/0.99  --sat_epr_types                         true
% 4.08/0.99  --sat_non_cyclic_types                  false
% 4.08/0.99  --sat_finite_models                     false
% 4.08/0.99  --sat_fm_lemmas                         false
% 4.08/0.99  --sat_fm_prep                           false
% 4.08/0.99  --sat_fm_uc_incr                        true
% 4.08/0.99  --sat_out_model                         small
% 4.08/0.99  --sat_out_clauses                       false
% 4.08/0.99  
% 4.08/0.99  ------ QBF Options
% 4.08/0.99  
% 4.08/0.99  --qbf_mode                              false
% 4.08/0.99  --qbf_elim_univ                         false
% 4.08/0.99  --qbf_dom_inst                          none
% 4.08/0.99  --qbf_dom_pre_inst                      false
% 4.08/0.99  --qbf_sk_in                             false
% 4.08/0.99  --qbf_pred_elim                         true
% 4.08/0.99  --qbf_split                             512
% 4.08/0.99  
% 4.08/0.99  ------ BMC1 Options
% 4.08/0.99  
% 4.08/0.99  --bmc1_incremental                      false
% 4.08/0.99  --bmc1_axioms                           reachable_all
% 4.08/0.99  --bmc1_min_bound                        0
% 4.08/0.99  --bmc1_max_bound                        -1
% 4.08/0.99  --bmc1_max_bound_default                -1
% 4.08/0.99  --bmc1_symbol_reachability              true
% 4.08/0.99  --bmc1_property_lemmas                  false
% 4.08/0.99  --bmc1_k_induction                      false
% 4.08/0.99  --bmc1_non_equiv_states                 false
% 4.08/0.99  --bmc1_deadlock                         false
% 4.08/0.99  --bmc1_ucm                              false
% 4.08/0.99  --bmc1_add_unsat_core                   none
% 4.08/0.99  --bmc1_unsat_core_children              false
% 4.08/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 4.08/0.99  --bmc1_out_stat                         full
% 4.08/0.99  --bmc1_ground_init                      false
% 4.08/0.99  --bmc1_pre_inst_next_state              false
% 4.08/0.99  --bmc1_pre_inst_state                   false
% 4.08/0.99  --bmc1_pre_inst_reach_state             false
% 4.08/0.99  --bmc1_out_unsat_core                   false
% 4.08/0.99  --bmc1_aig_witness_out                  false
% 4.08/0.99  --bmc1_verbose                          false
% 4.08/0.99  --bmc1_dump_clauses_tptp                false
% 4.08/0.99  --bmc1_dump_unsat_core_tptp             false
% 4.08/0.99  --bmc1_dump_file                        -
% 4.08/0.99  --bmc1_ucm_expand_uc_limit              128
% 4.08/0.99  --bmc1_ucm_n_expand_iterations          6
% 4.08/0.99  --bmc1_ucm_extend_mode                  1
% 4.08/0.99  --bmc1_ucm_init_mode                    2
% 4.08/0.99  --bmc1_ucm_cone_mode                    none
% 4.08/0.99  --bmc1_ucm_reduced_relation_type        0
% 4.08/0.99  --bmc1_ucm_relax_model                  4
% 4.08/0.99  --bmc1_ucm_full_tr_after_sat            true
% 4.08/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 4.08/0.99  --bmc1_ucm_layered_model                none
% 4.08/0.99  --bmc1_ucm_max_lemma_size               10
% 4.08/0.99  
% 4.08/0.99  ------ AIG Options
% 4.08/0.99  
% 4.08/0.99  --aig_mode                              false
% 4.08/0.99  
% 4.08/0.99  ------ Instantiation Options
% 4.08/0.99  
% 4.08/0.99  --instantiation_flag                    true
% 4.08/0.99  --inst_sos_flag                         false
% 4.08/0.99  --inst_sos_phase                        true
% 4.08/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.08/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.08/0.99  --inst_lit_sel_side                     num_symb
% 4.08/0.99  --inst_solver_per_active                1400
% 4.08/0.99  --inst_solver_calls_frac                1.
% 4.08/0.99  --inst_passive_queue_type               priority_queues
% 4.08/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.08/0.99  --inst_passive_queues_freq              [25;2]
% 4.08/0.99  --inst_dismatching                      true
% 4.08/0.99  --inst_eager_unprocessed_to_passive     true
% 4.08/0.99  --inst_prop_sim_given                   true
% 4.08/0.99  --inst_prop_sim_new                     false
% 4.08/0.99  --inst_subs_new                         false
% 4.08/0.99  --inst_eq_res_simp                      false
% 4.08/0.99  --inst_subs_given                       false
% 4.08/0.99  --inst_orphan_elimination               true
% 4.08/0.99  --inst_learning_loop_flag               true
% 4.08/0.99  --inst_learning_start                   3000
% 4.08/0.99  --inst_learning_factor                  2
% 4.08/0.99  --inst_start_prop_sim_after_learn       3
% 4.08/0.99  --inst_sel_renew                        solver
% 4.08/0.99  --inst_lit_activity_flag                true
% 4.08/0.99  --inst_restr_to_given                   false
% 4.08/0.99  --inst_activity_threshold               500
% 4.08/0.99  --inst_out_proof                        true
% 4.08/0.99  
% 4.08/0.99  ------ Resolution Options
% 4.08/0.99  
% 4.08/0.99  --resolution_flag                       true
% 4.08/0.99  --res_lit_sel                           adaptive
% 4.08/0.99  --res_lit_sel_side                      none
% 4.08/0.99  --res_ordering                          kbo
% 4.08/0.99  --res_to_prop_solver                    active
% 4.08/0.99  --res_prop_simpl_new                    false
% 4.08/0.99  --res_prop_simpl_given                  true
% 4.08/0.99  --res_passive_queue_type                priority_queues
% 4.08/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.08/0.99  --res_passive_queues_freq               [15;5]
% 4.08/0.99  --res_forward_subs                      full
% 4.08/0.99  --res_backward_subs                     full
% 4.08/0.99  --res_forward_subs_resolution           true
% 4.08/0.99  --res_backward_subs_resolution          true
% 4.08/0.99  --res_orphan_elimination                true
% 4.08/0.99  --res_time_limit                        2.
% 4.08/0.99  --res_out_proof                         true
% 4.08/0.99  
% 4.08/0.99  ------ Superposition Options
% 4.08/0.99  
% 4.08/0.99  --superposition_flag                    true
% 4.08/0.99  --sup_passive_queue_type                priority_queues
% 4.08/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.08/0.99  --sup_passive_queues_freq               [8;1;4]
% 4.08/0.99  --demod_completeness_check              fast
% 4.08/0.99  --demod_use_ground                      true
% 4.08/0.99  --sup_to_prop_solver                    passive
% 4.08/0.99  --sup_prop_simpl_new                    true
% 4.08/0.99  --sup_prop_simpl_given                  true
% 4.08/0.99  --sup_fun_splitting                     false
% 4.08/0.99  --sup_smt_interval                      50000
% 4.08/0.99  
% 4.08/0.99  ------ Superposition Simplification Setup
% 4.08/0.99  
% 4.08/0.99  --sup_indices_passive                   []
% 4.08/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.08/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.08/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.08/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 4.08/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.08/0.99  --sup_full_bw                           [BwDemod]
% 4.08/0.99  --sup_immed_triv                        [TrivRules]
% 4.08/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.08/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.08/0.99  --sup_immed_bw_main                     []
% 4.08/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.08/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 4.08/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.08/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.08/0.99  
% 4.08/0.99  ------ Combination Options
% 4.08/0.99  
% 4.08/0.99  --comb_res_mult                         3
% 4.08/0.99  --comb_sup_mult                         2
% 4.08/0.99  --comb_inst_mult                        10
% 4.08/0.99  
% 4.08/0.99  ------ Debug Options
% 4.08/0.99  
% 4.08/0.99  --dbg_backtrace                         false
% 4.08/0.99  --dbg_dump_prop_clauses                 false
% 4.08/0.99  --dbg_dump_prop_clauses_file            -
% 4.08/0.99  --dbg_out_stat                          false
% 4.08/0.99  ------ Parsing...
% 4.08/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.08/0.99  
% 4.08/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e 
% 4.08/0.99  
% 4.08/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.08/0.99  
% 4.08/0.99  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.08/0.99  ------ Proving...
% 4.08/0.99  ------ Problem Properties 
% 4.08/0.99  
% 4.08/0.99  
% 4.08/0.99  clauses                                 49
% 4.08/0.99  conjectures                             0
% 4.08/0.99  EPR                                     0
% 4.08/0.99  Horn                                    30
% 4.08/0.99  unary                                   13
% 4.08/0.99  binary                                  21
% 4.08/0.99  lits                                    141
% 4.08/0.99  lits eq                                 55
% 4.08/0.99  fd_pure                                 0
% 4.08/0.99  fd_pseudo                               0
% 4.08/0.99  fd_cond                                 6
% 4.08/0.99  fd_pseudo_cond                          0
% 4.08/0.99  AC symbols                              0
% 4.08/0.99  
% 4.08/0.99  ------ Schedule dynamic 5 is on 
% 4.08/0.99  
% 4.08/0.99  ------ no conjectures: strip conj schedule 
% 4.08/0.99  
% 4.08/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 4.08/0.99  
% 4.08/0.99  
% 4.08/0.99  ------ 
% 4.08/0.99  Current options:
% 4.08/0.99  ------ 
% 4.08/0.99  
% 4.08/0.99  ------ Input Options
% 4.08/0.99  
% 4.08/0.99  --out_options                           all
% 4.08/0.99  --tptp_safe_out                         true
% 4.08/0.99  --problem_path                          ""
% 4.08/0.99  --include_path                          ""
% 4.08/0.99  --clausifier                            res/vclausify_rel
% 4.08/0.99  --clausifier_options                    --mode clausify
% 4.08/0.99  --stdin                                 false
% 4.08/0.99  --stats_out                             all
% 4.08/0.99  
% 4.08/0.99  ------ General Options
% 4.08/0.99  
% 4.08/0.99  --fof                                   false
% 4.08/0.99  --time_out_real                         305.
% 4.08/0.99  --time_out_virtual                      -1.
% 4.08/0.99  --symbol_type_check                     false
% 4.08/0.99  --clausify_out                          false
% 4.08/0.99  --sig_cnt_out                           false
% 4.08/0.99  --trig_cnt_out                          false
% 4.08/0.99  --trig_cnt_out_tolerance                1.
% 4.08/0.99  --trig_cnt_out_sk_spl                   false
% 4.08/0.99  --abstr_cl_out                          false
% 4.08/0.99  
% 4.08/0.99  ------ Global Options
% 4.08/0.99  
% 4.08/0.99  --schedule                              default
% 4.08/0.99  --add_important_lit                     false
% 4.08/0.99  --prop_solver_per_cl                    1000
% 4.08/0.99  --min_unsat_core                        false
% 4.08/0.99  --soft_assumptions                      false
% 4.08/0.99  --soft_lemma_size                       3
% 4.08/0.99  --prop_impl_unit_size                   0
% 4.08/0.99  --prop_impl_unit                        []
% 4.08/0.99  --share_sel_clauses                     true
% 4.08/0.99  --reset_solvers                         false
% 4.08/0.99  --bc_imp_inh                            [conj_cone]
% 4.08/0.99  --conj_cone_tolerance                   3.
% 4.08/0.99  --extra_neg_conj                        none
% 4.08/0.99  --large_theory_mode                     true
% 4.08/0.99  --prolific_symb_bound                   200
% 4.08/0.99  --lt_threshold                          2000
% 4.08/0.99  --clause_weak_htbl                      true
% 4.08/0.99  --gc_record_bc_elim                     false
% 4.08/0.99  
% 4.08/0.99  ------ Preprocessing Options
% 4.08/0.99  
% 4.08/0.99  --preprocessing_flag                    true
% 4.08/0.99  --time_out_prep_mult                    0.1
% 4.08/0.99  --splitting_mode                        input
% 4.08/0.99  --splitting_grd                         true
% 4.08/0.99  --splitting_cvd                         false
% 4.08/0.99  --splitting_cvd_svl                     false
% 4.08/0.99  --splitting_nvd                         32
% 4.08/0.99  --sub_typing                            true
% 4.08/0.99  --prep_gs_sim                           true
% 4.08/0.99  --prep_unflatten                        true
% 4.08/0.99  --prep_res_sim                          true
% 4.08/0.99  --prep_upred                            true
% 4.08/0.99  --prep_sem_filter                       exhaustive
% 4.08/0.99  --prep_sem_filter_out                   false
% 4.08/0.99  --pred_elim                             true
% 4.08/0.99  --res_sim_input                         true
% 4.08/0.99  --eq_ax_congr_red                       true
% 4.08/0.99  --pure_diseq_elim                       true
% 4.08/0.99  --brand_transform                       false
% 4.08/0.99  --non_eq_to_eq                          false
% 4.08/0.99  --prep_def_merge                        true
% 4.08/0.99  --prep_def_merge_prop_impl              false
% 4.08/0.99  --prep_def_merge_mbd                    true
% 4.08/0.99  --prep_def_merge_tr_red                 false
% 4.08/0.99  --prep_def_merge_tr_cl                  false
% 4.08/0.99  --smt_preprocessing                     true
% 4.08/0.99  --smt_ac_axioms                         fast
% 4.08/0.99  --preprocessed_out                      false
% 4.08/0.99  --preprocessed_stats                    false
% 4.08/0.99  
% 4.08/0.99  ------ Abstraction refinement Options
% 4.08/0.99  
% 4.08/0.99  --abstr_ref                             []
% 4.08/0.99  --abstr_ref_prep                        false
% 4.08/0.99  --abstr_ref_until_sat                   false
% 4.08/0.99  --abstr_ref_sig_restrict                funpre
% 4.08/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 4.08/0.99  --abstr_ref_under                       []
% 4.08/0.99  
% 4.08/0.99  ------ SAT Options
% 4.08/0.99  
% 4.08/0.99  --sat_mode                              false
% 4.08/0.99  --sat_fm_restart_options                ""
% 4.08/0.99  --sat_gr_def                            false
% 4.08/0.99  --sat_epr_types                         true
% 4.08/0.99  --sat_non_cyclic_types                  false
% 4.08/0.99  --sat_finite_models                     false
% 4.08/0.99  --sat_fm_lemmas                         false
% 4.08/0.99  --sat_fm_prep                           false
% 4.08/0.99  --sat_fm_uc_incr                        true
% 4.08/0.99  --sat_out_model                         small
% 4.08/0.99  --sat_out_clauses                       false
% 4.08/0.99  
% 4.08/0.99  ------ QBF Options
% 4.08/0.99  
% 4.08/0.99  --qbf_mode                              false
% 4.08/0.99  --qbf_elim_univ                         false
% 4.08/0.99  --qbf_dom_inst                          none
% 4.08/0.99  --qbf_dom_pre_inst                      false
% 4.08/0.99  --qbf_sk_in                             false
% 4.08/0.99  --qbf_pred_elim                         true
% 4.08/0.99  --qbf_split                             512
% 4.08/0.99  
% 4.08/0.99  ------ BMC1 Options
% 4.08/0.99  
% 4.08/0.99  --bmc1_incremental                      false
% 4.08/0.99  --bmc1_axioms                           reachable_all
% 4.08/0.99  --bmc1_min_bound                        0
% 4.08/0.99  --bmc1_max_bound                        -1
% 4.08/0.99  --bmc1_max_bound_default                -1
% 4.08/0.99  --bmc1_symbol_reachability              true
% 4.08/0.99  --bmc1_property_lemmas                  false
% 4.08/0.99  --bmc1_k_induction                      false
% 4.08/0.99  --bmc1_non_equiv_states                 false
% 4.08/0.99  --bmc1_deadlock                         false
% 4.08/0.99  --bmc1_ucm                              false
% 4.08/0.99  --bmc1_add_unsat_core                   none
% 4.08/0.99  --bmc1_unsat_core_children              false
% 4.08/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 4.08/0.99  --bmc1_out_stat                         full
% 4.08/0.99  --bmc1_ground_init                      false
% 4.08/0.99  --bmc1_pre_inst_next_state              false
% 4.08/0.99  --bmc1_pre_inst_state                   false
% 4.08/0.99  --bmc1_pre_inst_reach_state             false
% 4.08/0.99  --bmc1_out_unsat_core                   false
% 4.08/0.99  --bmc1_aig_witness_out                  false
% 4.08/0.99  --bmc1_verbose                          false
% 4.08/0.99  --bmc1_dump_clauses_tptp                false
% 4.08/0.99  --bmc1_dump_unsat_core_tptp             false
% 4.08/0.99  --bmc1_dump_file                        -
% 4.08/0.99  --bmc1_ucm_expand_uc_limit              128
% 4.08/0.99  --bmc1_ucm_n_expand_iterations          6
% 4.08/0.99  --bmc1_ucm_extend_mode                  1
% 4.08/0.99  --bmc1_ucm_init_mode                    2
% 4.08/0.99  --bmc1_ucm_cone_mode                    none
% 4.08/0.99  --bmc1_ucm_reduced_relation_type        0
% 4.08/0.99  --bmc1_ucm_relax_model                  4
% 4.08/0.99  --bmc1_ucm_full_tr_after_sat            true
% 4.08/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 4.08/0.99  --bmc1_ucm_layered_model                none
% 4.08/0.99  --bmc1_ucm_max_lemma_size               10
% 4.08/0.99  
% 4.08/0.99  ------ AIG Options
% 4.08/0.99  
% 4.08/0.99  --aig_mode                              false
% 4.08/0.99  
% 4.08/0.99  ------ Instantiation Options
% 4.08/0.99  
% 4.08/0.99  --instantiation_flag                    true
% 4.08/0.99  --inst_sos_flag                         false
% 4.08/0.99  --inst_sos_phase                        true
% 4.08/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.08/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.08/0.99  --inst_lit_sel_side                     none
% 4.08/0.99  --inst_solver_per_active                1400
% 4.08/0.99  --inst_solver_calls_frac                1.
% 4.08/0.99  --inst_passive_queue_type               priority_queues
% 4.08/0.99  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 4.08/0.99  --inst_passive_queues_freq              [25;2]
% 4.08/0.99  --inst_dismatching                      true
% 4.08/0.99  --inst_eager_unprocessed_to_passive     true
% 4.08/0.99  --inst_prop_sim_given                   true
% 4.08/0.99  --inst_prop_sim_new                     false
% 4.08/0.99  --inst_subs_new                         false
% 4.08/0.99  --inst_eq_res_simp                      false
% 4.08/0.99  --inst_subs_given                       false
% 4.08/0.99  --inst_orphan_elimination               true
% 4.08/0.99  --inst_learning_loop_flag               true
% 4.08/0.99  --inst_learning_start                   3000
% 4.08/0.99  --inst_learning_factor                  2
% 4.08/0.99  --inst_start_prop_sim_after_learn       3
% 4.08/0.99  --inst_sel_renew                        solver
% 4.08/0.99  --inst_lit_activity_flag                true
% 4.08/0.99  --inst_restr_to_given                   false
% 4.08/0.99  --inst_activity_threshold               500
% 4.08/0.99  --inst_out_proof                        true
% 4.08/0.99  
% 4.08/0.99  ------ Resolution Options
% 4.08/0.99  
% 4.08/0.99  --resolution_flag                       false
% 4.08/0.99  --res_lit_sel                           adaptive
% 4.08/0.99  --res_lit_sel_side                      none
% 4.08/0.99  --res_ordering                          kbo
% 4.08/0.99  --res_to_prop_solver                    active
% 4.08/0.99  --res_prop_simpl_new                    false
% 4.08/0.99  --res_prop_simpl_given                  true
% 4.08/0.99  --res_passive_queue_type                priority_queues
% 4.08/0.99  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 4.08/0.99  --res_passive_queues_freq               [15;5]
% 4.08/0.99  --res_forward_subs                      full
% 4.08/0.99  --res_backward_subs                     full
% 4.08/0.99  --res_forward_subs_resolution           true
% 4.08/0.99  --res_backward_subs_resolution          true
% 4.08/0.99  --res_orphan_elimination                true
% 4.08/0.99  --res_time_limit                        2.
% 4.08/0.99  --res_out_proof                         true
% 4.08/0.99  
% 4.08/0.99  ------ Superposition Options
% 4.08/0.99  
% 4.08/0.99  --superposition_flag                    true
% 4.08/0.99  --sup_passive_queue_type                priority_queues
% 4.08/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.08/0.99  --sup_passive_queues_freq               [8;1;4]
% 4.08/0.99  --demod_completeness_check              fast
% 4.08/0.99  --demod_use_ground                      true
% 4.08/0.99  --sup_to_prop_solver                    passive
% 4.08/0.99  --sup_prop_simpl_new                    true
% 4.08/0.99  --sup_prop_simpl_given                  true
% 4.08/0.99  --sup_fun_splitting                     false
% 4.08/0.99  --sup_smt_interval                      50000
% 4.08/0.99  
% 4.08/0.99  ------ Superposition Simplification Setup
% 4.08/0.99  
% 4.08/0.99  --sup_indices_passive                   []
% 4.08/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.08/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.08/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.08/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 4.08/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.08/0.99  --sup_full_bw                           [BwDemod]
% 4.08/0.99  --sup_immed_triv                        [TrivRules]
% 4.08/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.08/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.08/0.99  --sup_immed_bw_main                     []
% 4.08/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.08/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 4.08/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.08/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.08/0.99  
% 4.08/0.99  ------ Combination Options
% 4.08/0.99  
% 4.08/0.99  --comb_res_mult                         3
% 4.08/0.99  --comb_sup_mult                         2
% 4.08/0.99  --comb_inst_mult                        10
% 4.08/0.99  
% 4.08/0.99  ------ Debug Options
% 4.08/0.99  
% 4.08/0.99  --dbg_backtrace                         false
% 4.08/0.99  --dbg_dump_prop_clauses                 false
% 4.08/0.99  --dbg_dump_prop_clauses_file            -
% 4.08/0.99  --dbg_out_stat                          false
% 4.08/0.99  
% 4.08/0.99  
% 4.08/0.99  
% 4.08/0.99  
% 4.08/0.99  ------ Proving...
% 4.08/0.99  
% 4.08/0.99  
% 4.08/0.99  % SZS status Theorem for theBenchmark.p
% 4.08/0.99  
% 4.08/0.99   Resolution empty clause
% 4.08/0.99  
% 4.08/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 4.08/0.99  
% 4.08/0.99  fof(f14,axiom,(
% 4.08/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 4.08/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.08/0.99  
% 4.08/0.99  fof(f43,plain,(
% 4.08/0.99    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 4.08/0.99    inference(ennf_transformation,[],[f14])).
% 4.08/0.99  
% 4.08/0.99  fof(f99,plain,(
% 4.08/0.99    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 4.08/0.99    inference(cnf_transformation,[],[f43])).
% 4.08/0.99  
% 4.08/0.99  fof(f16,conjecture,(
% 4.08/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))))))),
% 4.08/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.08/0.99  
% 4.08/0.99  fof(f17,negated_conjecture,(
% 4.08/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))))))),
% 4.08/0.99    inference(negated_conjecture,[],[f16])).
% 4.08/0.99  
% 4.08/0.99  fof(f45,plain,(
% 4.08/0.99    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1)))) & m1_pre_topc(X1,X0)) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 4.08/0.99    inference(ennf_transformation,[],[f17])).
% 4.08/0.99  
% 4.08/0.99  fof(f46,plain,(
% 4.08/0.99    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 4.08/0.99    inference(flattening,[],[f45])).
% 4.08/0.99  
% 4.08/0.99  fof(f61,plain,(
% 4.08/0.99    ? [X0] : (? [X1] : ((((~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) & ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 4.08/0.99    inference(nnf_transformation,[],[f46])).
% 4.08/0.99  
% 4.08/0.99  fof(f62,plain,(
% 4.08/0.99    ? [X0] : (? [X1] : ((~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 4.08/0.99    inference(flattening,[],[f61])).
% 4.08/0.99  
% 4.08/0.99  fof(f64,plain,(
% 4.08/0.99    ( ! [X0] : (? [X1] : ((~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0)) => ((~m1_subset_1(k9_tmap_1(X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,sK4))))) | ~v5_pre_topc(k9_tmap_1(X0,sK4),X0,k8_tmap_1(X0,sK4)) | ~v1_funct_2(k9_tmap_1(X0,sK4),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,sK4))) | ~v1_funct_1(k9_tmap_1(X0,sK4)) | ~m1_pre_topc(sK4,X0) | ~v1_tsep_1(sK4,X0)) & ((m1_subset_1(k9_tmap_1(X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,sK4))))) & v5_pre_topc(k9_tmap_1(X0,sK4),X0,k8_tmap_1(X0,sK4)) & v1_funct_2(k9_tmap_1(X0,sK4),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,sK4))) & v1_funct_1(k9_tmap_1(X0,sK4))) | (m1_pre_topc(sK4,X0) & v1_tsep_1(sK4,X0))) & m1_pre_topc(sK4,X0))) )),
% 4.08/0.99    introduced(choice_axiom,[])).
% 4.08/0.99  
% 4.08/0.99  fof(f63,plain,(
% 4.08/0.99    ? [X0] : (? [X1] : ((~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~m1_subset_1(k9_tmap_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X1))))) | ~v5_pre_topc(k9_tmap_1(sK3,X1),sK3,k8_tmap_1(sK3,X1)) | ~v1_funct_2(k9_tmap_1(sK3,X1),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X1))) | ~v1_funct_1(k9_tmap_1(sK3,X1)) | ~m1_pre_topc(X1,sK3) | ~v1_tsep_1(X1,sK3)) & ((m1_subset_1(k9_tmap_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X1))))) & v5_pre_topc(k9_tmap_1(sK3,X1),sK3,k8_tmap_1(sK3,X1)) & v1_funct_2(k9_tmap_1(sK3,X1),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X1))) & v1_funct_1(k9_tmap_1(sK3,X1))) | (m1_pre_topc(X1,sK3) & v1_tsep_1(X1,sK3))) & m1_pre_topc(X1,sK3)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 4.08/0.99    introduced(choice_axiom,[])).
% 4.08/0.99  
% 4.08/0.99  fof(f65,plain,(
% 4.08/0.99    ((~m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) | ~v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4)) | ~v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) | ~v1_funct_1(k9_tmap_1(sK3,sK4)) | ~m1_pre_topc(sK4,sK3) | ~v1_tsep_1(sK4,sK3)) & ((m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) & v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4)) & v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) & v1_funct_1(k9_tmap_1(sK3,sK4))) | (m1_pre_topc(sK4,sK3) & v1_tsep_1(sK4,sK3))) & m1_pre_topc(sK4,sK3)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 4.08/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f62,f64,f63])).
% 4.08/0.99  
% 4.08/0.99  fof(f112,plain,(
% 4.08/0.99    m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) | m1_pre_topc(sK4,sK3)),
% 4.08/0.99    inference(cnf_transformation,[],[f65])).
% 4.08/0.99  
% 4.08/0.99  fof(f104,plain,(
% 4.08/0.99    m1_pre_topc(sK4,sK3)),
% 4.08/0.99    inference(cnf_transformation,[],[f65])).
% 4.08/0.99  
% 4.08/0.99  fof(f103,plain,(
% 4.08/0.99    l1_pre_topc(sK3)),
% 4.08/0.99    inference(cnf_transformation,[],[f65])).
% 4.08/0.99  
% 4.08/0.99  fof(f4,axiom,(
% 4.08/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))))),
% 4.08/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.08/0.99  
% 4.08/0.99  fof(f23,plain,(
% 4.08/0.99    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.08/0.99    inference(ennf_transformation,[],[f4])).
% 4.08/0.99  
% 4.08/0.99  fof(f24,plain,(
% 4.08/0.99    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.08/0.99    inference(flattening,[],[f23])).
% 4.08/0.99  
% 4.08/0.99  fof(f69,plain,(
% 4.08/0.99    ( ! [X0,X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.08/0.99    inference(cnf_transformation,[],[f24])).
% 4.08/0.99  
% 4.08/0.99  fof(f101,plain,(
% 4.08/0.99    ~v2_struct_0(sK3)),
% 4.08/0.99    inference(cnf_transformation,[],[f65])).
% 4.08/0.99  
% 4.08/0.99  fof(f102,plain,(
% 4.08/0.99    v2_pre_topc(sK3)),
% 4.08/0.99    inference(cnf_transformation,[],[f65])).
% 4.08/0.99  
% 4.08/0.99  fof(f8,axiom,(
% 4.08/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 4.08/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.08/0.99  
% 4.08/0.99  fof(f31,plain,(
% 4.08/0.99    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.08/0.99    inference(ennf_transformation,[],[f8])).
% 4.08/0.99  
% 4.08/0.99  fof(f32,plain,(
% 4.08/0.99    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.08/0.99    inference(flattening,[],[f31])).
% 4.08/0.99  
% 4.08/0.99  fof(f84,plain,(
% 4.08/0.99    ( ! [X0,X1] : (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.08/0.99    inference(cnf_transformation,[],[f32])).
% 4.08/0.99  
% 4.08/0.99  fof(f5,axiom,(
% 4.08/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & v1_pre_topc(X2)) => (k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => k6_tmap_1(X0,X3) = X2))))))),
% 4.08/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.08/0.99  
% 4.08/0.99  fof(f25,plain,(
% 4.08/0.99    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : ((k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.08/0.99    inference(ennf_transformation,[],[f5])).
% 4.08/0.99  
% 4.08/0.99  fof(f26,plain,(
% 4.08/0.99    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.08/0.99    inference(flattening,[],[f25])).
% 4.08/0.99  
% 4.08/0.99  fof(f47,plain,(
% 4.08/0.99    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.08/0.99    inference(nnf_transformation,[],[f26])).
% 4.08/0.99  
% 4.08/0.99  fof(f48,plain,(
% 4.08/0.99    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.08/0.99    inference(rectify,[],[f47])).
% 4.08/0.99  
% 4.08/0.99  fof(f49,plain,(
% 4.08/0.99    ! [X2,X1,X0] : (? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (k6_tmap_1(X0,sK0(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK0(X0,X1,X2) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 4.08/0.99    introduced(choice_axiom,[])).
% 4.08/0.99  
% 4.08/0.99  fof(f50,plain,(
% 4.08/0.99    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | (k6_tmap_1(X0,sK0(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK0(X0,X1,X2) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.08/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f48,f49])).
% 4.08/0.99  
% 4.08/0.99  fof(f70,plain,(
% 4.08/0.99    ( ! [X4,X2,X0,X1] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.08/0.99    inference(cnf_transformation,[],[f50])).
% 4.08/0.99  
% 4.08/0.99  fof(f114,plain,(
% 4.08/0.99    ( ! [X2,X0,X1] : (k6_tmap_1(X0,u1_struct_0(X1)) = X2 | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.08/0.99    inference(equality_resolution,[],[f70])).
% 4.08/0.99  
% 4.08/0.99  fof(f115,plain,(
% 4.08/0.99    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.08/0.99    inference(equality_resolution,[],[f114])).
% 4.08/0.99  
% 4.08/0.99  fof(f9,axiom,(
% 4.08/0.99    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 4.08/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.08/0.99  
% 4.08/0.99  fof(f33,plain,(
% 4.08/0.99    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.08/0.99    inference(ennf_transformation,[],[f9])).
% 4.08/0.99  
% 4.08/0.99  fof(f34,plain,(
% 4.08/0.99    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.08/0.99    inference(flattening,[],[f33])).
% 4.08/0.99  
% 4.08/0.99  fof(f85,plain,(
% 4.08/0.99    ( ! [X0,X1] : (v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.08/0.99    inference(cnf_transformation,[],[f34])).
% 4.08/0.99  
% 4.08/0.99  fof(f86,plain,(
% 4.08/0.99    ( ! [X0,X1] : (v2_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.08/0.99    inference(cnf_transformation,[],[f34])).
% 4.08/0.99  
% 4.08/0.99  fof(f87,plain,(
% 4.08/0.99    ( ! [X0,X1] : (l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.08/0.99    inference(cnf_transformation,[],[f34])).
% 4.08/0.99  
% 4.08/0.99  fof(f11,axiom,(
% 4.08/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 4.08/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.08/0.99  
% 4.08/0.99  fof(f37,plain,(
% 4.08/0.99    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.08/0.99    inference(ennf_transformation,[],[f11])).
% 4.08/0.99  
% 4.08/0.99  fof(f38,plain,(
% 4.08/0.99    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.08/0.99    inference(flattening,[],[f37])).
% 4.08/0.99  
% 4.08/0.99  fof(f91,plain,(
% 4.08/0.99    ( ! [X0,X1] : (u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.08/0.99    inference(cnf_transformation,[],[f38])).
% 4.08/0.99  
% 4.08/0.99  fof(f15,axiom,(
% 4.08/0.99    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 4.08/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.08/0.99  
% 4.08/0.99  fof(f44,plain,(
% 4.08/0.99    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 4.08/0.99    inference(ennf_transformation,[],[f15])).
% 4.08/0.99  
% 4.08/0.99  fof(f100,plain,(
% 4.08/0.99    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 4.08/0.99    inference(cnf_transformation,[],[f44])).
% 4.08/0.99  
% 4.08/0.99  fof(f6,axiom,(
% 4.08/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(X2)) => (k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))))))))),
% 4.08/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.08/0.99  
% 4.08/0.99  fof(f27,plain,(
% 4.08/0.99    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : ((r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.08/0.99    inference(ennf_transformation,[],[f6])).
% 4.08/0.99  
% 4.08/0.99  fof(f28,plain,(
% 4.08/0.99    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.08/0.99    inference(flattening,[],[f27])).
% 4.08/0.99  
% 4.08/0.99  fof(f51,plain,(
% 4.08/0.99    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | ? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.08/0.99    inference(nnf_transformation,[],[f28])).
% 4.08/0.99  
% 4.08/0.99  fof(f52,plain,(
% 4.08/0.99    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | ? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.08/0.99    inference(rectify,[],[f51])).
% 4.08/0.99  
% 4.08/0.99  fof(f53,plain,(
% 4.08/0.99    ! [X2,X1,X0] : (? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2))) & u1_struct_0(X1) = sK1(X0,X1,X2) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 4.08/0.99    introduced(choice_axiom,[])).
% 4.08/0.99  
% 4.08/0.99  fof(f54,plain,(
% 4.08/0.99    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2))) & u1_struct_0(X1) = sK1(X0,X1,X2) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.08/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f52,f53])).
% 4.08/0.99  
% 4.08/0.99  fof(f76,plain,(
% 4.08/0.99    ( ! [X2,X0,X1] : (k9_tmap_1(X0,X1) = X2 | u1_struct_0(X1) = sK1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.08/0.99    inference(cnf_transformation,[],[f54])).
% 4.08/0.99  
% 4.08/0.99  fof(f82,plain,(
% 4.08/0.99    ( ! [X0,X1] : (v1_funct_1(k7_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.08/0.99    inference(cnf_transformation,[],[f32])).
% 4.08/0.99  
% 4.08/0.99  fof(f83,plain,(
% 4.08/0.99    ( ! [X0,X1] : (v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.08/0.99    inference(cnf_transformation,[],[f32])).
% 4.08/0.99  
% 4.08/0.99  fof(f3,axiom,(
% 4.08/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => r1_funct_2(X0,X1,X2,X3,X4,X4))),
% 4.08/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.08/0.99  
% 4.08/0.99  fof(f21,plain,(
% 4.08/0.99    ! [X0,X1,X2,X3,X4,X5] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 4.08/0.99    inference(ennf_transformation,[],[f3])).
% 4.08/0.99  
% 4.08/0.99  fof(f22,plain,(
% 4.08/0.99    ! [X0,X1,X2,X3,X4,X5] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 4.08/0.99    inference(flattening,[],[f21])).
% 4.08/0.99  
% 4.08/0.99  fof(f68,plain,(
% 4.08/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 4.08/0.99    inference(cnf_transformation,[],[f22])).
% 4.08/0.99  
% 4.08/0.99  fof(f77,plain,(
% 4.08/0.99    ( ! [X2,X0,X1] : (k9_tmap_1(X0,X1) = X2 | ~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.08/0.99    inference(cnf_transformation,[],[f54])).
% 4.08/0.99  
% 4.08/0.99  fof(f2,axiom,(
% 4.08/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 4.08/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.08/0.99  
% 4.08/0.99  fof(f19,plain,(
% 4.08/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 4.08/0.99    inference(ennf_transformation,[],[f2])).
% 4.08/0.99  
% 4.08/0.99  fof(f20,plain,(
% 4.08/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 4.08/0.99    inference(flattening,[],[f19])).
% 4.08/0.99  
% 4.08/0.99  fof(f67,plain,(
% 4.08/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 4.08/0.99    inference(cnf_transformation,[],[f20])).
% 4.08/0.99  
% 4.08/0.99  fof(f1,axiom,(
% 4.08/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 4.08/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.08/0.99  
% 4.08/0.99  fof(f18,plain,(
% 4.08/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 4.08/0.99    inference(ennf_transformation,[],[f1])).
% 4.08/0.99  
% 4.08/0.99  fof(f66,plain,(
% 4.08/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 4.08/0.99    inference(cnf_transformation,[],[f18])).
% 4.08/0.99  
% 4.08/0.99  fof(f75,plain,(
% 4.08/0.99    ( ! [X2,X0,X1] : (k9_tmap_1(X0,X1) = X2 | m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.08/0.99    inference(cnf_transformation,[],[f54])).
% 4.08/0.99  
% 4.08/0.99  fof(f10,axiom,(
% 4.08/0.99    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))))),
% 4.08/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.08/0.99  
% 4.08/0.99  fof(f35,plain,(
% 4.08/0.99    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.08/0.99    inference(ennf_transformation,[],[f10])).
% 4.08/0.99  
% 4.08/0.99  fof(f36,plain,(
% 4.08/0.99    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.08/0.99    inference(flattening,[],[f35])).
% 4.08/0.99  
% 4.08/0.99  fof(f90,plain,(
% 4.08/0.99    ( ! [X0,X1] : (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.08/0.99    inference(cnf_transformation,[],[f36])).
% 4.08/0.99  
% 4.08/0.99  fof(f88,plain,(
% 4.08/0.99    ( ! [X0,X1] : (v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.08/0.99    inference(cnf_transformation,[],[f36])).
% 4.08/0.99  
% 4.08/0.99  fof(f89,plain,(
% 4.08/0.99    ( ! [X0,X1] : (v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.08/0.99    inference(cnf_transformation,[],[f36])).
% 4.08/0.99  
% 4.08/0.99  fof(f74,plain,(
% 4.08/0.99    ( ! [X4,X2,X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k9_tmap_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.08/0.99    inference(cnf_transformation,[],[f54])).
% 4.08/0.99  
% 4.08/0.99  fof(f116,plain,(
% 4.08/0.99    ( ! [X2,X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),X2,k7_tmap_1(X0,u1_struct_0(X1))) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k9_tmap_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.08/0.99    inference(equality_resolution,[],[f74])).
% 4.08/0.99  
% 4.08/0.99  fof(f117,plain,(
% 4.08/0.99    ( ! [X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1))) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.08/0.99    inference(equality_resolution,[],[f116])).
% 4.08/0.99  
% 4.08/0.99  fof(f12,axiom,(
% 4.08/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))))),
% 4.08/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.08/0.99  
% 4.08/0.99  fof(f39,plain,(
% 4.08/0.99    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.08/0.99    inference(ennf_transformation,[],[f12])).
% 4.08/0.99  
% 4.08/0.99  fof(f40,plain,(
% 4.08/0.99    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.08/0.99    inference(flattening,[],[f39])).
% 4.08/0.99  
% 4.08/0.99  fof(f59,plain,(
% 4.08/0.99    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | (~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1)))) & ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.08/0.99    inference(nnf_transformation,[],[f40])).
% 4.08/0.99  
% 4.08/0.99  fof(f60,plain,(
% 4.08/0.99    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1))) & ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.08/0.99    inference(flattening,[],[f59])).
% 4.08/0.99  
% 4.08/0.99  fof(f97,plain,(
% 4.08/0.99    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.08/0.99    inference(cnf_transformation,[],[f60])).
% 4.08/0.99  
% 4.08/0.99  fof(f109,plain,(
% 4.08/0.99    v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4)) | v1_tsep_1(sK4,sK3)),
% 4.08/0.99    inference(cnf_transformation,[],[f65])).
% 4.08/0.99  
% 4.08/0.99  fof(f7,axiom,(
% 4.08/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tsep_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v3_pre_topc(X2,X0))))))),
% 4.08/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.08/0.99  
% 4.08/0.99  fof(f29,plain,(
% 4.08/0.99    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 4.08/0.99    inference(ennf_transformation,[],[f7])).
% 4.08/0.99  
% 4.08/0.99  fof(f30,plain,(
% 4.08/0.99    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 4.08/0.99    inference(flattening,[],[f29])).
% 4.08/0.99  
% 4.08/0.99  fof(f55,plain,(
% 4.08/0.99    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 4.08/0.99    inference(nnf_transformation,[],[f30])).
% 4.08/0.99  
% 4.08/0.99  fof(f56,plain,(
% 4.08/0.99    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 4.08/0.99    inference(rectify,[],[f55])).
% 4.08/0.99  
% 4.08/0.99  fof(f57,plain,(
% 4.08/0.99    ! [X1,X0] : (? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK2(X0,X1),X0) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 4.08/0.99    introduced(choice_axiom,[])).
% 4.08/0.99  
% 4.08/0.99  fof(f58,plain,(
% 4.08/0.99    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | (~v3_pre_topc(sK2(X0,X1),X0) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 4.08/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f56,f57])).
% 4.08/0.99  
% 4.08/0.99  fof(f81,plain,(
% 4.08/0.99    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(sK2(X0,X1),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 4.08/0.99    inference(cnf_transformation,[],[f58])).
% 4.08/0.99  
% 4.08/0.99  fof(f79,plain,(
% 4.08/0.99    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 4.08/0.99    inference(cnf_transformation,[],[f58])).
% 4.08/0.99  
% 4.08/0.99  fof(f95,plain,(
% 4.08/0.99    ( ! [X0,X1] : (v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.08/0.99    inference(cnf_transformation,[],[f60])).
% 4.08/0.99  
% 4.08/0.99  fof(f113,plain,(
% 4.08/0.99    ~m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) | ~v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4)) | ~v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) | ~v1_funct_1(k9_tmap_1(sK3,sK4)) | ~m1_pre_topc(sK4,sK3) | ~v1_tsep_1(sK4,sK3)),
% 4.08/0.99    inference(cnf_transformation,[],[f65])).
% 4.08/0.99  
% 4.08/0.99  fof(f78,plain,(
% 4.08/0.99    ( ! [X0,X3,X1] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 4.08/0.99    inference(cnf_transformation,[],[f58])).
% 4.08/0.99  
% 4.08/0.99  fof(f118,plain,(
% 4.08/0.99    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 4.08/0.99    inference(equality_resolution,[],[f78])).
% 4.08/0.99  
% 4.08/0.99  fof(f80,plain,(
% 4.08/0.99    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | u1_struct_0(X1) = sK2(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 4.08/0.99    inference(cnf_transformation,[],[f58])).
% 4.08/0.99  
% 4.08/0.99  cnf(c_33,plain,
% 4.08/0.99      ( ~ m1_pre_topc(X0,X1)
% 4.08/0.99      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 4.08/0.99      | ~ l1_pre_topc(X1) ),
% 4.08/0.99      inference(cnf_transformation,[],[f99]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_36,negated_conjecture,
% 4.08/0.99      ( m1_pre_topc(sK4,sK3)
% 4.08/0.99      | m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) ),
% 4.08/0.99      inference(cnf_transformation,[],[f112]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_44,negated_conjecture,
% 4.08/0.99      ( m1_pre_topc(sK4,sK3) ),
% 4.08/0.99      inference(cnf_transformation,[],[f104]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_286,negated_conjecture,
% 4.08/0.99      ( m1_pre_topc(sK4,sK3) ),
% 4.08/0.99      inference(global_propositional_subsumption,[status(thm)],[c_36,c_44]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_1914,plain,
% 4.08/0.99      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 4.08/0.99      | ~ l1_pre_topc(X1)
% 4.08/0.99      | sK4 != X0
% 4.08/0.99      | sK3 != X1 ),
% 4.08/0.99      inference(resolution_lifted,[status(thm)],[c_33,c_286]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_1915,plain,
% 4.08/0.99      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 4.08/0.99      | ~ l1_pre_topc(sK3) ),
% 4.08/0.99      inference(unflattening,[status(thm)],[c_1914]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_45,negated_conjecture,
% 4.08/0.99      ( l1_pre_topc(sK3) ),
% 4.08/0.99      inference(cnf_transformation,[],[f103]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_1917,plain,
% 4.08/0.99      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 4.08/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1915,c_45]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_4232,plain,
% 4.08/0.99      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 4.08/0.99      inference(subtyping,[status(esa)],[c_1917]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_5003,plain,
% 4.08/0.99      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 4.08/0.99      inference(predicate_to_equality,[status(thm)],[c_4232]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_3,plain,
% 4.08/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.08/0.99      | ~ v2_pre_topc(X1)
% 4.08/0.99      | v2_struct_0(X1)
% 4.08/0.99      | ~ l1_pre_topc(X1)
% 4.08/0.99      | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1)) ),
% 4.08/0.99      inference(cnf_transformation,[],[f69]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_47,negated_conjecture,
% 4.08/0.99      ( ~ v2_struct_0(sK3) ),
% 4.08/0.99      inference(cnf_transformation,[],[f101]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_3644,plain,
% 4.08/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.08/0.99      | ~ v2_pre_topc(X1)
% 4.08/0.99      | ~ l1_pre_topc(X1)
% 4.08/0.99      | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1))
% 4.08/0.99      | sK3 != X1 ),
% 4.08/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_47]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_3645,plain,
% 4.08/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 4.08/0.99      | ~ v2_pre_topc(sK3)
% 4.08/0.99      | ~ l1_pre_topc(sK3)
% 4.08/0.99      | k7_tmap_1(sK3,X0) = k6_partfun1(u1_struct_0(sK3)) ),
% 4.08/0.99      inference(unflattening,[status(thm)],[c_3644]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_46,negated_conjecture,
% 4.08/0.99      ( v2_pre_topc(sK3) ),
% 4.08/0.99      inference(cnf_transformation,[],[f102]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_3649,plain,
% 4.08/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 4.08/0.99      | k7_tmap_1(sK3,X0) = k6_partfun1(u1_struct_0(sK3)) ),
% 4.08/0.99      inference(global_propositional_subsumption,
% 4.08/0.99                [status(thm)],
% 4.08/0.99                [c_3645,c_46,c_45]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_4206,plain,
% 4.08/0.99      ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK3)))
% 4.08/0.99      | k7_tmap_1(sK3,X0_58) = k6_partfun1(u1_struct_0(sK3)) ),
% 4.08/0.99      inference(subtyping,[status(esa)],[c_3649]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_5028,plain,
% 4.08/0.99      ( k7_tmap_1(sK3,X0_58) = k6_partfun1(u1_struct_0(sK3))
% 4.08/0.99      | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 4.08/0.99      inference(predicate_to_equality,[status(thm)],[c_4206]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_5860,plain,
% 4.08/0.99      ( k7_tmap_1(sK3,u1_struct_0(sK4)) = k6_partfun1(u1_struct_0(sK3)) ),
% 4.08/0.99      inference(superposition,[status(thm)],[c_5003,c_5028]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_16,plain,
% 4.08/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.08/0.99      | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
% 4.08/0.99      | ~ v2_pre_topc(X1)
% 4.08/0.99      | v2_struct_0(X1)
% 4.08/0.99      | ~ l1_pre_topc(X1) ),
% 4.08/0.99      inference(cnf_transformation,[],[f84]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_3626,plain,
% 4.08/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.08/0.99      | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
% 4.08/0.99      | ~ v2_pre_topc(X1)
% 4.08/0.99      | ~ l1_pre_topc(X1)
% 4.08/0.99      | sK3 != X1 ),
% 4.08/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_47]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_3627,plain,
% 4.08/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 4.08/0.99      | m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))))
% 4.08/0.99      | ~ v2_pre_topc(sK3)
% 4.08/0.99      | ~ l1_pre_topc(sK3) ),
% 4.08/0.99      inference(unflattening,[status(thm)],[c_3626]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_3631,plain,
% 4.08/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 4.08/0.99      | m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0))))) ),
% 4.08/0.99      inference(global_propositional_subsumption,
% 4.08/0.99                [status(thm)],
% 4.08/0.99                [c_3627,c_46,c_45]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_4207,plain,
% 4.08/0.99      ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK3)))
% 4.08/0.99      | m1_subset_1(k7_tmap_1(sK3,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0_58))))) ),
% 4.08/0.99      inference(subtyping,[status(esa)],[c_3631]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_5027,plain,
% 4.08/0.99      ( m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 4.08/0.99      | m1_subset_1(k7_tmap_1(sK3,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0_58))))) = iProver_top ),
% 4.08/0.99      inference(predicate_to_equality,[status(thm)],[c_4207]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_6907,plain,
% 4.08/0.99      ( m1_subset_1(k6_partfun1(u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))))) = iProver_top
% 4.08/0.99      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 4.08/0.99      inference(superposition,[status(thm)],[c_5860,c_5027]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_7,plain,
% 4.08/0.99      ( ~ m1_pre_topc(X0,X1)
% 4.08/0.99      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 4.08/0.99      | ~ v1_pre_topc(k8_tmap_1(X1,X0))
% 4.08/0.99      | ~ v2_pre_topc(X1)
% 4.08/0.99      | ~ v2_pre_topc(k8_tmap_1(X1,X0))
% 4.08/0.99      | v2_struct_0(X1)
% 4.08/0.99      | ~ l1_pre_topc(X1)
% 4.08/0.99      | ~ l1_pre_topc(k8_tmap_1(X1,X0))
% 4.08/0.99      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 4.08/0.99      inference(cnf_transformation,[],[f115]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_21,plain,
% 4.08/0.99      ( ~ m1_pre_topc(X0,X1)
% 4.08/0.99      | v1_pre_topc(k8_tmap_1(X1,X0))
% 4.08/0.99      | ~ v2_pre_topc(X1)
% 4.08/0.99      | v2_struct_0(X1)
% 4.08/0.99      | ~ l1_pre_topc(X1) ),
% 4.08/0.99      inference(cnf_transformation,[],[f85]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_20,plain,
% 4.08/0.99      ( ~ m1_pre_topc(X0,X1)
% 4.08/0.99      | ~ v2_pre_topc(X1)
% 4.08/0.99      | v2_pre_topc(k8_tmap_1(X1,X0))
% 4.08/0.99      | v2_struct_0(X1)
% 4.08/0.99      | ~ l1_pre_topc(X1) ),
% 4.08/0.99      inference(cnf_transformation,[],[f86]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_19,plain,
% 4.08/0.99      ( ~ m1_pre_topc(X0,X1)
% 4.08/0.99      | ~ v2_pre_topc(X1)
% 4.08/0.99      | v2_struct_0(X1)
% 4.08/0.99      | ~ l1_pre_topc(X1)
% 4.08/0.99      | l1_pre_topc(k8_tmap_1(X1,X0)) ),
% 4.08/0.99      inference(cnf_transformation,[],[f87]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_353,plain,
% 4.08/0.99      ( ~ l1_pre_topc(X1)
% 4.08/0.99      | v2_struct_0(X1)
% 4.08/0.99      | ~ m1_pre_topc(X0,X1)
% 4.08/0.99      | ~ v2_pre_topc(X1)
% 4.08/0.99      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 4.08/0.99      inference(global_propositional_subsumption,
% 4.08/0.99                [status(thm)],
% 4.08/0.99                [c_7,c_33,c_21,c_20,c_19]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_354,plain,
% 4.08/0.99      ( ~ m1_pre_topc(X0,X1)
% 4.08/0.99      | ~ v2_pre_topc(X1)
% 4.08/0.99      | v2_struct_0(X1)
% 4.08/0.99      | ~ l1_pre_topc(X1)
% 4.08/0.99      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 4.08/0.99      inference(renaming,[status(thm)],[c_353]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_1892,plain,
% 4.08/0.99      ( ~ v2_pre_topc(X0)
% 4.08/0.99      | v2_struct_0(X0)
% 4.08/0.99      | ~ l1_pre_topc(X0)
% 4.08/0.99      | k6_tmap_1(X0,u1_struct_0(X1)) = k8_tmap_1(X0,X1)
% 4.08/0.99      | sK4 != X1
% 4.08/0.99      | sK3 != X0 ),
% 4.08/0.99      inference(resolution_lifted,[status(thm)],[c_354,c_286]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_1893,plain,
% 4.08/0.99      ( ~ v2_pre_topc(sK3)
% 4.08/0.99      | v2_struct_0(sK3)
% 4.08/0.99      | ~ l1_pre_topc(sK3)
% 4.08/0.99      | k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4) ),
% 4.08/0.99      inference(unflattening,[status(thm)],[c_1892]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_1895,plain,
% 4.08/0.99      ( k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4) ),
% 4.08/0.99      inference(global_propositional_subsumption,
% 4.08/0.99                [status(thm)],
% 4.08/0.99                [c_1893,c_47,c_46,c_45]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_4233,plain,
% 4.08/0.99      ( k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4) ),
% 4.08/0.99      inference(subtyping,[status(esa)],[c_1895]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_26,plain,
% 4.08/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.08/0.99      | ~ v2_pre_topc(X1)
% 4.08/0.99      | v2_struct_0(X1)
% 4.08/0.99      | ~ l1_pre_topc(X1)
% 4.08/0.99      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
% 4.08/0.99      inference(cnf_transformation,[],[f91]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_3572,plain,
% 4.08/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.08/0.99      | ~ v2_pre_topc(X1)
% 4.08/0.99      | ~ l1_pre_topc(X1)
% 4.08/0.99      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1)
% 4.08/0.99      | sK3 != X1 ),
% 4.08/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_47]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_3573,plain,
% 4.08/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 4.08/0.99      | ~ v2_pre_topc(sK3)
% 4.08/0.99      | ~ l1_pre_topc(sK3)
% 4.08/0.99      | u1_struct_0(k6_tmap_1(sK3,X0)) = u1_struct_0(sK3) ),
% 4.08/0.99      inference(unflattening,[status(thm)],[c_3572]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_3577,plain,
% 4.08/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 4.08/0.99      | u1_struct_0(k6_tmap_1(sK3,X0)) = u1_struct_0(sK3) ),
% 4.08/0.99      inference(global_propositional_subsumption,
% 4.08/0.99                [status(thm)],
% 4.08/0.99                [c_3573,c_46,c_45]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_4210,plain,
% 4.08/0.99      ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK3)))
% 4.08/0.99      | u1_struct_0(k6_tmap_1(sK3,X0_58)) = u1_struct_0(sK3) ),
% 4.08/0.99      inference(subtyping,[status(esa)],[c_3577]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_5024,plain,
% 4.08/0.99      ( u1_struct_0(k6_tmap_1(sK3,X0_58)) = u1_struct_0(sK3)
% 4.08/0.99      | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 4.08/0.99      inference(predicate_to_equality,[status(thm)],[c_4210]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_5719,plain,
% 4.08/0.99      ( u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))) = u1_struct_0(sK3) ),
% 4.08/0.99      inference(superposition,[status(thm)],[c_5003,c_5024]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_5721,plain,
% 4.08/0.99      ( u1_struct_0(k8_tmap_1(sK3,sK4)) = u1_struct_0(sK3) ),
% 4.08/0.99      inference(light_normalisation,[status(thm)],[c_5719,c_4233]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_6916,plain,
% 4.08/0.99      ( m1_subset_1(k6_partfun1(u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) = iProver_top
% 4.08/0.99      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 4.08/0.99      inference(light_normalisation,[status(thm)],[c_6907,c_4233,c_5721]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_50,plain,
% 4.08/0.99      ( l1_pre_topc(sK3) = iProver_top ),
% 4.08/0.99      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_34,plain,
% 4.08/0.99      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 4.08/0.99      inference(cnf_transformation,[],[f100]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_61,plain,
% 4.08/0.99      ( m1_pre_topc(X0,X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 4.08/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_63,plain,
% 4.08/0.99      ( m1_pre_topc(sK3,sK3) = iProver_top | l1_pre_topc(sK3) != iProver_top ),
% 4.08/0.99      inference(instantiation,[status(thm)],[c_61]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_64,plain,
% 4.08/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 4.08/0.99      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 4.08/0.99      | l1_pre_topc(X1) != iProver_top ),
% 4.08/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_66,plain,
% 4.08/0.99      ( m1_pre_topc(sK3,sK3) != iProver_top
% 4.08/0.99      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 4.08/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 4.08/0.99      inference(instantiation,[status(thm)],[c_64]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_1637,plain,
% 4.08/0.99      ( ~ v2_pre_topc(X0)
% 4.08/0.99      | v2_struct_0(X0)
% 4.08/0.99      | ~ l1_pre_topc(X0)
% 4.08/0.99      | ~ l1_pre_topc(X1)
% 4.08/0.99      | X1 != X0
% 4.08/0.99      | X1 != X2
% 4.08/0.99      | k6_tmap_1(X0,u1_struct_0(X2)) = k8_tmap_1(X0,X2) ),
% 4.08/0.99      inference(resolution_lifted,[status(thm)],[c_354,c_34]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_1638,plain,
% 4.08/0.99      ( ~ v2_pre_topc(X0)
% 4.08/0.99      | v2_struct_0(X0)
% 4.08/0.99      | ~ l1_pre_topc(X0)
% 4.08/0.99      | k6_tmap_1(X0,u1_struct_0(X0)) = k8_tmap_1(X0,X0) ),
% 4.08/0.99      inference(unflattening,[status(thm)],[c_1637]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_3371,plain,
% 4.08/0.99      ( ~ v2_pre_topc(X0)
% 4.08/0.99      | ~ l1_pre_topc(X0)
% 4.08/0.99      | k6_tmap_1(X0,u1_struct_0(X0)) = k8_tmap_1(X0,X0)
% 4.08/0.99      | sK3 != X0 ),
% 4.08/0.99      inference(resolution_lifted,[status(thm)],[c_1638,c_47]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_3372,plain,
% 4.08/0.99      ( ~ v2_pre_topc(sK3)
% 4.08/0.99      | ~ l1_pre_topc(sK3)
% 4.08/0.99      | k6_tmap_1(sK3,u1_struct_0(sK3)) = k8_tmap_1(sK3,sK3) ),
% 4.08/0.99      inference(unflattening,[status(thm)],[c_3371]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_62,plain,
% 4.08/1.00      ( m1_pre_topc(sK3,sK3) | ~ l1_pre_topc(sK3) ),
% 4.08/1.00      inference(instantiation,[status(thm)],[c_34]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_65,plain,
% 4.08/1.00      ( ~ m1_pre_topc(sK3,sK3)
% 4.08/1.00      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 4.08/1.00      | ~ l1_pre_topc(sK3) ),
% 4.08/1.00      inference(instantiation,[status(thm)],[c_33]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_101,plain,
% 4.08/1.00      ( ~ m1_pre_topc(sK3,sK3)
% 4.08/1.00      | v1_pre_topc(k8_tmap_1(sK3,sK3))
% 4.08/1.00      | ~ v2_pre_topc(sK3)
% 4.08/1.00      | v2_struct_0(sK3)
% 4.08/1.00      | ~ l1_pre_topc(sK3) ),
% 4.08/1.00      inference(instantiation,[status(thm)],[c_21]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_104,plain,
% 4.08/1.00      ( ~ m1_pre_topc(sK3,sK3)
% 4.08/1.00      | v2_pre_topc(k8_tmap_1(sK3,sK3))
% 4.08/1.00      | ~ v2_pre_topc(sK3)
% 4.08/1.00      | v2_struct_0(sK3)
% 4.08/1.00      | ~ l1_pre_topc(sK3) ),
% 4.08/1.00      inference(instantiation,[status(thm)],[c_20]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_107,plain,
% 4.08/1.00      ( ~ m1_pre_topc(sK3,sK3)
% 4.08/1.00      | ~ v2_pre_topc(sK3)
% 4.08/1.00      | v2_struct_0(sK3)
% 4.08/1.00      | l1_pre_topc(k8_tmap_1(sK3,sK3))
% 4.08/1.00      | ~ l1_pre_topc(sK3) ),
% 4.08/1.00      inference(instantiation,[status(thm)],[c_19]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_143,plain,
% 4.08/1.00      ( ~ m1_pre_topc(sK3,sK3)
% 4.08/1.00      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 4.08/1.00      | ~ v1_pre_topc(k8_tmap_1(sK3,sK3))
% 4.08/1.00      | ~ v2_pre_topc(k8_tmap_1(sK3,sK3))
% 4.08/1.00      | ~ v2_pre_topc(sK3)
% 4.08/1.00      | v2_struct_0(sK3)
% 4.08/1.00      | ~ l1_pre_topc(k8_tmap_1(sK3,sK3))
% 4.08/1.00      | ~ l1_pre_topc(sK3)
% 4.08/1.00      | k6_tmap_1(sK3,u1_struct_0(sK3)) = k8_tmap_1(sK3,sK3) ),
% 4.08/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_3374,plain,
% 4.08/1.00      ( k6_tmap_1(sK3,u1_struct_0(sK3)) = k8_tmap_1(sK3,sK3) ),
% 4.08/1.00      inference(global_propositional_subsumption,
% 4.08/1.00                [status(thm)],
% 4.08/1.00                [c_3372,c_47,c_46,c_45,c_62,c_65,c_101,c_104,c_107,c_143]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_4216,plain,
% 4.08/1.00      ( k6_tmap_1(sK3,u1_struct_0(sK3)) = k8_tmap_1(sK3,sK3) ),
% 4.08/1.00      inference(subtyping,[status(esa)],[c_3374]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_6365,plain,
% 4.08/1.00      ( m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))))) = iProver_top
% 4.08/1.00      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_4216,c_5027]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1670,plain,
% 4.08/1.00      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 4.08/1.00      | ~ l1_pre_topc(X1)
% 4.08/1.00      | ~ l1_pre_topc(X2)
% 4.08/1.00      | X2 != X1
% 4.08/1.00      | X2 != X0 ),
% 4.08/1.00      inference(resolution_lifted,[status(thm)],[c_33,c_34]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1671,plain,
% 4.08/1.00      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 4.08/1.00      | ~ l1_pre_topc(X0) ),
% 4.08/1.00      inference(unflattening,[status(thm)],[c_1670]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_3865,plain,
% 4.08/1.00      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | sK3 != X0 ),
% 4.08/1.00      inference(resolution_lifted,[status(thm)],[c_1671,c_45]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_3866,plain,
% 4.08/1.00      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 4.08/1.00      inference(unflattening,[status(thm)],[c_3865]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_4197,plain,
% 4.08/1.00      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 4.08/1.00      inference(subtyping,[status(esa)],[c_3866]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_5033,plain,
% 4.08/1.00      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_4197]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_5717,plain,
% 4.08/1.00      ( u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3))) = u1_struct_0(sK3) ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_5033,c_5024]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_5728,plain,
% 4.08/1.00      ( u1_struct_0(k8_tmap_1(sK3,sK3)) = u1_struct_0(sK3) ),
% 4.08/1.00      inference(light_normalisation,[status(thm)],[c_5717,c_4216]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_5858,plain,
% 4.08/1.00      ( k7_tmap_1(sK3,u1_struct_0(sK3)) = k6_partfun1(u1_struct_0(sK3)) ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_5033,c_5028]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_6374,plain,
% 4.08/1.00      ( m1_subset_1(k6_partfun1(u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) = iProver_top
% 4.08/1.00      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 4.08/1.00      inference(light_normalisation,[status(thm)],[c_6365,c_5728,c_5858]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_7000,plain,
% 4.08/1.00      ( m1_subset_1(k6_partfun1(u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) = iProver_top ),
% 4.08/1.00      inference(global_propositional_subsumption,
% 4.08/1.00                [status(thm)],
% 4.08/1.00                [c_6916,c_50,c_63,c_66,c_6374]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_9,plain,
% 4.08/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
% 4.08/1.00      | ~ m1_pre_topc(X2,X1)
% 4.08/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
% 4.08/1.00      | ~ v2_pre_topc(X1)
% 4.08/1.00      | ~ v1_funct_1(X0)
% 4.08/1.00      | v2_struct_0(X1)
% 4.08/1.00      | ~ l1_pre_topc(X1)
% 4.08/1.00      | sK1(X1,X2,X0) = u1_struct_0(X2)
% 4.08/1.00      | k9_tmap_1(X1,X2) = X0 ),
% 4.08/1.00      inference(cnf_transformation,[],[f76]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_2125,plain,
% 4.08/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
% 4.08/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
% 4.08/1.00      | ~ v2_pre_topc(X1)
% 4.08/1.00      | ~ v1_funct_1(X0)
% 4.08/1.00      | v2_struct_0(X1)
% 4.08/1.00      | ~ l1_pre_topc(X1)
% 4.08/1.00      | ~ l1_pre_topc(X3)
% 4.08/1.00      | X3 != X1
% 4.08/1.00      | X3 != X2
% 4.08/1.00      | sK1(X1,X2,X0) = u1_struct_0(X2)
% 4.08/1.00      | k9_tmap_1(X1,X2) = X0 ),
% 4.08/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_34]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_2126,plain,
% 4.08/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))
% 4.08/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))))
% 4.08/1.00      | ~ v2_pre_topc(X1)
% 4.08/1.00      | ~ v1_funct_1(X0)
% 4.08/1.00      | v2_struct_0(X1)
% 4.08/1.00      | ~ l1_pre_topc(X1)
% 4.08/1.00      | sK1(X1,X1,X0) = u1_struct_0(X1)
% 4.08/1.00      | k9_tmap_1(X1,X1) = X0 ),
% 4.08/1.00      inference(unflattening,[status(thm)],[c_2125]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_3468,plain,
% 4.08/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))
% 4.08/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))))
% 4.08/1.00      | ~ v2_pre_topc(X1)
% 4.08/1.00      | ~ v1_funct_1(X0)
% 4.08/1.00      | ~ l1_pre_topc(X1)
% 4.08/1.00      | sK1(X1,X1,X0) = u1_struct_0(X1)
% 4.08/1.00      | k9_tmap_1(X1,X1) = X0
% 4.08/1.00      | sK3 != X1 ),
% 4.08/1.00      inference(resolution_lifted,[status(thm)],[c_2126,c_47]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_3469,plain,
% 4.08/1.00      ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
% 4.08/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
% 4.08/1.00      | ~ v2_pre_topc(sK3)
% 4.08/1.00      | ~ v1_funct_1(X0)
% 4.08/1.00      | ~ l1_pre_topc(sK3)
% 4.08/1.00      | sK1(sK3,sK3,X0) = u1_struct_0(sK3)
% 4.08/1.00      | k9_tmap_1(sK3,sK3) = X0 ),
% 4.08/1.00      inference(unflattening,[status(thm)],[c_3468]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_3473,plain,
% 4.08/1.00      ( ~ v1_funct_1(X0)
% 4.08/1.00      | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
% 4.08/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
% 4.08/1.00      | sK1(sK3,sK3,X0) = u1_struct_0(sK3)
% 4.08/1.00      | k9_tmap_1(sK3,sK3) = X0 ),
% 4.08/1.00      inference(global_propositional_subsumption,
% 4.08/1.00                [status(thm)],
% 4.08/1.00                [c_3469,c_46,c_45]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_3474,plain,
% 4.08/1.00      ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
% 4.08/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
% 4.08/1.00      | ~ v1_funct_1(X0)
% 4.08/1.00      | sK1(sK3,sK3,X0) = u1_struct_0(sK3)
% 4.08/1.00      | k9_tmap_1(sK3,sK3) = X0 ),
% 4.08/1.00      inference(renaming,[status(thm)],[c_3473]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_4212,plain,
% 4.08/1.00      ( ~ v1_funct_2(X0_58,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
% 4.08/1.00      | ~ m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
% 4.08/1.00      | ~ v1_funct_1(X0_58)
% 4.08/1.00      | sK1(sK3,sK3,X0_58) = u1_struct_0(sK3)
% 4.08/1.00      | k9_tmap_1(sK3,sK3) = X0_58 ),
% 4.08/1.00      inference(subtyping,[status(esa)],[c_3474]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_5022,plain,
% 4.08/1.00      ( sK1(sK3,sK3,X0_58) = u1_struct_0(sK3)
% 4.08/1.00      | k9_tmap_1(sK3,sK3) = X0_58
% 4.08/1.00      | v1_funct_2(X0_58,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))) != iProver_top
% 4.08/1.00      | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))))) != iProver_top
% 4.08/1.00      | v1_funct_1(X0_58) != iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_4212]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_6771,plain,
% 4.08/1.00      ( sK1(sK3,sK3,X0_58) = u1_struct_0(sK3)
% 4.08/1.00      | k9_tmap_1(sK3,sK3) = X0_58
% 4.08/1.00      | v1_funct_2(X0_58,u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
% 4.08/1.00      | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) != iProver_top
% 4.08/1.00      | v1_funct_1(X0_58) != iProver_top ),
% 4.08/1.00      inference(light_normalisation,[status(thm)],[c_5022,c_5728]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_7007,plain,
% 4.08/1.00      ( sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3))) = u1_struct_0(sK3)
% 4.08/1.00      | k9_tmap_1(sK3,sK3) = k6_partfun1(u1_struct_0(sK3))
% 4.08/1.00      | v1_funct_2(k6_partfun1(u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
% 4.08/1.00      | v1_funct_1(k6_partfun1(u1_struct_0(sK3))) != iProver_top ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_7000,c_6771]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_18,plain,
% 4.08/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.08/1.00      | ~ v2_pre_topc(X1)
% 4.08/1.00      | v1_funct_1(k7_tmap_1(X1,X0))
% 4.08/1.00      | v2_struct_0(X1)
% 4.08/1.00      | ~ l1_pre_topc(X1) ),
% 4.08/1.00      inference(cnf_transformation,[],[f82]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_3608,plain,
% 4.08/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.08/1.00      | ~ v2_pre_topc(X1)
% 4.08/1.00      | v1_funct_1(k7_tmap_1(X1,X0))
% 4.08/1.00      | ~ l1_pre_topc(X1)
% 4.08/1.00      | sK3 != X1 ),
% 4.08/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_47]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_3609,plain,
% 4.08/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 4.08/1.00      | ~ v2_pre_topc(sK3)
% 4.08/1.00      | v1_funct_1(k7_tmap_1(sK3,X0))
% 4.08/1.00      | ~ l1_pre_topc(sK3) ),
% 4.08/1.00      inference(unflattening,[status(thm)],[c_3608]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_3613,plain,
% 4.08/1.00      ( v1_funct_1(k7_tmap_1(sK3,X0))
% 4.08/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 4.08/1.00      inference(global_propositional_subsumption,
% 4.08/1.00                [status(thm)],
% 4.08/1.00                [c_3609,c_46,c_45]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_3614,plain,
% 4.08/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 4.08/1.00      | v1_funct_1(k7_tmap_1(sK3,X0)) ),
% 4.08/1.00      inference(renaming,[status(thm)],[c_3613]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_4208,plain,
% 4.08/1.00      ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK3)))
% 4.08/1.00      | v1_funct_1(k7_tmap_1(sK3,X0_58)) ),
% 4.08/1.00      inference(subtyping,[status(esa)],[c_3614]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_5026,plain,
% 4.08/1.00      ( m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 4.08/1.00      | v1_funct_1(k7_tmap_1(sK3,X0_58)) = iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_4208]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_5700,plain,
% 4.08/1.00      ( v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK3))) = iProver_top ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_5033,c_5026]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_5988,plain,
% 4.08/1.00      ( v1_funct_1(k6_partfun1(u1_struct_0(sK3))) = iProver_top ),
% 4.08/1.00      inference(demodulation,[status(thm)],[c_5858,c_5700]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_17,plain,
% 4.08/1.00      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
% 4.08/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 4.08/1.00      | ~ v2_pre_topc(X0)
% 4.08/1.00      | v2_struct_0(X0)
% 4.08/1.00      | ~ l1_pre_topc(X0) ),
% 4.08/1.00      inference(cnf_transformation,[],[f83]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_3450,plain,
% 4.08/1.00      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
% 4.08/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 4.08/1.00      | ~ v2_pre_topc(X0)
% 4.08/1.00      | ~ l1_pre_topc(X0)
% 4.08/1.00      | sK3 != X0 ),
% 4.08/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_47]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_3451,plain,
% 4.08/1.00      ( v1_funct_2(k7_tmap_1(sK3,X0),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))
% 4.08/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 4.08/1.00      | ~ v2_pre_topc(sK3)
% 4.08/1.00      | ~ l1_pre_topc(sK3) ),
% 4.08/1.00      inference(unflattening,[status(thm)],[c_3450]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_3455,plain,
% 4.08/1.00      ( v1_funct_2(k7_tmap_1(sK3,X0),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))
% 4.08/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 4.08/1.00      inference(global_propositional_subsumption,
% 4.08/1.00                [status(thm)],
% 4.08/1.00                [c_3451,c_46,c_45]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_4213,plain,
% 4.08/1.00      ( v1_funct_2(k7_tmap_1(sK3,X0_58),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0_58)))
% 4.08/1.00      | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 4.08/1.00      inference(subtyping,[status(esa)],[c_3455]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_5021,plain,
% 4.08/1.00      ( v1_funct_2(k7_tmap_1(sK3,X0_58),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0_58))) = iProver_top
% 4.08/1.00      | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_4213]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_6344,plain,
% 4.08/1.00      ( v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))) = iProver_top
% 4.08/1.00      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_4216,c_5021]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_6353,plain,
% 4.08/1.00      ( v1_funct_2(k6_partfun1(u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK3)) = iProver_top
% 4.08/1.00      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 4.08/1.00      inference(light_normalisation,[status(thm)],[c_6344,c_5728,c_5858]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_9052,plain,
% 4.08/1.00      ( sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3))) = u1_struct_0(sK3)
% 4.08/1.00      | k9_tmap_1(sK3,sK3) = k6_partfun1(u1_struct_0(sK3)) ),
% 4.08/1.00      inference(global_propositional_subsumption,
% 4.08/1.00                [status(thm)],
% 4.08/1.00                [c_7007,c_50,c_63,c_66,c_5988,c_6353]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_2,plain,
% 4.08/1.00      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
% 4.08/1.00      | ~ v1_funct_2(X5,X2,X3)
% 4.08/1.00      | ~ v1_funct_2(X4,X0,X1)
% 4.08/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 4.08/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.08/1.00      | ~ v1_funct_1(X5)
% 4.08/1.00      | ~ v1_funct_1(X4)
% 4.08/1.00      | v1_xboole_0(X1)
% 4.08/1.00      | v1_xboole_0(X3) ),
% 4.08/1.00      inference(cnf_transformation,[],[f68]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_8,plain,
% 4.08/1.00      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2)))
% 4.08/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 4.08/1.00      | ~ m1_pre_topc(X1,X0)
% 4.08/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 4.08/1.00      | ~ v2_pre_topc(X0)
% 4.08/1.00      | ~ v1_funct_1(X2)
% 4.08/1.00      | v2_struct_0(X0)
% 4.08/1.00      | ~ l1_pre_topc(X0)
% 4.08/1.00      | k9_tmap_1(X0,X1) = X2 ),
% 4.08/1.00      inference(cnf_transformation,[],[f77]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1521,plain,
% 4.08/1.00      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2)))
% 4.08/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 4.08/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 4.08/1.00      | ~ v2_pre_topc(X0)
% 4.08/1.00      | ~ v1_funct_1(X2)
% 4.08/1.00      | v2_struct_0(X0)
% 4.08/1.00      | ~ l1_pre_topc(X0)
% 4.08/1.00      | ~ l1_pre_topc(X3)
% 4.08/1.00      | X3 != X1
% 4.08/1.00      | X3 != X0
% 4.08/1.00      | k9_tmap_1(X0,X1) = X2 ),
% 4.08/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_34]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1522,plain,
% 4.08/1.00      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X0,X1))),X1,k7_tmap_1(X0,sK1(X0,X0,X1)))
% 4.08/1.00      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))
% 4.08/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))))
% 4.08/1.00      | ~ v2_pre_topc(X0)
% 4.08/1.00      | ~ v1_funct_1(X1)
% 4.08/1.00      | v2_struct_0(X0)
% 4.08/1.00      | ~ l1_pre_topc(X0)
% 4.08/1.00      | k9_tmap_1(X0,X0) = X1 ),
% 4.08/1.00      inference(unflattening,[status(thm)],[c_1521]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_3379,plain,
% 4.08/1.00      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X0,X1))),X1,k7_tmap_1(X0,sK1(X0,X0,X1)))
% 4.08/1.00      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))
% 4.08/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X0)))))
% 4.08/1.00      | ~ v2_pre_topc(X0)
% 4.08/1.00      | ~ v1_funct_1(X1)
% 4.08/1.00      | ~ l1_pre_topc(X0)
% 4.08/1.00      | k9_tmap_1(X0,X0) = X1
% 4.08/1.00      | sK3 != X0 ),
% 4.08/1.00      inference(resolution_lifted,[status(thm)],[c_1522,c_47]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_3380,plain,
% 4.08/1.00      ( ~ r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X0))),X0,k7_tmap_1(sK3,sK1(sK3,sK3,X0)))
% 4.08/1.00      | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
% 4.08/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
% 4.08/1.00      | ~ v2_pre_topc(sK3)
% 4.08/1.00      | ~ v1_funct_1(X0)
% 4.08/1.00      | ~ l1_pre_topc(sK3)
% 4.08/1.00      | k9_tmap_1(sK3,sK3) = X0 ),
% 4.08/1.00      inference(unflattening,[status(thm)],[c_3379]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_3384,plain,
% 4.08/1.00      ( ~ v1_funct_1(X0)
% 4.08/1.00      | ~ r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X0))),X0,k7_tmap_1(sK3,sK1(sK3,sK3,X0)))
% 4.08/1.00      | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
% 4.08/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
% 4.08/1.00      | k9_tmap_1(sK3,sK3) = X0 ),
% 4.08/1.00      inference(global_propositional_subsumption,
% 4.08/1.00                [status(thm)],
% 4.08/1.00                [c_3380,c_46,c_45]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_3385,plain,
% 4.08/1.00      ( ~ r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X0))),X0,k7_tmap_1(sK3,sK1(sK3,sK3,X0)))
% 4.08/1.00      | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
% 4.08/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
% 4.08/1.00      | ~ v1_funct_1(X0)
% 4.08/1.00      | k9_tmap_1(sK3,sK3) = X0 ),
% 4.08/1.00      inference(renaming,[status(thm)],[c_3384]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_3984,plain,
% 4.08/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 4.08/1.00      | ~ v1_funct_2(X3,X4,X5)
% 4.08/1.00      | ~ v1_funct_2(X6,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
% 4.08/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.08/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 4.08/1.00      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
% 4.08/1.00      | ~ v1_funct_1(X0)
% 4.08/1.00      | ~ v1_funct_1(X3)
% 4.08/1.00      | ~ v1_funct_1(X6)
% 4.08/1.00      | v1_xboole_0(X5)
% 4.08/1.00      | v1_xboole_0(X2)
% 4.08/1.00      | X6 != X3
% 4.08/1.00      | k9_tmap_1(sK3,sK3) = X6
% 4.08/1.00      | k7_tmap_1(sK3,sK1(sK3,sK3,X6)) != X3
% 4.08/1.00      | u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X6))) != X2
% 4.08/1.00      | u1_struct_0(k8_tmap_1(sK3,sK3)) != X5
% 4.08/1.00      | u1_struct_0(sK3) != X1
% 4.08/1.00      | u1_struct_0(sK3) != X4 ),
% 4.08/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_3385]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_3985,plain,
% 4.08/1.00      ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X1))))
% 4.08/1.00      | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
% 4.08/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X1))))))
% 4.08/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
% 4.08/1.00      | ~ v1_funct_1(X0)
% 4.08/1.00      | ~ v1_funct_1(X1)
% 4.08/1.00      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X1))))
% 4.08/1.00      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK3)))
% 4.08/1.00      | k9_tmap_1(sK3,sK3) = X1
% 4.08/1.00      | k7_tmap_1(sK3,sK1(sK3,sK3,X1)) != X1 ),
% 4.08/1.00      inference(unflattening,[status(thm)],[c_3984]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_4190,plain,
% 4.08/1.00      ( ~ v1_funct_2(X0_58,u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X1_58))))
% 4.08/1.00      | ~ v1_funct_2(X1_58,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
% 4.08/1.00      | ~ m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X1_58))))))
% 4.08/1.00      | ~ m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
% 4.08/1.00      | ~ v1_funct_1(X0_58)
% 4.08/1.00      | ~ v1_funct_1(X1_58)
% 4.08/1.00      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X1_58))))
% 4.08/1.00      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK3)))
% 4.08/1.00      | k9_tmap_1(sK3,sK3) = X1_58
% 4.08/1.00      | k7_tmap_1(sK3,sK1(sK3,sK3,X1_58)) != X1_58 ),
% 4.08/1.00      inference(subtyping,[status(esa)],[c_3985]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_5040,plain,
% 4.08/1.00      ( k9_tmap_1(sK3,sK3) = X0_58
% 4.08/1.00      | k7_tmap_1(sK3,sK1(sK3,sK3,X0_58)) != X0_58
% 4.08/1.00      | v1_funct_2(X1_58,u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X0_58)))) != iProver_top
% 4.08/1.00      | v1_funct_2(X0_58,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))) != iProver_top
% 4.08/1.00      | m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X0_58)))))) != iProver_top
% 4.08/1.00      | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))))) != iProver_top
% 4.08/1.00      | v1_funct_1(X0_58) != iProver_top
% 4.08/1.00      | v1_funct_1(X1_58) != iProver_top
% 4.08/1.00      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X0_58)))) = iProver_top
% 4.08/1.00      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK3))) = iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_4190]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_5813,plain,
% 4.08/1.00      ( k9_tmap_1(sK3,sK3) = X0_58
% 4.08/1.00      | k7_tmap_1(sK3,sK1(sK3,sK3,X0_58)) != X0_58
% 4.08/1.00      | v1_funct_2(X1_58,u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X0_58)))) != iProver_top
% 4.08/1.00      | v1_funct_2(X0_58,u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
% 4.08/1.00      | m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X0_58)))))) != iProver_top
% 4.08/1.00      | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) != iProver_top
% 4.08/1.00      | v1_funct_1(X1_58) != iProver_top
% 4.08/1.00      | v1_funct_1(X0_58) != iProver_top
% 4.08/1.00      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X0_58)))) = iProver_top
% 4.08/1.00      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 4.08/1.00      inference(demodulation,[status(thm)],[c_5728,c_5040]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_48,plain,
% 4.08/1.00      ( v2_struct_0(sK3) != iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1,plain,
% 4.08/1.00      ( v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | ~ l1_struct_0(X0) ),
% 4.08/1.00      inference(cnf_transformation,[],[f67]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_160,plain,
% 4.08/1.00      ( v2_struct_0(X0) = iProver_top
% 4.08/1.00      | v1_xboole_0(u1_struct_0(X0)) != iProver_top
% 4.08/1.00      | l1_struct_0(X0) != iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_162,plain,
% 4.08/1.00      ( v2_struct_0(sK3) = iProver_top
% 4.08/1.00      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top
% 4.08/1.00      | l1_struct_0(sK3) != iProver_top ),
% 4.08/1.00      inference(instantiation,[status(thm)],[c_160]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_0,plain,
% 4.08/1.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 4.08/1.00      inference(cnf_transformation,[],[f66]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_163,plain,
% 4.08/1.00      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_165,plain,
% 4.08/1.00      ( l1_pre_topc(sK3) != iProver_top | l1_struct_0(sK3) = iProver_top ),
% 4.08/1.00      inference(instantiation,[status(thm)],[c_163]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_6957,plain,
% 4.08/1.00      ( v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X0_58)))) = iProver_top
% 4.08/1.00      | v1_funct_1(X0_58) != iProver_top
% 4.08/1.00      | v1_funct_1(X1_58) != iProver_top
% 4.08/1.00      | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) != iProver_top
% 4.08/1.00      | m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X0_58)))))) != iProver_top
% 4.08/1.00      | v1_funct_2(X0_58,u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
% 4.08/1.00      | v1_funct_2(X1_58,u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X0_58)))) != iProver_top
% 4.08/1.00      | k7_tmap_1(sK3,sK1(sK3,sK3,X0_58)) != X0_58
% 4.08/1.00      | k9_tmap_1(sK3,sK3) = X0_58 ),
% 4.08/1.00      inference(global_propositional_subsumption,
% 4.08/1.00                [status(thm)],
% 4.08/1.00                [c_5813,c_48,c_50,c_162,c_165]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_6958,plain,
% 4.08/1.00      ( k9_tmap_1(sK3,sK3) = X0_58
% 4.08/1.00      | k7_tmap_1(sK3,sK1(sK3,sK3,X0_58)) != X0_58
% 4.08/1.00      | v1_funct_2(X1_58,u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X0_58)))) != iProver_top
% 4.08/1.00      | v1_funct_2(X0_58,u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
% 4.08/1.00      | m1_subset_1(X1_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X0_58)))))) != iProver_top
% 4.08/1.00      | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) != iProver_top
% 4.08/1.00      | v1_funct_1(X1_58) != iProver_top
% 4.08/1.00      | v1_funct_1(X0_58) != iProver_top
% 4.08/1.00      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X0_58)))) = iProver_top ),
% 4.08/1.00      inference(renaming,[status(thm)],[c_6957]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_9056,plain,
% 4.08/1.00      ( k9_tmap_1(sK3,sK3) = k6_partfun1(u1_struct_0(sK3))
% 4.08/1.00      | k7_tmap_1(sK3,u1_struct_0(sK3)) != k6_partfun1(u1_struct_0(sK3))
% 4.08/1.00      | v1_funct_2(X0_58,u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))) != iProver_top
% 4.08/1.00      | v1_funct_2(k6_partfun1(u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
% 4.08/1.00      | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))))) != iProver_top
% 4.08/1.00      | m1_subset_1(k6_partfun1(u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) != iProver_top
% 4.08/1.00      | v1_funct_1(X0_58) != iProver_top
% 4.08/1.00      | v1_funct_1(k6_partfun1(u1_struct_0(sK3))) != iProver_top
% 4.08/1.00      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))) = iProver_top ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_9052,c_6958]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_9057,plain,
% 4.08/1.00      ( k9_tmap_1(sK3,sK3) = k6_partfun1(u1_struct_0(sK3))
% 4.08/1.00      | k6_partfun1(u1_struct_0(sK3)) != k6_partfun1(u1_struct_0(sK3))
% 4.08/1.00      | v1_funct_2(X0_58,u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))) != iProver_top
% 4.08/1.00      | v1_funct_2(k6_partfun1(u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
% 4.08/1.00      | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))))) != iProver_top
% 4.08/1.00      | m1_subset_1(k6_partfun1(u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) != iProver_top
% 4.08/1.00      | v1_funct_1(X0_58) != iProver_top
% 4.08/1.00      | v1_funct_1(k6_partfun1(u1_struct_0(sK3))) != iProver_top
% 4.08/1.00      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))) = iProver_top ),
% 4.08/1.00      inference(light_normalisation,[status(thm)],[c_9056,c_5858]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_9058,plain,
% 4.08/1.00      ( k9_tmap_1(sK3,sK3) = k6_partfun1(u1_struct_0(sK3))
% 4.08/1.00      | v1_funct_2(X0_58,u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))) != iProver_top
% 4.08/1.00      | v1_funct_2(k6_partfun1(u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
% 4.08/1.00      | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))))) != iProver_top
% 4.08/1.00      | m1_subset_1(k6_partfun1(u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) != iProver_top
% 4.08/1.00      | v1_funct_1(X0_58) != iProver_top
% 4.08/1.00      | v1_funct_1(k6_partfun1(u1_struct_0(sK3))) != iProver_top
% 4.08/1.00      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))) = iProver_top ),
% 4.08/1.00      inference(equality_resolution_simp,[status(thm)],[c_9057]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_12822,plain,
% 4.08/1.00      ( v1_funct_1(X0_58) != iProver_top
% 4.08/1.00      | v1_funct_2(X0_58,u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))) != iProver_top
% 4.08/1.00      | k9_tmap_1(sK3,sK3) = k6_partfun1(u1_struct_0(sK3))
% 4.08/1.00      | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))))) != iProver_top
% 4.08/1.00      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))) = iProver_top ),
% 4.08/1.00      inference(global_propositional_subsumption,
% 4.08/1.00                [status(thm)],
% 4.08/1.00                [c_9058,c_50,c_63,c_66,c_5988,c_6353,c_6374]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_12823,plain,
% 4.08/1.00      ( k9_tmap_1(sK3,sK3) = k6_partfun1(u1_struct_0(sK3))
% 4.08/1.00      | v1_funct_2(X0_58,u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))) != iProver_top
% 4.08/1.00      | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))))) != iProver_top
% 4.08/1.00      | v1_funct_1(X0_58) != iProver_top
% 4.08/1.00      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))) = iProver_top ),
% 4.08/1.00      inference(renaming,[status(thm)],[c_12822]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_12836,plain,
% 4.08/1.00      ( k9_tmap_1(sK3,sK3) = k6_partfun1(u1_struct_0(sK3))
% 4.08/1.00      | v1_funct_2(X0_58,u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))) != iProver_top
% 4.08/1.00      | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3)))))) != iProver_top
% 4.08/1.00      | v1_funct_1(X0_58) != iProver_top
% 4.08/1.00      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))) = iProver_top ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_9052,c_12823]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_12842,plain,
% 4.08/1.00      ( k9_tmap_1(sK3,sK3) = k6_partfun1(u1_struct_0(sK3))
% 4.08/1.00      | v1_funct_2(X0_58,u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))) != iProver_top
% 4.08/1.00      | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) != iProver_top
% 4.08/1.00      | v1_funct_1(X0_58) != iProver_top
% 4.08/1.00      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))) = iProver_top ),
% 4.08/1.00      inference(light_normalisation,[status(thm)],[c_12836,c_4216,c_5728]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_10,plain,
% 4.08/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
% 4.08/1.00      | ~ m1_pre_topc(X2,X1)
% 4.08/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
% 4.08/1.00      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 4.08/1.00      | ~ v2_pre_topc(X1)
% 4.08/1.00      | ~ v1_funct_1(X0)
% 4.08/1.00      | v2_struct_0(X1)
% 4.08/1.00      | ~ l1_pre_topc(X1)
% 4.08/1.00      | k9_tmap_1(X1,X2) = X0 ),
% 4.08/1.00      inference(cnf_transformation,[],[f75]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_2095,plain,
% 4.08/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
% 4.08/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
% 4.08/1.00      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 4.08/1.00      | ~ v2_pre_topc(X1)
% 4.08/1.00      | ~ v1_funct_1(X0)
% 4.08/1.00      | v2_struct_0(X1)
% 4.08/1.00      | ~ l1_pre_topc(X1)
% 4.08/1.00      | ~ l1_pre_topc(X3)
% 4.08/1.00      | X3 != X1
% 4.08/1.00      | X3 != X2
% 4.08/1.00      | k9_tmap_1(X1,X2) = X0 ),
% 4.08/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_34]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_2096,plain,
% 4.08/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))
% 4.08/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))))
% 4.08/1.00      | m1_subset_1(sK1(X1,X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 4.08/1.00      | ~ v2_pre_topc(X1)
% 4.08/1.00      | ~ v1_funct_1(X0)
% 4.08/1.00      | v2_struct_0(X1)
% 4.08/1.00      | ~ l1_pre_topc(X1)
% 4.08/1.00      | k9_tmap_1(X1,X1) = X0 ),
% 4.08/1.00      inference(unflattening,[status(thm)],[c_2095]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_3495,plain,
% 4.08/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))
% 4.08/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X1)))))
% 4.08/1.00      | m1_subset_1(sK1(X1,X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 4.08/1.00      | ~ v2_pre_topc(X1)
% 4.08/1.00      | ~ v1_funct_1(X0)
% 4.08/1.00      | ~ l1_pre_topc(X1)
% 4.08/1.00      | k9_tmap_1(X1,X1) = X0
% 4.08/1.00      | sK3 != X1 ),
% 4.08/1.00      inference(resolution_lifted,[status(thm)],[c_2096,c_47]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_3496,plain,
% 4.08/1.00      ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
% 4.08/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
% 4.08/1.00      | m1_subset_1(sK1(sK3,sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 4.08/1.00      | ~ v2_pre_topc(sK3)
% 4.08/1.00      | ~ v1_funct_1(X0)
% 4.08/1.00      | ~ l1_pre_topc(sK3)
% 4.08/1.00      | k9_tmap_1(sK3,sK3) = X0 ),
% 4.08/1.00      inference(unflattening,[status(thm)],[c_3495]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_3500,plain,
% 4.08/1.00      ( ~ v1_funct_1(X0)
% 4.08/1.00      | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
% 4.08/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
% 4.08/1.00      | m1_subset_1(sK1(sK3,sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 4.08/1.00      | k9_tmap_1(sK3,sK3) = X0 ),
% 4.08/1.00      inference(global_propositional_subsumption,
% 4.08/1.00                [status(thm)],
% 4.08/1.00                [c_3496,c_46,c_45]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_3501,plain,
% 4.08/1.00      ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
% 4.08/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
% 4.08/1.00      | m1_subset_1(sK1(sK3,sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 4.08/1.00      | ~ v1_funct_1(X0)
% 4.08/1.00      | k9_tmap_1(sK3,sK3) = X0 ),
% 4.08/1.00      inference(renaming,[status(thm)],[c_3500]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_4211,plain,
% 4.08/1.00      ( ~ v1_funct_2(X0_58,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
% 4.08/1.00      | ~ m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
% 4.08/1.00      | m1_subset_1(sK1(sK3,sK3,X0_58),k1_zfmisc_1(u1_struct_0(sK3)))
% 4.08/1.00      | ~ v1_funct_1(X0_58)
% 4.08/1.00      | k9_tmap_1(sK3,sK3) = X0_58 ),
% 4.08/1.00      inference(subtyping,[status(esa)],[c_3501]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_5023,plain,
% 4.08/1.00      ( k9_tmap_1(sK3,sK3) = X0_58
% 4.08/1.00      | v1_funct_2(X0_58,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))) != iProver_top
% 4.08/1.00      | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))))) != iProver_top
% 4.08/1.00      | m1_subset_1(sK1(sK3,sK3,X0_58),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 4.08/1.00      | v1_funct_1(X0_58) != iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_4211]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_6865,plain,
% 4.08/1.00      ( k9_tmap_1(sK3,sK3) = X0_58
% 4.08/1.00      | v1_funct_2(X0_58,u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
% 4.08/1.00      | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) != iProver_top
% 4.08/1.00      | m1_subset_1(sK1(sK3,sK3,X0_58),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 4.08/1.00      | v1_funct_1(X0_58) != iProver_top ),
% 4.08/1.00      inference(light_normalisation,[status(thm)],[c_5023,c_5728]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_7005,plain,
% 4.08/1.00      ( k9_tmap_1(sK3,sK3) = k6_partfun1(u1_struct_0(sK3))
% 4.08/1.00      | v1_funct_2(k6_partfun1(u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
% 4.08/1.00      | m1_subset_1(sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 4.08/1.00      | v1_funct_1(k6_partfun1(u1_struct_0(sK3))) != iProver_top ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_7000,c_6865]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_9531,plain,
% 4.08/1.00      ( m1_subset_1(sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 4.08/1.00      | k9_tmap_1(sK3,sK3) = k6_partfun1(u1_struct_0(sK3)) ),
% 4.08/1.00      inference(global_propositional_subsumption,
% 4.08/1.00                [status(thm)],
% 4.08/1.00                [c_7005,c_50,c_63,c_66,c_5988,c_6353]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_9532,plain,
% 4.08/1.00      ( k9_tmap_1(sK3,sK3) = k6_partfun1(u1_struct_0(sK3))
% 4.08/1.00      | m1_subset_1(sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 4.08/1.00      inference(renaming,[status(thm)],[c_9531]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_9539,plain,
% 4.08/1.00      ( k9_tmap_1(sK3,sK3) = k6_partfun1(u1_struct_0(sK3))
% 4.08/1.00      | k7_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))) = k6_partfun1(u1_struct_0(sK3)) ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_9532,c_5028]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_9610,plain,
% 4.08/1.00      ( k9_tmap_1(sK3,sK3) = k6_partfun1(u1_struct_0(sK3))
% 4.08/1.00      | v1_funct_2(k6_partfun1(u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))) = iProver_top
% 4.08/1.00      | m1_subset_1(sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_9539,c_5021]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_10684,plain,
% 4.08/1.00      ( v1_funct_2(k6_partfun1(u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))) = iProver_top
% 4.08/1.00      | k9_tmap_1(sK3,sK3) = k6_partfun1(u1_struct_0(sK3)) ),
% 4.08/1.00      inference(global_propositional_subsumption,[status(thm)],[c_9610,c_9532]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_10685,plain,
% 4.08/1.00      ( k9_tmap_1(sK3,sK3) = k6_partfun1(u1_struct_0(sK3))
% 4.08/1.00      | v1_funct_2(k6_partfun1(u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))) = iProver_top ),
% 4.08/1.00      inference(renaming,[status(thm)],[c_10684]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_9609,plain,
% 4.08/1.00      ( k9_tmap_1(sK3,sK3) = k6_partfun1(u1_struct_0(sK3))
% 4.08/1.00      | m1_subset_1(sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 4.08/1.00      | m1_subset_1(k6_partfun1(u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))))) = iProver_top ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_9539,c_5027]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_11621,plain,
% 4.08/1.00      ( k9_tmap_1(sK3,sK3) = k6_partfun1(u1_struct_0(sK3))
% 4.08/1.00      | m1_subset_1(k6_partfun1(u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))))) = iProver_top ),
% 4.08/1.00      inference(global_propositional_subsumption,[status(thm)],[c_9609,c_9532]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_12834,plain,
% 4.08/1.00      ( k9_tmap_1(sK3,sK3) = k6_partfun1(u1_struct_0(sK3))
% 4.08/1.00      | v1_funct_2(k6_partfun1(u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))) != iProver_top
% 4.08/1.00      | v1_funct_1(k6_partfun1(u1_struct_0(sK3))) != iProver_top
% 4.08/1.00      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))) = iProver_top ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_11621,c_12823]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_12872,plain,
% 4.08/1.00      ( k9_tmap_1(sK3,sK3) = k6_partfun1(u1_struct_0(sK3))
% 4.08/1.00      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k6_partfun1(u1_struct_0(sK3)))))) = iProver_top ),
% 4.08/1.00      inference(global_propositional_subsumption,
% 4.08/1.00                [status(thm)],
% 4.08/1.00                [c_12842,c_5988,c_10685,c_12834]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_12879,plain,
% 4.08/1.00      ( k9_tmap_1(sK3,sK3) = k6_partfun1(u1_struct_0(sK3))
% 4.08/1.00      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3)))) = iProver_top ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_9052,c_12872]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_12882,plain,
% 4.08/1.00      ( k9_tmap_1(sK3,sK3) = k6_partfun1(u1_struct_0(sK3))
% 4.08/1.00      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 4.08/1.00      inference(light_normalisation,[status(thm)],[c_12879,c_4216,c_5728]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_13015,plain,
% 4.08/1.00      ( k9_tmap_1(sK3,sK3) = k6_partfun1(u1_struct_0(sK3)) ),
% 4.08/1.00      inference(global_propositional_subsumption,
% 4.08/1.00                [status(thm)],
% 4.08/1.00                [c_12882,c_48,c_50,c_162,c_165]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_22,plain,
% 4.08/1.00      ( ~ m1_pre_topc(X0,X1)
% 4.08/1.00      | m1_subset_1(k9_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X0)))))
% 4.08/1.00      | ~ v2_pre_topc(X1)
% 4.08/1.00      | v2_struct_0(X1)
% 4.08/1.00      | ~ l1_pre_topc(X1) ),
% 4.08/1.00      inference(cnf_transformation,[],[f90]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1940,plain,
% 4.08/1.00      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 4.08/1.00      | ~ v2_pre_topc(X0)
% 4.08/1.00      | v2_struct_0(X0)
% 4.08/1.00      | ~ l1_pre_topc(X0)
% 4.08/1.00      | sK4 != X1
% 4.08/1.00      | sK3 != X0 ),
% 4.08/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_286]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1941,plain,
% 4.08/1.00      ( m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 4.08/1.00      | ~ v2_pre_topc(sK3)
% 4.08/1.00      | v2_struct_0(sK3)
% 4.08/1.00      | ~ l1_pre_topc(sK3) ),
% 4.08/1.00      inference(unflattening,[status(thm)],[c_1940]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1943,plain,
% 4.08/1.00      ( m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) ),
% 4.08/1.00      inference(global_propositional_subsumption,
% 4.08/1.00                [status(thm)],
% 4.08/1.00                [c_1941,c_47,c_46,c_45]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_4230,plain,
% 4.08/1.00      ( m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) ),
% 4.08/1.00      inference(subtyping,[status(esa)],[c_1943]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_5005,plain,
% 4.08/1.00      ( m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) = iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_4230]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_5778,plain,
% 4.08/1.00      ( m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) = iProver_top ),
% 4.08/1.00      inference(demodulation,[status(thm)],[c_5721,c_5005]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_7130,plain,
% 4.08/1.00      ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK3,sK4)
% 4.08/1.00      | v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
% 4.08/1.00      | m1_subset_1(sK1(sK3,sK3,k9_tmap_1(sK3,sK4)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 4.08/1.00      | v1_funct_1(k9_tmap_1(sK3,sK4)) != iProver_top ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_5778,c_6865]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_49,plain,
% 4.08/1.00      ( v2_pre_topc(sK3) = iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_24,plain,
% 4.08/1.00      ( ~ m1_pre_topc(X0,X1)
% 4.08/1.00      | ~ v2_pre_topc(X1)
% 4.08/1.00      | v1_funct_1(k9_tmap_1(X1,X0))
% 4.08/1.00      | v2_struct_0(X1)
% 4.08/1.00      | ~ l1_pre_topc(X1) ),
% 4.08/1.00      inference(cnf_transformation,[],[f88]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1927,plain,
% 4.08/1.00      ( ~ v2_pre_topc(X0)
% 4.08/1.00      | v1_funct_1(k9_tmap_1(X0,X1))
% 4.08/1.00      | v2_struct_0(X0)
% 4.08/1.00      | ~ l1_pre_topc(X0)
% 4.08/1.00      | sK4 != X1
% 4.08/1.00      | sK3 != X0 ),
% 4.08/1.00      inference(resolution_lifted,[status(thm)],[c_24,c_286]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1928,plain,
% 4.08/1.00      ( ~ v2_pre_topc(sK3)
% 4.08/1.00      | v1_funct_1(k9_tmap_1(sK3,sK4))
% 4.08/1.00      | v2_struct_0(sK3)
% 4.08/1.00      | ~ l1_pre_topc(sK3) ),
% 4.08/1.00      inference(unflattening,[status(thm)],[c_1927]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1929,plain,
% 4.08/1.00      ( v2_pre_topc(sK3) != iProver_top
% 4.08/1.00      | v1_funct_1(k9_tmap_1(sK3,sK4)) = iProver_top
% 4.08/1.00      | v2_struct_0(sK3) = iProver_top
% 4.08/1.00      | l1_pre_topc(sK3) != iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_1928]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_23,plain,
% 4.08/1.00      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 4.08/1.00      | ~ m1_pre_topc(X1,X0)
% 4.08/1.00      | ~ v2_pre_topc(X0)
% 4.08/1.00      | v2_struct_0(X0)
% 4.08/1.00      | ~ l1_pre_topc(X0) ),
% 4.08/1.00      inference(cnf_transformation,[],[f89]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1585,plain,
% 4.08/1.00      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 4.08/1.00      | ~ v2_pre_topc(X0)
% 4.08/1.00      | v2_struct_0(X0)
% 4.08/1.00      | ~ l1_pre_topc(X0)
% 4.08/1.00      | sK4 != X1
% 4.08/1.00      | sK3 != X0 ),
% 4.08/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_286]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1586,plain,
% 4.08/1.00      ( v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 4.08/1.00      | ~ v2_pre_topc(sK3)
% 4.08/1.00      | v2_struct_0(sK3)
% 4.08/1.00      | ~ l1_pre_topc(sK3) ),
% 4.08/1.00      inference(unflattening,[status(thm)],[c_1585]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1588,plain,
% 4.08/1.00      ( v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) ),
% 4.08/1.00      inference(global_propositional_subsumption,
% 4.08/1.00                [status(thm)],
% 4.08/1.00                [c_1586,c_47,c_46,c_45]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_4234,plain,
% 4.08/1.00      ( v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) ),
% 4.08/1.00      inference(subtyping,[status(esa)],[c_1588]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_5002,plain,
% 4.08/1.00      ( v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) = iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_4234]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_5780,plain,
% 4.08/1.00      ( v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK3)) = iProver_top ),
% 4.08/1.00      inference(demodulation,[status(thm)],[c_5721,c_5002]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_11388,plain,
% 4.08/1.00      ( m1_subset_1(sK1(sK3,sK3,k9_tmap_1(sK3,sK4)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 4.08/1.00      | k9_tmap_1(sK3,sK3) = k9_tmap_1(sK3,sK4) ),
% 4.08/1.00      inference(global_propositional_subsumption,
% 4.08/1.00                [status(thm)],
% 4.08/1.00                [c_7130,c_48,c_49,c_50,c_1929,c_5780]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_11389,plain,
% 4.08/1.00      ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK3,sK4)
% 4.08/1.00      | m1_subset_1(sK1(sK3,sK3,k9_tmap_1(sK3,sK4)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 4.08/1.00      inference(renaming,[status(thm)],[c_11388]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_11395,plain,
% 4.08/1.00      ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK3,sK4)
% 4.08/1.00      | k7_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK3,sK4))) = k6_partfun1(u1_struct_0(sK3)) ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_11389,c_5028]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1930,plain,
% 4.08/1.00      ( v1_funct_1(k9_tmap_1(sK3,sK4)) ),
% 4.08/1.00      inference(global_propositional_subsumption,
% 4.08/1.00                [status(thm)],
% 4.08/1.00                [c_1928,c_47,c_46,c_45]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_11,plain,
% 4.08/1.00      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
% 4.08/1.00      | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 4.08/1.00      | ~ m1_pre_topc(X1,X0)
% 4.08/1.00      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 4.08/1.00      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
% 4.08/1.00      | ~ v2_pre_topc(X0)
% 4.08/1.00      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 4.08/1.00      | v2_struct_0(X0)
% 4.08/1.00      | ~ l1_pre_topc(X0) ),
% 4.08/1.00      inference(cnf_transformation,[],[f117]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_343,plain,
% 4.08/1.00      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
% 4.08/1.00      | ~ m1_pre_topc(X1,X0)
% 4.08/1.00      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 4.08/1.00      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
% 4.08/1.00      | ~ v2_pre_topc(X0)
% 4.08/1.00      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 4.08/1.00      | v2_struct_0(X0)
% 4.08/1.00      | ~ l1_pre_topc(X0) ),
% 4.08/1.00      inference(global_propositional_subsumption,[status(thm)],[c_11,c_23]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1551,plain,
% 4.08/1.00      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
% 4.08/1.00      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 4.08/1.00      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
% 4.08/1.00      | ~ v2_pre_topc(X0)
% 4.08/1.00      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 4.08/1.00      | v2_struct_0(X0)
% 4.08/1.00      | ~ l1_pre_topc(X0)
% 4.08/1.00      | sK4 != X1
% 4.08/1.00      | sK3 != X0 ),
% 4.08/1.00      inference(resolution_lifted,[status(thm)],[c_343,c_286]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1552,plain,
% 4.08/1.00      ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)))
% 4.08/1.00      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 4.08/1.00      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 4.08/1.00      | ~ v2_pre_topc(sK3)
% 4.08/1.00      | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
% 4.08/1.00      | v2_struct_0(sK3)
% 4.08/1.00      | ~ l1_pre_topc(sK3) ),
% 4.08/1.00      inference(unflattening,[status(thm)],[c_1551]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1554,plain,
% 4.08/1.00      ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 4.08/1.00      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 4.08/1.00      | r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)))
% 4.08/1.00      | ~ v1_funct_1(k9_tmap_1(sK3,sK4)) ),
% 4.08/1.00      inference(global_propositional_subsumption,
% 4.08/1.00                [status(thm)],
% 4.08/1.00                [c_1552,c_47,c_46,c_45]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1555,plain,
% 4.08/1.00      ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)))
% 4.08/1.00      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 4.08/1.00      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 4.08/1.00      | ~ v1_funct_1(k9_tmap_1(sK3,sK4)) ),
% 4.08/1.00      inference(renaming,[status(thm)],[c_1554]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1924,plain,
% 4.08/1.00      ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)))
% 4.08/1.00      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 4.08/1.00      | ~ v1_funct_1(k9_tmap_1(sK3,sK4)) ),
% 4.08/1.00      inference(backward_subsumption_resolution,[status(thm)],[c_1917,c_1555]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1937,plain,
% 4.08/1.00      ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)))
% 4.08/1.00      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) ),
% 4.08/1.00      inference(backward_subsumption_resolution,[status(thm)],[c_1930,c_1924]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1950,plain,
% 4.08/1.00      ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4))) ),
% 4.08/1.00      inference(backward_subsumption_resolution,[status(thm)],[c_1943,c_1937]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_4078,plain,
% 4.08/1.00      ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
% 4.08/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
% 4.08/1.00      | ~ v1_funct_1(X0)
% 4.08/1.00      | k9_tmap_1(sK3,sK4) != X0
% 4.08/1.00      | k9_tmap_1(sK3,sK3) = X0
% 4.08/1.00      | k7_tmap_1(sK3,sK1(sK3,sK3,X0)) != k7_tmap_1(sK3,u1_struct_0(sK4))
% 4.08/1.00      | u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,X0))) != u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))
% 4.08/1.00      | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(k8_tmap_1(sK3,sK4))
% 4.08/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 4.08/1.00      inference(resolution_lifted,[status(thm)],[c_1950,c_3385]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_4079,plain,
% 4.08/1.00      ( ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
% 4.08/1.00      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
% 4.08/1.00      | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
% 4.08/1.00      | k9_tmap_1(sK3,sK3) = k9_tmap_1(sK3,sK4)
% 4.08/1.00      | k7_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK3,sK4))) != k7_tmap_1(sK3,u1_struct_0(sK4))
% 4.08/1.00      | u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK3,sK4)))) != u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))
% 4.08/1.00      | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(k8_tmap_1(sK3,sK4)) ),
% 4.08/1.00      inference(unflattening,[status(thm)],[c_4078]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_4081,plain,
% 4.08/1.00      ( ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
% 4.08/1.00      | ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
% 4.08/1.00      | k9_tmap_1(sK3,sK3) = k9_tmap_1(sK3,sK4)
% 4.08/1.00      | k7_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK3,sK4))) != k7_tmap_1(sK3,u1_struct_0(sK4))
% 4.08/1.00      | u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK3,sK4)))) != u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))
% 4.08/1.00      | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(k8_tmap_1(sK3,sK4)) ),
% 4.08/1.00      inference(global_propositional_subsumption,
% 4.08/1.00                [status(thm)],
% 4.08/1.00                [c_4079,c_47,c_46,c_45,c_1928]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_4082,plain,
% 4.08/1.00      ( ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
% 4.08/1.00      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
% 4.08/1.00      | k9_tmap_1(sK3,sK3) = k9_tmap_1(sK3,sK4)
% 4.08/1.00      | k7_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK3,sK4))) != k7_tmap_1(sK3,u1_struct_0(sK4))
% 4.08/1.00      | u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK3,sK4)))) != u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))
% 4.08/1.00      | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(k8_tmap_1(sK3,sK4)) ),
% 4.08/1.00      inference(renaming,[status(thm)],[c_4081]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_4187,plain,
% 4.08/1.00      ( ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))
% 4.08/1.00      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3)))))
% 4.08/1.00      | k9_tmap_1(sK3,sK3) = k9_tmap_1(sK3,sK4)
% 4.08/1.00      | k7_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK3,sK4))) != k7_tmap_1(sK3,u1_struct_0(sK4))
% 4.08/1.00      | u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK3,sK4)))) != u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))
% 4.08/1.00      | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(k8_tmap_1(sK3,sK4)) ),
% 4.08/1.00      inference(subtyping,[status(esa)],[c_4082]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_5043,plain,
% 4.08/1.00      ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK3,sK4)
% 4.08/1.00      | k7_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK3,sK4))) != k7_tmap_1(sK3,u1_struct_0(sK4))
% 4.08/1.00      | u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK3,sK4)))) != u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))
% 4.08/1.00      | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(k8_tmap_1(sK3,sK4))
% 4.08/1.00      | v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))) != iProver_top
% 4.08/1.00      | m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))))) != iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_4187]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_5263,plain,
% 4.08/1.00      ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK3,sK4)
% 4.08/1.00      | k7_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK3,sK4))) != k7_tmap_1(sK3,u1_struct_0(sK4))
% 4.08/1.00      | u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK3,sK4)))) != u1_struct_0(k8_tmap_1(sK3,sK4))
% 4.08/1.00      | u1_struct_0(k8_tmap_1(sK3,sK3)) != u1_struct_0(k8_tmap_1(sK3,sK4))
% 4.08/1.00      | v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))) != iProver_top
% 4.08/1.00      | m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))))) != iProver_top ),
% 4.08/1.00      inference(light_normalisation,[status(thm)],[c_5043,c_4233]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_6622,plain,
% 4.08/1.00      ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK3,sK4)
% 4.08/1.00      | k7_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK3,sK4))) != k7_tmap_1(sK3,u1_struct_0(sK4))
% 4.08/1.00      | u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK3,sK4)))) != u1_struct_0(sK3)
% 4.08/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 4.08/1.00      | v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
% 4.08/1.00      | m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) != iProver_top ),
% 4.08/1.00      inference(light_normalisation,[status(thm)],[c_5263,c_5721,c_5728]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_6623,plain,
% 4.08/1.00      ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK3,sK4)
% 4.08/1.00      | k7_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK3,sK4))) != k7_tmap_1(sK3,u1_struct_0(sK4))
% 4.08/1.00      | u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK3,sK4)))) != u1_struct_0(sK3)
% 4.08/1.00      | v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
% 4.08/1.00      | m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) != iProver_top ),
% 4.08/1.00      inference(equality_resolution_simp,[status(thm)],[c_6622]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_6630,plain,
% 4.08/1.00      ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK3,sK4)
% 4.08/1.00      | k7_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK3,sK4))) != k7_tmap_1(sK3,u1_struct_0(sK4))
% 4.08/1.00      | u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK3,sK4)))) != u1_struct_0(sK3) ),
% 4.08/1.00      inference(global_propositional_subsumption,
% 4.08/1.00                [status(thm)],
% 4.08/1.00                [c_6623,c_5778,c_5780]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_6900,plain,
% 4.08/1.00      ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK3,sK4)
% 4.08/1.00      | k7_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK3,sK4))) != k6_partfun1(u1_struct_0(sK3))
% 4.08/1.00      | u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK3,sK4)))) != u1_struct_0(sK3) ),
% 4.08/1.00      inference(demodulation,[status(thm)],[c_5860,c_6630]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_11396,plain,
% 4.08/1.00      ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK3,sK4)
% 4.08/1.00      | u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK3,k9_tmap_1(sK3,sK4)))) = u1_struct_0(sK3) ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_11389,c_5024]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_11494,plain,
% 4.08/1.00      ( k9_tmap_1(sK3,sK3) = k9_tmap_1(sK3,sK4) ),
% 4.08/1.00      inference(global_propositional_subsumption,
% 4.08/1.00                [status(thm)],
% 4.08/1.00                [c_11395,c_6900,c_11396]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_27,plain,
% 4.08/1.00      ( ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
% 4.08/1.00      | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
% 4.08/1.00      | v3_pre_topc(X1,X0)
% 4.08/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 4.08/1.00      | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
% 4.08/1.00      | ~ v2_pre_topc(X0)
% 4.08/1.00      | ~ v1_funct_1(k7_tmap_1(X0,X1))
% 4.08/1.00      | v2_struct_0(X0)
% 4.08/1.00      | ~ l1_pre_topc(X0) ),
% 4.08/1.00      inference(cnf_transformation,[],[f97]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_315,plain,
% 4.08/1.00      ( ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
% 4.08/1.00      | v3_pre_topc(X1,X0)
% 4.08/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 4.08/1.00      | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
% 4.08/1.00      | ~ v2_pre_topc(X0)
% 4.08/1.00      | ~ v1_funct_1(k7_tmap_1(X0,X1))
% 4.08/1.00      | v2_struct_0(X0)
% 4.08/1.00      | ~ l1_pre_topc(X0) ),
% 4.08/1.00      inference(global_propositional_subsumption,[status(thm)],[c_27,c_17]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_39,negated_conjecture,
% 4.08/1.00      ( v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4))
% 4.08/1.00      | v1_tsep_1(sK4,sK3) ),
% 4.08/1.00      inference(cnf_transformation,[],[f109]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_617,plain,
% 4.08/1.00      ( v3_pre_topc(X0,X1)
% 4.08/1.00      | v1_tsep_1(sK4,sK3)
% 4.08/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.08/1.00      | ~ m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
% 4.08/1.00      | ~ v2_pre_topc(X1)
% 4.08/1.00      | ~ v1_funct_1(k7_tmap_1(X1,X0))
% 4.08/1.00      | v2_struct_0(X1)
% 4.08/1.00      | ~ l1_pre_topc(X1)
% 4.08/1.00      | k6_tmap_1(X1,X0) != k8_tmap_1(sK3,sK4)
% 4.08/1.00      | k7_tmap_1(X1,X0) != k9_tmap_1(sK3,sK4)
% 4.08/1.00      | sK3 != X1 ),
% 4.08/1.00      inference(resolution_lifted,[status(thm)],[c_315,c_39]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_618,plain,
% 4.08/1.00      ( v3_pre_topc(X0,sK3)
% 4.08/1.00      | v1_tsep_1(sK4,sK3)
% 4.08/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 4.08/1.00      | ~ m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))))
% 4.08/1.00      | ~ v2_pre_topc(sK3)
% 4.08/1.00      | ~ v1_funct_1(k7_tmap_1(sK3,X0))
% 4.08/1.00      | v2_struct_0(sK3)
% 4.08/1.00      | ~ l1_pre_topc(sK3)
% 4.08/1.00      | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
% 4.08/1.00      | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4) ),
% 4.08/1.00      inference(unflattening,[status(thm)],[c_617]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_622,plain,
% 4.08/1.00      ( ~ m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))))
% 4.08/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 4.08/1.00      | v1_tsep_1(sK4,sK3)
% 4.08/1.00      | v3_pre_topc(X0,sK3)
% 4.08/1.00      | ~ v1_funct_1(k7_tmap_1(sK3,X0))
% 4.08/1.00      | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
% 4.08/1.00      | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4) ),
% 4.08/1.00      inference(global_propositional_subsumption,
% 4.08/1.00                [status(thm)],
% 4.08/1.00                [c_618,c_47,c_46,c_45]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_623,plain,
% 4.08/1.00      ( v3_pre_topc(X0,sK3)
% 4.08/1.00      | v1_tsep_1(sK4,sK3)
% 4.08/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 4.08/1.00      | ~ m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))))
% 4.08/1.00      | ~ v1_funct_1(k7_tmap_1(sK3,X0))
% 4.08/1.00      | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
% 4.08/1.00      | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4) ),
% 4.08/1.00      inference(renaming,[status(thm)],[c_622]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_12,plain,
% 4.08/1.00      ( ~ v3_pre_topc(sK2(X0,X1),X0)
% 4.08/1.00      | v1_tsep_1(X1,X0)
% 4.08/1.00      | ~ m1_pre_topc(X1,X0)
% 4.08/1.00      | ~ l1_pre_topc(X0) ),
% 4.08/1.00      inference(cnf_transformation,[],[f81]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1596,plain,
% 4.08/1.00      ( ~ v3_pre_topc(sK2(X0,X1),X0)
% 4.08/1.00      | v1_tsep_1(X1,X0)
% 4.08/1.00      | ~ l1_pre_topc(X0)
% 4.08/1.00      | sK4 != X1
% 4.08/1.00      | sK3 != X0 ),
% 4.08/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_286]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1597,plain,
% 4.08/1.00      ( ~ v3_pre_topc(sK2(sK3,sK4),sK3)
% 4.08/1.00      | v1_tsep_1(sK4,sK3)
% 4.08/1.00      | ~ l1_pre_topc(sK3) ),
% 4.08/1.00      inference(unflattening,[status(thm)],[c_1596]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1599,plain,
% 4.08/1.00      ( v1_tsep_1(sK4,sK3) | ~ v3_pre_topc(sK2(sK3,sK4),sK3) ),
% 4.08/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1597,c_45]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1600,plain,
% 4.08/1.00      ( ~ v3_pre_topc(sK2(sK3,sK4),sK3) | v1_tsep_1(sK4,sK3) ),
% 4.08/1.00      inference(renaming,[status(thm)],[c_1599]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_2411,plain,
% 4.08/1.00      ( v1_tsep_1(sK4,sK3)
% 4.08/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 4.08/1.00      | ~ m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))))
% 4.08/1.00      | ~ v1_funct_1(k7_tmap_1(sK3,X0))
% 4.08/1.00      | sK2(sK3,sK4) != X0
% 4.08/1.00      | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
% 4.08/1.00      | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4)
% 4.08/1.00      | sK3 != sK3 ),
% 4.08/1.00      inference(resolution_lifted,[status(thm)],[c_623,c_1600]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_2412,plain,
% 4.08/1.00      ( v1_tsep_1(sK4,sK3)
% 4.08/1.00      | ~ m1_subset_1(sK2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 4.08/1.00      | ~ m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4))))))
% 4.08/1.00      | ~ v1_funct_1(k7_tmap_1(sK3,sK2(sK3,sK4)))
% 4.08/1.00      | k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4)
% 4.08/1.00      | k7_tmap_1(sK3,sK2(sK3,sK4)) != k9_tmap_1(sK3,sK4) ),
% 4.08/1.00      inference(unflattening,[status(thm)],[c_2411]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_14,plain,
% 4.08/1.00      ( v1_tsep_1(X0,X1)
% 4.08/1.00      | ~ m1_pre_topc(X0,X1)
% 4.08/1.00      | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 4.08/1.00      | ~ l1_pre_topc(X1) ),
% 4.08/1.00      inference(cnf_transformation,[],[f79]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1986,plain,
% 4.08/1.00      ( v1_tsep_1(X0,X1)
% 4.08/1.00      | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 4.08/1.00      | ~ l1_pre_topc(X1)
% 4.08/1.00      | sK4 != X0
% 4.08/1.00      | sK3 != X1 ),
% 4.08/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_286]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1987,plain,
% 4.08/1.00      ( v1_tsep_1(sK4,sK3)
% 4.08/1.00      | m1_subset_1(sK2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 4.08/1.00      | ~ l1_pre_topc(sK3) ),
% 4.08/1.00      inference(unflattening,[status(thm)],[c_1986]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_2414,plain,
% 4.08/1.00      ( v1_tsep_1(sK4,sK3)
% 4.08/1.00      | ~ m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4))))))
% 4.08/1.00      | ~ v1_funct_1(k7_tmap_1(sK3,sK2(sK3,sK4)))
% 4.08/1.00      | k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4)
% 4.08/1.00      | k7_tmap_1(sK3,sK2(sK3,sK4)) != k9_tmap_1(sK3,sK4) ),
% 4.08/1.00      inference(global_propositional_subsumption,
% 4.08/1.00                [status(thm)],
% 4.08/1.00                [c_2412,c_45,c_1987]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_4225,plain,
% 4.08/1.00      ( v1_tsep_1(sK4,sK3)
% 4.08/1.00      | ~ m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4))))))
% 4.08/1.00      | ~ v1_funct_1(k7_tmap_1(sK3,sK2(sK3,sK4)))
% 4.08/1.00      | k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4)
% 4.08/1.00      | k7_tmap_1(sK3,sK2(sK3,sK4)) != k9_tmap_1(sK3,sK4) ),
% 4.08/1.00      inference(subtyping,[status(esa)],[c_2414]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_5010,plain,
% 4.08/1.00      ( k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4)
% 4.08/1.00      | k7_tmap_1(sK3,sK2(sK3,sK4)) != k9_tmap_1(sK3,sK4)
% 4.08/1.00      | v1_tsep_1(sK4,sK3) = iProver_top
% 4.08/1.00      | m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4)))))) != iProver_top
% 4.08/1.00      | v1_funct_1(k7_tmap_1(sK3,sK2(sK3,sK4))) != iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_4225]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_4298,plain,
% 4.08/1.00      ( k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4)
% 4.08/1.00      | k7_tmap_1(sK3,sK2(sK3,sK4)) != k9_tmap_1(sK3,sK4)
% 4.08/1.00      | v1_tsep_1(sK4,sK3) = iProver_top
% 4.08/1.00      | m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4)))))) != iProver_top
% 4.08/1.00      | v1_funct_1(k7_tmap_1(sK3,sK2(sK3,sK4))) != iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_4225]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1989,plain,
% 4.08/1.00      ( m1_subset_1(sK2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 4.08/1.00      | v1_tsep_1(sK4,sK3) ),
% 4.08/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1987,c_45]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1990,plain,
% 4.08/1.00      ( v1_tsep_1(sK4,sK3)
% 4.08/1.00      | m1_subset_1(sK2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 4.08/1.00      inference(renaming,[status(thm)],[c_1989]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_4229,plain,
% 4.08/1.00      ( v1_tsep_1(sK4,sK3)
% 4.08/1.00      | m1_subset_1(sK2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 4.08/1.00      inference(subtyping,[status(esa)],[c_1990]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_5006,plain,
% 4.08/1.00      ( v1_tsep_1(sK4,sK3) = iProver_top
% 4.08/1.00      | m1_subset_1(sK2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_4229]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_6661,plain,
% 4.08/1.00      ( v1_tsep_1(sK4,sK3) = iProver_top
% 4.08/1.00      | v1_funct_1(k7_tmap_1(sK3,sK2(sK3,sK4))) = iProver_top ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_5006,c_5026]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_6922,plain,
% 4.08/1.00      ( m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4)))))) != iProver_top
% 4.08/1.00      | v1_tsep_1(sK4,sK3) = iProver_top
% 4.08/1.00      | k7_tmap_1(sK3,sK2(sK3,sK4)) != k9_tmap_1(sK3,sK4)
% 4.08/1.00      | k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4) ),
% 4.08/1.00      inference(global_propositional_subsumption,
% 4.08/1.00                [status(thm)],
% 4.08/1.00                [c_5010,c_4298,c_6661]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_6923,plain,
% 4.08/1.00      ( k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4)
% 4.08/1.00      | k7_tmap_1(sK3,sK2(sK3,sK4)) != k9_tmap_1(sK3,sK4)
% 4.08/1.00      | v1_tsep_1(sK4,sK3) = iProver_top
% 4.08/1.00      | m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4)))))) != iProver_top ),
% 4.08/1.00      inference(renaming,[status(thm)],[c_6922]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_11507,plain,
% 4.08/1.00      ( k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4)
% 4.08/1.00      | k7_tmap_1(sK3,sK2(sK3,sK4)) != k9_tmap_1(sK3,sK3)
% 4.08/1.00      | v1_tsep_1(sK4,sK3) = iProver_top
% 4.08/1.00      | m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4)))))) != iProver_top ),
% 4.08/1.00      inference(demodulation,[status(thm)],[c_11494,c_6923]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_13021,plain,
% 4.08/1.00      ( k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4)
% 4.08/1.00      | k7_tmap_1(sK3,sK2(sK3,sK4)) != k6_partfun1(u1_struct_0(sK3))
% 4.08/1.00      | v1_tsep_1(sK4,sK3) = iProver_top
% 4.08/1.00      | m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4)))))) != iProver_top ),
% 4.08/1.00      inference(demodulation,[status(thm)],[c_13015,c_11507]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_29,plain,
% 4.08/1.00      ( v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
% 4.08/1.00      | ~ v3_pre_topc(X1,X0)
% 4.08/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 4.08/1.00      | ~ v2_pre_topc(X0)
% 4.08/1.00      | v2_struct_0(X0)
% 4.08/1.00      | ~ l1_pre_topc(X0) ),
% 4.08/1.00      inference(cnf_transformation,[],[f95]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_35,negated_conjecture,
% 4.08/1.00      ( ~ v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4))
% 4.08/1.00      | ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 4.08/1.00      | ~ v1_tsep_1(sK4,sK3)
% 4.08/1.00      | ~ m1_pre_topc(sK4,sK3)
% 4.08/1.00      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 4.08/1.00      | ~ v1_funct_1(k9_tmap_1(sK3,sK4)) ),
% 4.08/1.00      inference(cnf_transformation,[],[f113]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_291,plain,
% 4.08/1.00      ( ~ v1_tsep_1(sK4,sK3)
% 4.08/1.00      | ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 4.08/1.00      | ~ v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4))
% 4.08/1.00      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 4.08/1.00      | ~ v1_funct_1(k9_tmap_1(sK3,sK4)) ),
% 4.08/1.00      inference(global_propositional_subsumption,[status(thm)],[c_35,c_44]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_292,negated_conjecture,
% 4.08/1.00      ( ~ v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4))
% 4.08/1.00      | ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 4.08/1.00      | ~ v1_tsep_1(sK4,sK3)
% 4.08/1.00      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 4.08/1.00      | ~ v1_funct_1(k9_tmap_1(sK3,sK4)) ),
% 4.08/1.00      inference(renaming,[status(thm)],[c_291]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_581,plain,
% 4.08/1.00      ( ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 4.08/1.00      | ~ v3_pre_topc(X0,X1)
% 4.08/1.00      | ~ v1_tsep_1(sK4,sK3)
% 4.08/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.08/1.00      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 4.08/1.00      | ~ v2_pre_topc(X1)
% 4.08/1.00      | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
% 4.08/1.00      | v2_struct_0(X1)
% 4.08/1.00      | ~ l1_pre_topc(X1)
% 4.08/1.00      | k6_tmap_1(X1,X0) != k8_tmap_1(sK3,sK4)
% 4.08/1.00      | k7_tmap_1(X1,X0) != k9_tmap_1(sK3,sK4)
% 4.08/1.00      | sK3 != X1 ),
% 4.08/1.00      inference(resolution_lifted,[status(thm)],[c_29,c_292]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_582,plain,
% 4.08/1.00      ( ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 4.08/1.00      | ~ v3_pre_topc(X0,sK3)
% 4.08/1.00      | ~ v1_tsep_1(sK4,sK3)
% 4.08/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 4.08/1.00      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 4.08/1.00      | ~ v2_pre_topc(sK3)
% 4.08/1.00      | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
% 4.08/1.00      | v2_struct_0(sK3)
% 4.08/1.00      | ~ l1_pre_topc(sK3)
% 4.08/1.00      | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
% 4.08/1.00      | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4) ),
% 4.08/1.00      inference(unflattening,[status(thm)],[c_581]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_586,plain,
% 4.08/1.00      ( ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 4.08/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 4.08/1.00      | ~ v1_tsep_1(sK4,sK3)
% 4.08/1.00      | ~ v3_pre_topc(X0,sK3)
% 4.08/1.00      | ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 4.08/1.00      | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
% 4.08/1.00      | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
% 4.08/1.00      | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4) ),
% 4.08/1.00      inference(global_propositional_subsumption,
% 4.08/1.00                [status(thm)],
% 4.08/1.00                [c_582,c_47,c_46,c_45]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_587,plain,
% 4.08/1.00      ( ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 4.08/1.00      | ~ v3_pre_topc(X0,sK3)
% 4.08/1.00      | ~ v1_tsep_1(sK4,sK3)
% 4.08/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 4.08/1.00      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 4.08/1.00      | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
% 4.08/1.00      | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
% 4.08/1.00      | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4) ),
% 4.08/1.00      inference(renaming,[status(thm)],[c_586]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_2245,plain,
% 4.08/1.00      ( ~ v3_pre_topc(X0,sK3)
% 4.08/1.00      | ~ v1_tsep_1(sK4,sK3)
% 4.08/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 4.08/1.00      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 4.08/1.00      | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
% 4.08/1.00      | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
% 4.08/1.00      | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4) ),
% 4.08/1.00      inference(backward_subsumption_resolution,[status(thm)],[c_1588,c_587]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_2338,plain,
% 4.08/1.00      ( ~ v3_pre_topc(X0,sK3)
% 4.08/1.00      | ~ v1_tsep_1(sK4,sK3)
% 4.08/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 4.08/1.00      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 4.08/1.00      | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
% 4.08/1.00      | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4) ),
% 4.08/1.00      inference(backward_subsumption_resolution,[status(thm)],[c_1930,c_2245]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_2344,plain,
% 4.08/1.00      ( ~ v3_pre_topc(X0,sK3)
% 4.08/1.00      | ~ v1_tsep_1(sK4,sK3)
% 4.08/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 4.08/1.00      | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
% 4.08/1.00      | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4) ),
% 4.08/1.00      inference(backward_subsumption_resolution,[status(thm)],[c_1943,c_2338]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_15,plain,
% 4.08/1.00      ( v3_pre_topc(u1_struct_0(X0),X1)
% 4.08/1.00      | ~ v1_tsep_1(X0,X1)
% 4.08/1.00      | ~ m1_pre_topc(X0,X1)
% 4.08/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 4.08/1.00      | ~ l1_pre_topc(X1) ),
% 4.08/1.00      inference(cnf_transformation,[],[f118]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_333,plain,
% 4.08/1.00      ( ~ m1_pre_topc(X0,X1)
% 4.08/1.00      | ~ v1_tsep_1(X0,X1)
% 4.08/1.00      | v3_pre_topc(u1_struct_0(X0),X1)
% 4.08/1.00      | ~ l1_pre_topc(X1) ),
% 4.08/1.00      inference(global_propositional_subsumption,[status(thm)],[c_15,c_33]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_334,plain,
% 4.08/1.00      ( v3_pre_topc(u1_struct_0(X0),X1)
% 4.08/1.00      | ~ v1_tsep_1(X0,X1)
% 4.08/1.00      | ~ m1_pre_topc(X0,X1)
% 4.08/1.00      | ~ l1_pre_topc(X1) ),
% 4.08/1.00      inference(renaming,[status(thm)],[c_333]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1900,plain,
% 4.08/1.00      ( v3_pre_topc(u1_struct_0(X0),X1)
% 4.08/1.00      | ~ v1_tsep_1(X0,X1)
% 4.08/1.00      | ~ l1_pre_topc(X1)
% 4.08/1.00      | sK4 != X0
% 4.08/1.00      | sK3 != X1 ),
% 4.08/1.00      inference(resolution_lifted,[status(thm)],[c_334,c_286]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1901,plain,
% 4.08/1.00      ( v3_pre_topc(u1_struct_0(sK4),sK3)
% 4.08/1.00      | ~ v1_tsep_1(sK4,sK3)
% 4.08/1.00      | ~ l1_pre_topc(sK3) ),
% 4.08/1.00      inference(unflattening,[status(thm)],[c_1900]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1903,plain,
% 4.08/1.00      ( ~ v1_tsep_1(sK4,sK3) | v3_pre_topc(u1_struct_0(sK4),sK3) ),
% 4.08/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1901,c_45]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1904,plain,
% 4.08/1.00      ( v3_pre_topc(u1_struct_0(sK4),sK3) | ~ v1_tsep_1(sK4,sK3) ),
% 4.08/1.00      inference(renaming,[status(thm)],[c_1903]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_2434,plain,
% 4.08/1.00      ( ~ v1_tsep_1(sK4,sK3)
% 4.08/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 4.08/1.00      | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
% 4.08/1.00      | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4)
% 4.08/1.00      | u1_struct_0(sK4) != X0
% 4.08/1.00      | sK3 != sK3 ),
% 4.08/1.00      inference(resolution_lifted,[status(thm)],[c_2344,c_1904]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_2435,plain,
% 4.08/1.00      ( ~ v1_tsep_1(sK4,sK3)
% 4.08/1.00      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 4.08/1.00      | k6_tmap_1(sK3,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4)
% 4.08/1.00      | k7_tmap_1(sK3,u1_struct_0(sK4)) != k9_tmap_1(sK3,sK4) ),
% 4.08/1.00      inference(unflattening,[status(thm)],[c_2434]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_2437,plain,
% 4.08/1.00      ( ~ v1_tsep_1(sK4,sK3)
% 4.08/1.00      | k7_tmap_1(sK3,u1_struct_0(sK4)) != k9_tmap_1(sK3,sK4) ),
% 4.08/1.00      inference(global_propositional_subsumption,
% 4.08/1.00                [status(thm)],
% 4.08/1.00                [c_2435,c_47,c_46,c_45,c_1893,c_1915]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_4224,plain,
% 4.08/1.00      ( ~ v1_tsep_1(sK4,sK3)
% 4.08/1.00      | k7_tmap_1(sK3,u1_struct_0(sK4)) != k9_tmap_1(sK3,sK4) ),
% 4.08/1.00      inference(subtyping,[status(esa)],[c_2437]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_5011,plain,
% 4.08/1.00      ( k7_tmap_1(sK3,u1_struct_0(sK4)) != k9_tmap_1(sK3,sK4)
% 4.08/1.00      | v1_tsep_1(sK4,sK3) != iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_4224]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_7261,plain,
% 4.08/1.00      ( k9_tmap_1(sK3,sK4) != k6_partfun1(u1_struct_0(sK3))
% 4.08/1.00      | v1_tsep_1(sK4,sK3) != iProver_top ),
% 4.08/1.00      inference(light_normalisation,[status(thm)],[c_5011,c_5860]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_11504,plain,
% 4.08/1.00      ( k9_tmap_1(sK3,sK3) != k6_partfun1(u1_struct_0(sK3))
% 4.08/1.00      | v1_tsep_1(sK4,sK3) != iProver_top ),
% 4.08/1.00      inference(demodulation,[status(thm)],[c_11494,c_7261]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_13022,plain,
% 4.08/1.00      ( k6_partfun1(u1_struct_0(sK3)) != k6_partfun1(u1_struct_0(sK3))
% 4.08/1.00      | v1_tsep_1(sK4,sK3) != iProver_top ),
% 4.08/1.00      inference(demodulation,[status(thm)],[c_13015,c_11504]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_13070,plain,
% 4.08/1.00      ( v1_tsep_1(sK4,sK3) != iProver_top ),
% 4.08/1.00      inference(equality_resolution_simp,[status(thm)],[c_13022]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_13077,plain,
% 4.08/1.00      ( k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4)
% 4.08/1.00      | k7_tmap_1(sK3,sK2(sK3,sK4)) != k6_partfun1(u1_struct_0(sK3))
% 4.08/1.00      | m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4)))))) != iProver_top ),
% 4.08/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_13021,c_13070]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_6659,plain,
% 4.08/1.00      ( k7_tmap_1(sK3,sK2(sK3,sK4)) = k6_partfun1(u1_struct_0(sK3))
% 4.08/1.00      | v1_tsep_1(sK4,sK3) = iProver_top ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_5006,c_5028]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_13863,plain,
% 4.08/1.00      ( k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4)
% 4.08/1.00      | m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4)))))) != iProver_top ),
% 4.08/1.00      inference(global_propositional_subsumption,
% 4.08/1.00                [status(thm)],
% 4.08/1.00                [c_13077,c_48,c_50,c_162,c_165,c_6659,c_11504,c_12882]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_13,plain,
% 4.08/1.00      ( v1_tsep_1(X0,X1)
% 4.08/1.00      | ~ m1_pre_topc(X0,X1)
% 4.08/1.00      | ~ l1_pre_topc(X1)
% 4.08/1.00      | sK2(X1,X0) = u1_struct_0(X0) ),
% 4.08/1.00      inference(cnf_transformation,[],[f80]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_2000,plain,
% 4.08/1.00      ( v1_tsep_1(X0,X1)
% 4.08/1.00      | ~ l1_pre_topc(X1)
% 4.08/1.00      | sK2(X1,X0) = u1_struct_0(X0)
% 4.08/1.00      | sK4 != X0
% 4.08/1.00      | sK3 != X1 ),
% 4.08/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_286]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_2001,plain,
% 4.08/1.00      ( v1_tsep_1(sK4,sK3)
% 4.08/1.00      | ~ l1_pre_topc(sK3)
% 4.08/1.00      | sK2(sK3,sK4) = u1_struct_0(sK4) ),
% 4.08/1.00      inference(unflattening,[status(thm)],[c_2000]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_2003,plain,
% 4.08/1.00      ( v1_tsep_1(sK4,sK3) | sK2(sK3,sK4) = u1_struct_0(sK4) ),
% 4.08/1.00      inference(global_propositional_subsumption,[status(thm)],[c_2001,c_45]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_4228,plain,
% 4.08/1.00      ( v1_tsep_1(sK4,sK3) | sK2(sK3,sK4) = u1_struct_0(sK4) ),
% 4.08/1.00      inference(subtyping,[status(esa)],[c_2003]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_5007,plain,
% 4.08/1.00      ( sK2(sK3,sK4) = u1_struct_0(sK4) | v1_tsep_1(sK4,sK3) = iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_4228]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_13565,plain,
% 4.08/1.00      ( sK2(sK3,sK4) = u1_struct_0(sK4) ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_5007,c_13070]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_13867,plain,
% 4.08/1.00      ( k8_tmap_1(sK3,sK4) != k8_tmap_1(sK3,sK4)
% 4.08/1.00      | m1_subset_1(k6_partfun1(u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) != iProver_top ),
% 4.08/1.00      inference(light_normalisation,
% 4.08/1.00                [status(thm)],
% 4.08/1.00                [c_13863,c_4233,c_5721,c_5860,c_13565]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_13868,plain,
% 4.08/1.00      ( m1_subset_1(k6_partfun1(u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) != iProver_top ),
% 4.08/1.00      inference(equality_resolution_simp,[status(thm)],[c_13867]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_13870,plain,
% 4.08/1.00      ( $false ),
% 4.08/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_13868,c_7000]) ).
% 4.08/1.00  
% 4.08/1.00  
% 4.08/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 4.08/1.00  
% 4.08/1.00  ------                               Statistics
% 4.08/1.00  
% 4.08/1.00  ------ General
% 4.08/1.00  
% 4.08/1.00  abstr_ref_over_cycles:                  0
% 4.08/1.00  abstr_ref_under_cycles:                 0
% 4.08/1.00  gc_basic_clause_elim:                   0
% 4.08/1.00  forced_gc_time:                         0
% 4.08/1.00  parsing_time:                           0.011
% 4.08/1.00  unif_index_cands_time:                  0.
% 4.08/1.00  unif_index_add_time:                    0.
% 4.08/1.00  orderings_time:                         0.
% 4.08/1.00  out_proof_time:                         0.024
% 4.08/1.00  total_time:                             0.499
% 4.08/1.00  num_of_symbols:                         68
% 4.08/1.00  num_of_terms:                           10660
% 4.08/1.00  
% 4.08/1.00  ------ Preprocessing
% 4.08/1.00  
% 4.08/1.00  num_of_splits:                          0
% 4.08/1.00  num_of_split_atoms:                     0
% 4.08/1.00  num_of_reused_defs:                     0
% 4.08/1.00  num_eq_ax_congr_red:                    16
% 4.08/1.00  num_of_sem_filtered_clauses:            6
% 4.08/1.00  num_of_subtypes:                        4
% 4.08/1.00  monotx_restored_types:                  0
% 4.08/1.00  sat_num_of_epr_types:                   0
% 4.08/1.00  sat_num_of_non_cyclic_types:            0
% 4.08/1.00  sat_guarded_non_collapsed_types:        1
% 4.08/1.00  num_pure_diseq_elim:                    0
% 4.08/1.00  simp_replaced_by:                       0
% 4.08/1.00  res_preprocessed:                       187
% 4.08/1.00  prep_upred:                             0
% 4.08/1.00  prep_unflattend:                        213
% 4.08/1.00  smt_new_axioms:                         0
% 4.08/1.00  pred_elim_cands:                        14
% 4.08/1.00  pred_elim:                              9
% 4.08/1.00  pred_elim_cl:                           -8
% 4.08/1.00  pred_elim_cycles:                       16
% 4.08/1.00  merged_defs:                            0
% 4.08/1.00  merged_defs_ncl:                        0
% 4.08/1.00  bin_hyper_res:                          0
% 4.08/1.00  prep_cycles:                            3
% 4.08/1.00  pred_elim_time:                         0.094
% 4.08/1.00  splitting_time:                         0.
% 4.08/1.00  sem_filter_time:                        0.
% 4.08/1.00  monotx_time:                            0.
% 4.08/1.00  subtype_inf_time:                       0.003
% 4.08/1.00  
% 4.08/1.00  ------ Problem properties
% 4.08/1.00  
% 4.08/1.00  clauses:                                49
% 4.08/1.00  conjectures:                            0
% 4.08/1.00  epr:                                    0
% 4.08/1.00  horn:                                   30
% 4.08/1.00  ground:                                 37
% 4.08/1.00  unary:                                  13
% 4.08/1.00  binary:                                 21
% 4.08/1.00  lits:                                   141
% 4.08/1.00  lits_eq:                                55
% 4.08/1.00  fd_pure:                                0
% 4.08/1.00  fd_pseudo:                              0
% 4.08/1.00  fd_cond:                                6
% 4.08/1.00  fd_pseudo_cond:                         0
% 4.08/1.00  ac_symbols:                             0
% 4.08/1.00  
% 4.08/1.00  ------ Propositional Solver
% 4.08/1.00  
% 4.08/1.00  prop_solver_calls:                      25
% 4.08/1.00  prop_fast_solver_calls:                 3046
% 4.08/1.00  smt_solver_calls:                       0
% 4.08/1.00  smt_fast_solver_calls:                  0
% 4.08/1.00  prop_num_of_clauses:                    3852
% 4.08/1.00  prop_preprocess_simplified:             10147
% 4.08/1.00  prop_fo_subsumed:                       253
% 4.08/1.00  prop_solver_time:                       0.
% 4.08/1.00  smt_solver_time:                        0.
% 4.08/1.00  smt_fast_solver_time:                   0.
% 4.08/1.00  prop_fast_solver_time:                  0.
% 4.08/1.00  prop_unsat_core_time:                   0.
% 4.08/1.00  
% 4.08/1.00  ------ QBF
% 4.08/1.00  
% 4.08/1.00  qbf_q_res:                              0
% 4.08/1.00  qbf_num_tautologies:                    0
% 4.08/1.00  qbf_prep_cycles:                        0
% 4.08/1.00  
% 4.08/1.00  ------ BMC1
% 4.08/1.00  
% 4.08/1.00  bmc1_current_bound:                     -1
% 4.08/1.00  bmc1_last_solved_bound:                 -1
% 4.08/1.00  bmc1_unsat_core_size:                   -1
% 4.08/1.00  bmc1_unsat_core_parents_size:           -1
% 4.08/1.00  bmc1_merge_next_fun:                    0
% 4.08/1.00  bmc1_unsat_core_clauses_time:           0.
% 4.08/1.00  
% 4.08/1.00  ------ Instantiation
% 4.08/1.00  
% 4.08/1.00  inst_num_of_clauses:                    1187
% 4.08/1.00  inst_num_in_passive:                    525
% 4.08/1.00  inst_num_in_active:                     655
% 4.08/1.00  inst_num_in_unprocessed:                7
% 4.08/1.00  inst_num_of_loops:                      760
% 4.08/1.00  inst_num_of_learning_restarts:          0
% 4.08/1.00  inst_num_moves_active_passive:          99
% 4.08/1.00  inst_lit_activity:                      0
% 4.08/1.00  inst_lit_activity_moves:                0
% 4.08/1.00  inst_num_tautologies:                   0
% 4.08/1.00  inst_num_prop_implied:                  0
% 4.08/1.00  inst_num_existing_simplified:           0
% 4.08/1.00  inst_num_eq_res_simplified:             0
% 4.08/1.00  inst_num_child_elim:                    0
% 4.08/1.00  inst_num_of_dismatching_blockings:      627
% 4.08/1.00  inst_num_of_non_proper_insts:           1274
% 4.08/1.00  inst_num_of_duplicates:                 0
% 4.08/1.00  inst_inst_num_from_inst_to_res:         0
% 4.08/1.00  inst_dismatching_checking_time:         0.
% 4.08/1.00  
% 4.08/1.00  ------ Resolution
% 4.08/1.00  
% 4.08/1.00  res_num_of_clauses:                     0
% 4.08/1.00  res_num_in_passive:                     0
% 4.08/1.00  res_num_in_active:                      0
% 4.08/1.00  res_num_of_loops:                       190
% 4.08/1.00  res_forward_subset_subsumed:            229
% 4.08/1.00  res_backward_subset_subsumed:           11
% 4.08/1.00  res_forward_subsumed:                   0
% 4.08/1.00  res_backward_subsumed:                  2
% 4.08/1.00  res_forward_subsumption_resolution:     16
% 4.08/1.00  res_backward_subsumption_resolution:    6
% 4.08/1.00  res_clause_to_clause_subsumption:       553
% 4.08/1.00  res_orphan_elimination:                 0
% 4.08/1.00  res_tautology_del:                      168
% 4.08/1.00  res_num_eq_res_simplified:              0
% 4.08/1.00  res_num_sel_changes:                    0
% 4.08/1.00  res_moves_from_active_to_pass:          0
% 4.08/1.00  
% 4.08/1.00  ------ Superposition
% 4.08/1.00  
% 4.08/1.00  sup_time_total:                         0.
% 4.08/1.00  sup_time_generating:                    0.
% 4.08/1.00  sup_time_sim_full:                      0.
% 4.08/1.00  sup_time_sim_immed:                     0.
% 4.08/1.00  
% 4.08/1.00  sup_num_of_clauses:                     101
% 4.08/1.00  sup_num_in_active:                      82
% 4.08/1.00  sup_num_in_passive:                     19
% 4.08/1.00  sup_num_of_loops:                       150
% 4.08/1.00  sup_fw_superposition:                   128
% 4.08/1.00  sup_bw_superposition:                   111
% 4.08/1.00  sup_immediate_simplified:               118
% 4.08/1.00  sup_given_eliminated:                   0
% 4.08/1.00  comparisons_done:                       0
% 4.08/1.00  comparisons_avoided:                    52
% 4.08/1.00  
% 4.08/1.00  ------ Simplifications
% 4.08/1.00  
% 4.08/1.00  
% 4.08/1.00  sim_fw_subset_subsumed:                 41
% 4.08/1.00  sim_bw_subset_subsumed:                 40
% 4.08/1.00  sim_fw_subsumed:                        20
% 4.08/1.00  sim_bw_subsumed:                        1
% 4.08/1.00  sim_fw_subsumption_res:                 5
% 4.08/1.00  sim_bw_subsumption_res:                 0
% 4.08/1.00  sim_tautology_del:                      2
% 4.08/1.00  sim_eq_tautology_del:                   21
% 4.08/1.00  sim_eq_res_simp:                        7
% 4.08/1.00  sim_fw_demodulated:                     5
% 4.08/1.00  sim_bw_demodulated:                     43
% 4.08/1.00  sim_light_normalised:                   89
% 4.08/1.00  sim_joinable_taut:                      0
% 4.08/1.00  sim_joinable_simp:                      0
% 4.08/1.00  sim_ac_normalised:                      0
% 4.08/1.00  sim_smt_subsumption:                    0
% 4.08/1.00  
%------------------------------------------------------------------------------
