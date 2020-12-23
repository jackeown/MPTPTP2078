%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:14 EST 2020

% Result     : Theorem 51.28s
% Output     : CNFRefutation 51.28s
% Verified   : 
% Statistics : Number of formulae       :  460 (170029 expanded)
%              Number of clauses        :  356 (41226 expanded)
%              Number of leaves         :   29 (38922 expanded)
%              Depth                    :   41
%              Number of atoms          : 2383 (1845620 expanded)
%              Number of equality atoms :  881 (58978 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f104,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f17,conjecture,(
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

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f63,plain,(
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
    inference(nnf_transformation,[],[f48])).

fof(f64,plain,(
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
    inference(flattening,[],[f63])).

fof(f66,plain,(
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

fof(f65,plain,
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

fof(f67,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f64,f66,f65])).

fof(f117,plain,
    ( m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f67])).

fof(f109,plain,(
    m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f67])).

fof(f108,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f67])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f106,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f67])).

fof(f107,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f67])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

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

fof(f90,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f95,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

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

fof(f27,plain,(
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

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f50,plain,(
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
    inference(rectify,[],[f49])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k6_tmap_1(X0,X3) != X2
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k6_tmap_1(X0,sK0(X0,X1,X2)) != X2
        & u1_struct_0(X1) = sK0(X0,X1,X2)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f50,f51])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k8_tmap_1(X0,X1) = X2
      | u1_struct_0(X1) = sK0(X0,X1,X2)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f96,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f87,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k8_tmap_1(X0,X1) = X2
      | k6_tmap_1(X0,sK0(X0,X1,X2)) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

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

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f54,plain,(
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
    inference(rectify,[],[f53])).

fof(f55,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2)))
        & u1_struct_0(X1) = sK1(X0,X1,X2)
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f54,f55])).

fof(f78,plain,(
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
    inference(cnf_transformation,[],[f56])).

fof(f88,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f89,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f97,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f68,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f2])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
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

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f71,plain,(
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
    inference(cnf_transformation,[],[f24])).

fof(f80,plain,(
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
    inference(cnf_transformation,[],[f56])).

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

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f93,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f91,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k9_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f14,axiom,(
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

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f61,plain,(
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
    inference(nnf_transformation,[],[f44])).

fof(f62,plain,(
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
    inference(flattening,[],[f61])).

fof(f101,plain,(
    ! [X0,X1] :
      ( v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f118,plain,
    ( ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4))
    | ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
    | ~ m1_pre_topc(sK4,sK3)
    | ~ v1_tsep_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f67])).

fof(f8,axiom,(
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

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f57,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f58,plain,(
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
    inference(rectify,[],[f57])).

fof(f59,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK2(X0,X1),X0)
        & u1_struct_0(X1) = sK2(X0,X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f58,f59])).

fof(f81,plain,(
    ! [X0,X3,X1] :
      ( v3_pre_topc(X3,X0)
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f123,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f81])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f105,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f73,plain,(
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
    inference(cnf_transformation,[],[f52])).

fof(f119,plain,(
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
    inference(equality_resolution,[],[f73])).

fof(f120,plain,(
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
    inference(equality_resolution,[],[f119])).

fof(f103,plain,(
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
    inference(cnf_transformation,[],[f62])).

fof(f114,plain,
    ( v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4))
    | v1_tsep_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f67])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(sK2(X0,X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k8_tmap_1(X0,X1) = X2
      | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | u1_struct_0(X1) = sK2(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_36,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_39,negated_conjecture,
    ( m1_pre_topc(sK4,sK3)
    | m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_47,negated_conjecture,
    ( m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_298,negated_conjecture,
    ( m1_pre_topc(sK4,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_39,c_47])).

cnf(c_1690,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK4 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_298])).

cnf(c_1691,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1690])).

cnf(c_48,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1693,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1691,c_48])).

cnf(c_3906,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subtyping,[status(esa)],[c_1693])).

cnf(c_4955,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3906])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_3930,plain,
    ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_57)))
    | ~ v2_pre_topc(X0_57)
    | v2_struct_0(X0_57)
    | ~ l1_pre_topc(X0_57)
    | k7_tmap_1(X0_57,X0_58) = k6_partfun1(u1_struct_0(X0_57)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_4931,plain,
    ( k7_tmap_1(X0_57,X0_58) = k6_partfun1(u1_struct_0(X0_57))
    | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_57))) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | l1_pre_topc(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3930])).

cnf(c_6410,plain,
    ( k7_tmap_1(sK3,u1_struct_0(sK4)) = k6_partfun1(u1_struct_0(sK3))
    | v2_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4955,c_4931])).

cnf(c_50,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_49,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_5701,plain,
    ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | k7_tmap_1(sK3,u1_struct_0(sK4)) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_3930])).

cnf(c_7517,plain,
    ( k7_tmap_1(sK3,u1_struct_0(sK4)) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6410,c_50,c_49,c_48,c_1691,c_5701])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_3926,plain,
    ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_57)))
    | m1_subset_1(k7_tmap_1(X0_57,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(k6_tmap_1(X0_57,X0_58)))))
    | ~ v2_pre_topc(X0_57)
    | v2_struct_0(X0_57)
    | ~ l1_pre_topc(X0_57) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_4935,plain,
    ( m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_57))) != iProver_top
    | m1_subset_1(k7_tmap_1(X0_57,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(k6_tmap_1(X0_57,X0_58))))) = iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | l1_pre_topc(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3926])).

cnf(c_7536,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))))) = iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7517,c_4935])).

cnf(c_51,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_52,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_53,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_1692,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1691])).

cnf(c_21416,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7536,c_51,c_52,c_53,c_1692])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_pre_topc(k6_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_3927,plain,
    ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_57)))
    | v1_pre_topc(k6_tmap_1(X0_57,X0_58))
    | ~ v2_pre_topc(X0_57)
    | v2_struct_0(X0_57)
    | ~ l1_pre_topc(X0_57) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_4934,plain,
    ( m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_57))) != iProver_top
    | v1_pre_topc(k6_tmap_1(X0_57,X0_58)) = iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | l1_pre_topc(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3927])).

cnf(c_5797,plain,
    ( v1_pre_topc(k6_tmap_1(sK3,u1_struct_0(sK4))) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4955,c_4934])).

cnf(c_5630,plain,
    ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_pre_topc(k6_tmap_1(sK3,u1_struct_0(sK4)))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_3927])).

cnf(c_5631,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v1_pre_topc(k6_tmap_1(sK3,u1_struct_0(sK4))) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5630])).

cnf(c_7393,plain,
    ( v1_pre_topc(k6_tmap_1(sK3,u1_struct_0(sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5797,c_51,c_52,c_53,c_1692,c_5631])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | sK0(X1,X0,X2) = u1_struct_0(X0)
    | k8_tmap_1(X1,X0) = X2 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1778,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | sK0(X1,X2,X0) = u1_struct_0(X2)
    | k8_tmap_1(X1,X2) = X0
    | sK4 != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_298])).

cnf(c_1779,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3)
    | sK0(sK3,sK4,X0) = u1_struct_0(sK4)
    | k8_tmap_1(sK3,sK4) = X0 ),
    inference(unflattening,[status(thm)],[c_1778])).

cnf(c_1783,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | sK0(sK3,sK4,X0) = u1_struct_0(sK4)
    | k8_tmap_1(sK3,sK4) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1779,c_50,c_49,c_48])).

cnf(c_1784,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK0(sK3,sK4,X0) = u1_struct_0(sK4)
    | k8_tmap_1(sK3,sK4) = X0 ),
    inference(renaming,[status(thm)],[c_1783])).

cnf(c_3900,plain,
    ( ~ v1_pre_topc(X0_57)
    | ~ v2_pre_topc(X0_57)
    | ~ l1_pre_topc(X0_57)
    | sK0(sK3,sK4,X0_57) = u1_struct_0(sK4)
    | k8_tmap_1(sK3,sK4) = X0_57 ),
    inference(subtyping,[status(esa)],[c_1784])).

cnf(c_4961,plain,
    ( sK0(sK3,sK4,X0_57) = u1_struct_0(sK4)
    | k8_tmap_1(sK3,sK4) = X0_57
    | v1_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3900])).

cnf(c_7398,plain,
    ( sK0(sK3,sK4,k6_tmap_1(sK3,u1_struct_0(sK4))) = u1_struct_0(sK4)
    | k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4)
    | v2_pre_topc(k6_tmap_1(sK3,u1_struct_0(sK4))) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK3,u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7393,c_4961])).

cnf(c_3933,plain,
    ( X0_57 = X0_57 ),
    theory(equality)).

cnf(c_3985,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_3933])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k6_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_3928,plain,
    ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_57)))
    | ~ v2_pre_topc(X0_57)
    | v2_pre_topc(k6_tmap_1(X0_57,X0_58))
    | v2_struct_0(X0_57)
    | ~ l1_pre_topc(X0_57) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_5677,plain,
    ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_pre_topc(k6_tmap_1(sK3,u1_struct_0(sK4)))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_3928])).

cnf(c_5678,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_pre_topc(k6_tmap_1(sK3,u1_struct_0(sK4))) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5677])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k6_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_3929,plain,
    ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_57)))
    | ~ v2_pre_topc(X0_57)
    | v2_struct_0(X0_57)
    | ~ l1_pre_topc(X0_57)
    | l1_pre_topc(k6_tmap_1(X0_57,X0_58)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_5685,plain,
    ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | l1_pre_topc(k6_tmap_1(sK3,u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_3929])).

cnf(c_5686,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(k6_tmap_1(sK3,u1_struct_0(sK4))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5685])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k6_tmap_1(X1,sK0(X1,X0,X2)) != X2
    | k8_tmap_1(X1,X0) = X2 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1805,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | k6_tmap_1(X1,sK0(X1,X2,X0)) != X0
    | k8_tmap_1(X1,X2) = X0
    | sK4 != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_298])).

cnf(c_1806,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3)
    | k6_tmap_1(sK3,sK0(sK3,sK4,X0)) != X0
    | k8_tmap_1(sK3,sK4) = X0 ),
    inference(unflattening,[status(thm)],[c_1805])).

cnf(c_1810,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | k6_tmap_1(sK3,sK0(sK3,sK4,X0)) != X0
    | k8_tmap_1(sK3,sK4) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1806,c_50,c_49,c_48])).

cnf(c_1811,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k6_tmap_1(sK3,sK0(sK3,sK4,X0)) != X0
    | k8_tmap_1(sK3,sK4) = X0 ),
    inference(renaming,[status(thm)],[c_1810])).

cnf(c_3899,plain,
    ( ~ v1_pre_topc(X0_57)
    | ~ v2_pre_topc(X0_57)
    | ~ l1_pre_topc(X0_57)
    | k6_tmap_1(sK3,sK0(sK3,sK4,X0_57)) != X0_57
    | k8_tmap_1(sK3,sK4) = X0_57 ),
    inference(subtyping,[status(esa)],[c_1811])).

cnf(c_5955,plain,
    ( ~ v1_pre_topc(k6_tmap_1(sK3,u1_struct_0(sK4)))
    | ~ v2_pre_topc(k6_tmap_1(sK3,u1_struct_0(sK4)))
    | ~ l1_pre_topc(k6_tmap_1(sK3,u1_struct_0(sK4)))
    | k6_tmap_1(sK3,sK0(sK3,sK4,k6_tmap_1(sK3,u1_struct_0(sK4)))) != k6_tmap_1(sK3,u1_struct_0(sK4))
    | k8_tmap_1(sK3,sK4) = k6_tmap_1(sK3,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3899])).

cnf(c_3937,plain,
    ( X0_57 != X1_57
    | X2_57 != X1_57
    | X2_57 = X0_57 ),
    theory(equality)).

cnf(c_5864,plain,
    ( k6_tmap_1(sK3,u1_struct_0(sK4)) != X0_57
    | k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4)
    | k8_tmap_1(sK3,sK4) != X0_57 ),
    inference(instantiation,[status(thm)],[c_3937])).

cnf(c_6485,plain,
    ( k6_tmap_1(sK3,u1_struct_0(sK4)) != k6_tmap_1(sK3,u1_struct_0(sK4))
    | k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4)
    | k8_tmap_1(sK3,sK4) != k6_tmap_1(sK3,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_5864])).

cnf(c_6486,plain,
    ( k6_tmap_1(sK3,u1_struct_0(sK4)) = k6_tmap_1(sK3,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3933])).

cnf(c_3955,plain,
    ( X0_58 != X1_58
    | X0_57 != X1_57
    | k6_tmap_1(X0_57,X0_58) = k6_tmap_1(X1_57,X1_58) ),
    theory(equality)).

cnf(c_6523,plain,
    ( X0_58 != u1_struct_0(sK4)
    | X0_57 != sK3
    | k6_tmap_1(X0_57,X0_58) = k6_tmap_1(sK3,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3955])).

cnf(c_8448,plain,
    ( sK0(sK3,sK4,k6_tmap_1(sK3,u1_struct_0(sK4))) != u1_struct_0(sK4)
    | X0_57 != sK3
    | k6_tmap_1(X0_57,sK0(sK3,sK4,k6_tmap_1(sK3,u1_struct_0(sK4)))) = k6_tmap_1(sK3,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_6523])).

cnf(c_8449,plain,
    ( sK0(sK3,sK4,k6_tmap_1(sK3,u1_struct_0(sK4))) != u1_struct_0(sK4)
    | k6_tmap_1(sK3,sK0(sK3,sK4,k6_tmap_1(sK3,u1_struct_0(sK4)))) = k6_tmap_1(sK3,u1_struct_0(sK4))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_8448])).

cnf(c_8631,plain,
    ( k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7398,c_50,c_51,c_49,c_52,c_48,c_53,c_1691,c_1692,c_3985,c_5630,c_5677,c_5678,c_5685,c_5686,c_5955,c_6485,c_6486,c_8449])).

cnf(c_21420,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_21416,c_8631])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k9_tmap_1(X1,X2) = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2060,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k9_tmap_1(X1,X2) = X0
    | sK4 != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_298])).

cnf(c_2061,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | m1_subset_1(sK1(sK3,sK4,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(X0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | k9_tmap_1(sK3,sK4) = X0 ),
    inference(unflattening,[status(thm)],[c_2060])).

cnf(c_2065,plain,
    ( m1_subset_1(sK1(sK3,sK4,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ v1_funct_1(X0)
    | k9_tmap_1(sK3,sK4) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2061,c_50,c_49,c_48])).

cnf(c_2066,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | m1_subset_1(sK1(sK3,sK4,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_funct_1(X0)
    | k9_tmap_1(sK3,sK4) = X0 ),
    inference(renaming,[status(thm)],[c_2065])).

cnf(c_3889,plain,
    ( ~ v1_funct_2(X0_58,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | m1_subset_1(sK1(sK3,sK4,X0_58),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_funct_1(X0_58)
    | k9_tmap_1(sK3,sK4) = X0_58 ),
    inference(subtyping,[status(esa)],[c_2066])).

cnf(c_4972,plain,
    ( k9_tmap_1(sK3,sK4) = X0_58
    | v1_funct_2(X0_58,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) != iProver_top
    | m1_subset_1(sK1(sK3,sK4,X0_58),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | v1_funct_1(X0_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3889])).

cnf(c_21423,plain,
    ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
    | v1_funct_2(k6_partfun1(u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
    | m1_subset_1(sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | v1_funct_1(k6_partfun1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_21420,c_4972])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k7_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_3924,plain,
    ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_57)))
    | ~ v2_pre_topc(X0_57)
    | v1_funct_1(k7_tmap_1(X0_57,X0_58))
    | v2_struct_0(X0_57)
    | ~ l1_pre_topc(X0_57) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_4937,plain,
    ( m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_57))) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | v1_funct_1(k7_tmap_1(X0_57,X0_58)) = iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | l1_pre_topc(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3924])).

cnf(c_5878,plain,
    ( v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4))) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4955,c_4937])).

cnf(c_5622,plain,
    ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4)))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_3924])).

cnf(c_5623,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4))) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5622])).

cnf(c_7511,plain,
    ( v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5878,c_51,c_52,c_53,c_1692,c_5623])).

cnf(c_7520,plain,
    ( v1_funct_1(k6_partfun1(u1_struct_0(sK3))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7517,c_7511])).

cnf(c_21,plain,
    ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_3925,plain,
    ( v1_funct_2(k7_tmap_1(X0_57,X0_58),u1_struct_0(X0_57),u1_struct_0(k6_tmap_1(X0_57,X0_58)))
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_57)))
    | ~ v2_pre_topc(X0_57)
    | v2_struct_0(X0_57)
    | ~ l1_pre_topc(X0_57) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_4936,plain,
    ( v1_funct_2(k7_tmap_1(X0_57,X0_58),u1_struct_0(X0_57),u1_struct_0(k6_tmap_1(X0_57,X0_58))) = iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_57))) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | l1_pre_topc(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3925])).

cnf(c_8657,plain,
    ( v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) = iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_8631,c_4936])).

cnf(c_8663,plain,
    ( v1_funct_2(k6_partfun1(u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) = iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8657,c_7517])).

cnf(c_29944,plain,
    ( m1_subset_1(sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21423,c_51,c_52,c_53,c_1692,c_7520,c_8663])).

cnf(c_29945,plain,
    ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
    | m1_subset_1(sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(renaming,[status(thm)],[c_29944])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_3921,plain,
    ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_57)))
    | ~ v2_pre_topc(X0_57)
    | v2_struct_0(X0_57)
    | ~ l1_pre_topc(X0_57)
    | u1_struct_0(k6_tmap_1(X0_57,X0_58)) = u1_struct_0(X0_57) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_4940,plain,
    ( u1_struct_0(k6_tmap_1(X0_57,X0_58)) = u1_struct_0(X0_57)
    | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_57))) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | l1_pre_topc(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3921])).

cnf(c_29957,plain,
    ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
    | u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))) = u1_struct_0(sK3)
    | v2_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_29945,c_4940])).

cnf(c_30067,plain,
    ( ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
    | u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))) = u1_struct_0(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_29957])).

cnf(c_33106,plain,
    ( u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))) = u1_struct_0(sK3)
    | k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_29957,c_50,c_49,c_48,c_30067])).

cnf(c_33107,plain,
    ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
    | u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))) = u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_33106])).

cnf(c_33134,plain,
    ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
    | u1_struct_0(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),X0_58)) = u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))))
    | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_pre_topc(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))) != iProver_top
    | v2_struct_0(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))) = iProver_top
    | l1_pre_topc(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_33107,c_4940])).

cnf(c_4933,plain,
    ( m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_57))) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(k6_tmap_1(X0_57,X0_58)) = iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | l1_pre_topc(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3928])).

cnf(c_29962,plain,
    ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
    | v2_pre_topc(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_29945,c_4933])).

cnf(c_31581,plain,
    ( v2_pre_topc(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))) = iProver_top
    | k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_29962,c_51,c_52,c_53])).

cnf(c_31582,plain,
    ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
    | v2_pre_topc(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))) = iProver_top ),
    inference(renaming,[status(thm)],[c_31581])).

cnf(c_4932,plain,
    ( m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_57))) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(k6_tmap_1(X0_57,X0_58)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3929])).

cnf(c_29963,plain,
    ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
    | v2_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_29945,c_4932])).

cnf(c_31686,plain,
    ( l1_pre_topc(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))) = iProver_top
    | k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_29963,c_51,c_52,c_53])).

cnf(c_31687,plain,
    ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
    | l1_pre_topc(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))) = iProver_top ),
    inference(renaming,[status(thm)],[c_31686])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(k6_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_3923,plain,
    ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_57)))
    | ~ v2_pre_topc(X0_57)
    | v2_struct_0(X0_57)
    | ~ v2_struct_0(k6_tmap_1(X0_57,X0_58))
    | ~ l1_pre_topc(X0_57) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_4938,plain,
    ( m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_57))) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(k6_tmap_1(X0_57,X0_58)) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3923])).

cnf(c_29958,plain,
    ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
    | v2_pre_topc(sK3) != iProver_top
    | v2_struct_0(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_29945,c_4938])).

cnf(c_33791,plain,
    ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
    | v2_struct_0(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_29958,c_51,c_52,c_53])).

cnf(c_103302,plain,
    ( m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | u1_struct_0(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),X0_58)) = u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))))
    | k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_33134,c_31582,c_31687,c_33791])).

cnf(c_103303,plain,
    ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
    | u1_struct_0(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),X0_58)) = u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))))
    | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_103302])).

cnf(c_103313,plain,
    ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
    | u1_struct_0(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),u1_struct_0(sK4))) = u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))) ),
    inference(superposition,[status(thm)],[c_4955,c_103303])).

cnf(c_104013,plain,
    ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
    | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))))) != iProver_top
    | v2_pre_topc(k6_tmap_1(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),u1_struct_0(sK4)),X0_58)) = iProver_top
    | v2_pre_topc(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),u1_struct_0(sK4))) != iProver_top
    | v2_struct_0(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),u1_struct_0(sK4))) = iProver_top
    | l1_pre_topc(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_103313,c_4933])).

cnf(c_104012,plain,
    ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
    | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))))) != iProver_top
    | v1_pre_topc(k6_tmap_1(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),u1_struct_0(sK4)),X0_58)) = iProver_top
    | v2_pre_topc(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),u1_struct_0(sK4))) != iProver_top
    | v2_struct_0(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),u1_struct_0(sK4))) = iProver_top
    | l1_pre_topc(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_103313,c_4934])).

cnf(c_33140,plain,
    ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
    | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_pre_topc(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))) != iProver_top
    | v2_struct_0(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))) = iProver_top
    | l1_pre_topc(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),X0_58)) = iProver_top
    | l1_pre_topc(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_33107,c_4932])).

cnf(c_89121,plain,
    ( l1_pre_topc(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),X0_58)) = iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_33140,c_51,c_52,c_53,c_29958,c_31582,c_31687])).

cnf(c_89122,plain,
    ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
    | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),X0_58)) = iProver_top ),
    inference(renaming,[status(thm)],[c_89121])).

cnf(c_104011,plain,
    ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
    | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))))) != iProver_top
    | v2_pre_topc(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),u1_struct_0(sK4))) != iProver_top
    | v1_funct_1(k7_tmap_1(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),u1_struct_0(sK4)),X0_58)) = iProver_top
    | v2_struct_0(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),u1_struct_0(sK4))) = iProver_top
    | l1_pre_topc(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_103313,c_4937])).

cnf(c_5749,plain,
    ( v2_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(k6_tmap_1(sK3,u1_struct_0(sK4))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4955,c_4932])).

cnf(c_7187,plain,
    ( l1_pre_topc(k6_tmap_1(sK3,u1_struct_0(sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5749,c_51,c_52,c_53,c_1692,c_5686])).

cnf(c_8638,plain,
    ( l1_pre_topc(k8_tmap_1(sK3,sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8631,c_7187])).

cnf(c_6561,plain,
    ( v2_pre_topc(sK3) != iProver_top
    | v2_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4955,c_4938])).

cnf(c_7077,plain,
    ( v2_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6561,c_51,c_52,c_53])).

cnf(c_8639,plain,
    ( v2_struct_0(k8_tmap_1(sK3,sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8631,c_7077])).

cnf(c_8656,plain,
    ( m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) = iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_8631,c_4935])).

cnf(c_8674,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) = iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8656,c_7517])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_580,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_0,c_1])).

cnf(c_3917,plain,
    ( v2_struct_0(X0_57)
    | ~ v1_xboole_0(u1_struct_0(X0_57))
    | ~ l1_pre_topc(X0_57) ),
    inference(subtyping,[status(esa)],[c_580])).

cnf(c_11053,plain,
    ( v2_struct_0(k8_tmap_1(sK3,sK4))
    | ~ v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ l1_pre_topc(k8_tmap_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_3917])).

cnf(c_11054,plain,
    ( v2_struct_0(k8_tmap_1(sK3,sK4)) = iProver_top
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
    | l1_pre_topc(k8_tmap_1(sK3,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11053])).

cnf(c_3,plain,
    ( r1_funct_2(X0,X1,X2,X3,X4,X4)
    | ~ v1_funct_2(X5,X2,X3)
    | ~ v1_funct_2(X4,X0,X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_3931,plain,
    ( r1_funct_2(X0_58,X1_58,X2_58,X3_58,X4_58,X4_58)
    | ~ v1_funct_2(X5_58,X2_58,X3_58)
    | ~ v1_funct_2(X4_58,X0_58,X1_58)
    | ~ m1_subset_1(X5_58,k1_zfmisc_1(k2_zfmisc_1(X2_58,X3_58)))
    | ~ m1_subset_1(X4_58,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58)))
    | ~ v1_funct_1(X5_58)
    | ~ v1_funct_1(X4_58)
    | v1_xboole_0(X1_58)
    | v1_xboole_0(X3_58) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_4930,plain,
    ( r1_funct_2(X0_58,X1_58,X2_58,X3_58,X4_58,X4_58) = iProver_top
    | v1_funct_2(X5_58,X2_58,X3_58) != iProver_top
    | v1_funct_2(X4_58,X0_58,X1_58) != iProver_top
    | m1_subset_1(X5_58,k1_zfmisc_1(k2_zfmisc_1(X2_58,X3_58))) != iProver_top
    | m1_subset_1(X4_58,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58))) != iProver_top
    | v1_funct_1(X5_58) != iProver_top
    | v1_funct_1(X4_58) != iProver_top
    | v1_xboole_0(X1_58) = iProver_top
    | v1_xboole_0(X3_58) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3931])).

cnf(c_7328,plain,
    ( r1_funct_2(X0_58,X1_58,u1_struct_0(X0_57),u1_struct_0(k6_tmap_1(X0_57,X2_58)),X3_58,X3_58) = iProver_top
    | v1_funct_2(X3_58,X0_58,X1_58) != iProver_top
    | v1_funct_2(k7_tmap_1(X0_57,X2_58),u1_struct_0(X0_57),u1_struct_0(k6_tmap_1(X0_57,X2_58))) != iProver_top
    | m1_subset_1(X3_58,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58))) != iProver_top
    | m1_subset_1(X2_58,k1_zfmisc_1(u1_struct_0(X0_57))) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | v1_funct_1(X3_58) != iProver_top
    | v1_funct_1(k7_tmap_1(X0_57,X2_58)) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v1_xboole_0(X1_58) = iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(X0_57,X2_58))) = iProver_top
    | l1_pre_topc(X0_57) != iProver_top ),
    inference(superposition,[status(thm)],[c_4935,c_4930])).

cnf(c_36697,plain,
    ( r1_funct_2(X0_58,X1_58,u1_struct_0(X0_57),u1_struct_0(k6_tmap_1(X0_57,X2_58)),X3_58,X3_58) = iProver_top
    | v1_funct_2(X3_58,X0_58,X1_58) != iProver_top
    | m1_subset_1(X3_58,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58))) != iProver_top
    | m1_subset_1(X2_58,k1_zfmisc_1(u1_struct_0(X0_57))) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | v1_funct_1(X3_58) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v1_xboole_0(X1_58) = iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(X0_57,X2_58))) = iProver_top
    | l1_pre_topc(X0_57) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7328,c_4937,c_4936])).

cnf(c_29959,plain,
    ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
    | k7_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))) = k6_partfun1(u1_struct_0(sK3))
    | v2_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_29945,c_4931])).

cnf(c_30069,plain,
    ( ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
    | k7_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_29959])).

cnf(c_33800,plain,
    ( k7_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))) = k6_partfun1(u1_struct_0(sK3))
    | k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_29959,c_50,c_49,c_48,c_30069])).

cnf(c_33801,plain,
    ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
    | k7_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_33800])).

cnf(c_9,plain,
    ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2)))
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k9_tmap_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1973,plain,
    ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2)))
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k9_tmap_1(X0,X1) = X2
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_298])).

cnf(c_1974,plain,
    ( ~ r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK4,X0))),X0,k7_tmap_1(sK3,sK1(sK3,sK4,X0)))
    | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(X0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | k9_tmap_1(sK3,sK4) = X0 ),
    inference(unflattening,[status(thm)],[c_1973])).

cnf(c_1978,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK4,X0))),X0,k7_tmap_1(sK3,sK1(sK3,sK4,X0)))
    | ~ v1_funct_1(X0)
    | k9_tmap_1(sK3,sK4) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1974,c_50,c_49,c_48])).

cnf(c_1979,plain,
    ( ~ r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK4,X0))),X0,k7_tmap_1(sK3,sK1(sK3,sK4,X0)))
    | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v1_funct_1(X0)
    | k9_tmap_1(sK3,sK4) = X0 ),
    inference(renaming,[status(thm)],[c_1978])).

cnf(c_3892,plain,
    ( ~ r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK4,X0_58))),X0_58,k7_tmap_1(sK3,sK1(sK3,sK4,X0_58)))
    | ~ v1_funct_2(X0_58,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v1_funct_1(X0_58)
    | k9_tmap_1(sK3,sK4) = X0_58 ),
    inference(subtyping,[status(esa)],[c_1979])).

cnf(c_4969,plain,
    ( k9_tmap_1(sK3,sK4) = X0_58
    | r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK4,X0_58))),X0_58,k7_tmap_1(sK3,sK1(sK3,sK4,X0_58))) != iProver_top
    | v1_funct_2(X0_58,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) != iProver_top
    | v1_funct_1(X0_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3892])).

cnf(c_33805,plain,
    ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
    | r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))),k6_partfun1(u1_struct_0(sK3)),k6_partfun1(u1_struct_0(sK3))) != iProver_top
    | v1_funct_2(k6_partfun1(u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
    | m1_subset_1(k6_partfun1(u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) != iProver_top
    | v1_funct_1(k6_partfun1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_33801,c_4969])).

cnf(c_34380,plain,
    ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))),k6_partfun1(u1_struct_0(sK3)),k6_partfun1(u1_struct_0(sK3))) != iProver_top
    | k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_33805,c_51,c_52,c_53,c_1692,c_7520,c_8663,c_8674])).

cnf(c_34381,plain,
    ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
    | r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))),k6_partfun1(u1_struct_0(sK3)),k6_partfun1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_34380])).

cnf(c_36712,plain,
    ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
    | v1_funct_2(k6_partfun1(u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
    | m1_subset_1(sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(k6_partfun1(u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(k6_partfun1(u1_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))))) = iProver_top
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_36697,c_34381])).

cnf(c_4944,plain,
    ( v2_struct_0(X0_57) = iProver_top
    | v1_xboole_0(u1_struct_0(X0_57)) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3917])).

cnf(c_104004,plain,
    ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
    | v2_struct_0(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),u1_struct_0(sK4))) = iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))))) != iProver_top
    | l1_pre_topc(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_103313,c_4944])).

cnf(c_161511,plain,
    ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
    | v2_struct_0(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),u1_struct_0(sK4))) = iProver_top
    | l1_pre_topc(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),u1_struct_0(sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_104011,c_51,c_52,c_53,c_1692,c_7520,c_8638,c_8639,c_8663,c_8674,c_11054,c_21423,c_36712,c_104004])).

cnf(c_161518,plain,
    ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_struct_0(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),u1_struct_0(sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_89122,c_161511])).

cnf(c_161536,plain,
    ( v2_struct_0(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),u1_struct_0(sK4))) = iProver_top
    | k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_104012,c_53,c_1692,c_161518])).

cnf(c_161537,plain,
    ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
    | v2_struct_0(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),u1_struct_0(sK4))) = iProver_top ),
    inference(renaming,[status(thm)],[c_161536])).

cnf(c_33135,plain,
    ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
    | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_pre_topc(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))) != iProver_top
    | v2_struct_0(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),X0_58)) != iProver_top
    | v2_struct_0(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))) = iProver_top
    | l1_pre_topc(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_33107,c_4938])).

cnf(c_93909,plain,
    ( m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
    | v2_struct_0(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),X0_58)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_33135,c_51,c_52,c_53,c_29958,c_29962,c_29963])).

cnf(c_93910,plain,
    ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
    | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_struct_0(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),X0_58)) != iProver_top ),
    inference(renaming,[status(thm)],[c_93909])).

cnf(c_161543,plain,
    ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_161537,c_93910])).

cnf(c_161657,plain,
    ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_104013,c_53,c_1692,c_161543])).

cnf(c_24,plain,
    ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1948,plain,
    ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_298])).

cnf(c_1949,plain,
    ( v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1948])).

cnf(c_1951,plain,
    ( v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1949,c_50,c_49,c_48])).

cnf(c_23,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(k9_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X0)))))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1712,plain,
    ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_298])).

cnf(c_1713,plain,
    ( m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1712])).

cnf(c_1715,plain,
    ( m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1713,c_50,c_49,c_48])).

cnf(c_25,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k9_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1701,plain,
    ( ~ v2_pre_topc(X0)
    | v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_298])).

cnf(c_1702,plain,
    ( ~ v2_pre_topc(sK3)
    | v1_funct_1(k9_tmap_1(sK3,sK4))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1701])).

cnf(c_1704,plain,
    ( v1_funct_1(k9_tmap_1(sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1702,c_50,c_49,c_48])).

cnf(c_33,plain,
    ( v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
    | ~ v3_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_38,negated_conjecture,
    ( ~ v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4))
    | ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ v1_tsep_1(sK4,sK3)
    | ~ m1_pre_topc(sK4,sK3)
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4)) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_303,plain,
    ( ~ v1_tsep_1(sK4,sK3)
    | ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_38,c_47])).

cnf(c_304,negated_conjecture,
    ( ~ v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4))
    | ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4)) ),
    inference(renaming,[status(thm)],[c_303])).

cnf(c_708,plain,
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
    inference(resolution_lifted,[status(thm)],[c_33,c_304])).

cnf(c_709,plain,
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
    inference(unflattening,[status(thm)],[c_708])).

cnf(c_713,plain,
    ( ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_tsep_1(sK4,sK3)
    | ~ v3_pre_topc(X0,sK3)
    | ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
    | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_709,c_50,c_49,c_48])).

cnf(c_714,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ v3_pre_topc(X0,sK3)
    | ~ v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
    | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4) ),
    inference(renaming,[status(thm)],[c_713])).

cnf(c_2186,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ v3_pre_topc(X0,sK3)
    | ~ v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1704,c_714])).

cnf(c_2192,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ v3_pre_topc(X0,sK3)
    | ~ v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1715,c_2186])).

cnf(c_2250,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1951,c_2192])).

cnf(c_16,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_347,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16,c_36])).

cnf(c_348,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_347])).

cnf(c_37,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1471,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | X2 != X1
    | X2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_348,c_37])).

cnf(c_1472,plain,
    ( v3_pre_topc(u1_struct_0(X0),X0)
    | ~ v1_tsep_1(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_1471])).

cnf(c_2334,plain,
    ( ~ v1_tsep_1(X0,X0)
    | ~ v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(X0)
    | k6_tmap_1(sK3,X1) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,X1) != k9_tmap_1(sK3,sK4)
    | u1_struct_0(X0) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2250,c_1472])).

cnf(c_2335,plain,
    ( ~ v1_tsep_1(sK4,sK3)
    | ~ v1_tsep_1(sK3,sK3)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | k6_tmap_1(sK3,u1_struct_0(sK3)) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,u1_struct_0(sK3)) != k9_tmap_1(sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_2334])).

cnf(c_65,plain,
    ( m1_pre_topc(sK3,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_68,plain,
    ( ~ m1_pre_topc(sK3,sK3)
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_853,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ v1_tsep_1(X0,X1)
    | ~ v1_tsep_1(sK4,sK3)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(sK3,X2) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,X2) != k9_tmap_1(sK3,sK4)
    | u1_struct_0(X0) != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_348,c_714])).

cnf(c_854,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ v1_tsep_1(X0,sK3)
    | ~ v1_tsep_1(sK4,sK3)
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
    | ~ l1_pre_topc(sK3)
    | k6_tmap_1(sK3,u1_struct_0(X0)) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,u1_struct_0(X0)) != k9_tmap_1(sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_853])).

cnf(c_856,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ v1_tsep_1(sK4,sK3)
    | ~ v1_tsep_1(sK3,sK3)
    | ~ m1_pre_topc(sK3,sK3)
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
    | ~ l1_pre_topc(sK3)
    | k6_tmap_1(sK3,u1_struct_0(sK3)) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,u1_struct_0(sK3)) != k9_tmap_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_854])).

cnf(c_2337,plain,
    ( ~ v1_tsep_1(sK4,sK3)
    | ~ v1_tsep_1(sK3,sK3)
    | k6_tmap_1(sK3,u1_struct_0(sK3)) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,u1_struct_0(sK3)) != k9_tmap_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2335,c_50,c_49,c_48,c_65,c_68,c_856,c_1702,c_1713,c_1949])).

cnf(c_3885,plain,
    ( ~ v1_tsep_1(sK4,sK3)
    | ~ v1_tsep_1(sK3,sK3)
    | k7_tmap_1(sK3,u1_struct_0(sK3)) != k9_tmap_1(sK3,sK4)
    | k6_tmap_1(sK3,u1_struct_0(sK3)) != k8_tmap_1(sK3,sK4) ),
    inference(subtyping,[status(esa)],[c_2337])).

cnf(c_4976,plain,
    ( k7_tmap_1(sK3,u1_struct_0(sK3)) != k9_tmap_1(sK3,sK4)
    | k6_tmap_1(sK3,u1_struct_0(sK3)) != k8_tmap_1(sK3,sK4)
    | v1_tsep_1(sK4,sK3) != iProver_top
    | v1_tsep_1(sK3,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3885])).

cnf(c_3919,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(subtyping,[status(esa)],[c_49])).

cnf(c_4942,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3919])).

cnf(c_1486,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | X2 != X1
    | X2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_37])).

cnf(c_1487,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_1486])).

cnf(c_3915,plain,
    ( m1_subset_1(u1_struct_0(X0_57),k1_zfmisc_1(u1_struct_0(X0_57)))
    | ~ l1_pre_topc(X0_57) ),
    inference(subtyping,[status(esa)],[c_1487])).

cnf(c_4946,plain,
    ( m1_subset_1(u1_struct_0(X0_57),k1_zfmisc_1(u1_struct_0(X0_57))) = iProver_top
    | l1_pre_topc(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3915])).

cnf(c_9045,plain,
    ( k7_tmap_1(X0_57,u1_struct_0(X0_57)) = k6_partfun1(u1_struct_0(X0_57))
    | v2_pre_topc(X0_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | l1_pre_topc(X0_57) != iProver_top ),
    inference(superposition,[status(thm)],[c_4946,c_4931])).

cnf(c_10816,plain,
    ( k7_tmap_1(sK3,u1_struct_0(sK3)) = k6_partfun1(u1_struct_0(sK3))
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4942,c_9045])).

cnf(c_5704,plain,
    ( ~ m1_subset_1(u1_struct_0(X0_57),k1_zfmisc_1(u1_struct_0(X0_57)))
    | ~ v2_pre_topc(X0_57)
    | v2_struct_0(X0_57)
    | ~ l1_pre_topc(X0_57)
    | k7_tmap_1(X0_57,u1_struct_0(X0_57)) = k6_partfun1(u1_struct_0(X0_57)) ),
    inference(instantiation,[status(thm)],[c_3930])).

cnf(c_5706,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | k7_tmap_1(sK3,u1_struct_0(sK3)) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_5704])).

cnf(c_10943,plain,
    ( k7_tmap_1(sK3,u1_struct_0(sK3)) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10816,c_50,c_49,c_48,c_65,c_68,c_5706])).

cnf(c_9047,plain,
    ( v1_pre_topc(k6_tmap_1(X0_57,u1_struct_0(X0_57))) = iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | l1_pre_topc(X0_57) != iProver_top ),
    inference(superposition,[status(thm)],[c_4946,c_4934])).

cnf(c_1594,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X2)
    | X2 != X1
    | X2 != X3
    | sK0(X1,X3,X0) = u1_struct_0(X3)
    | k8_tmap_1(X1,X3) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_37])).

cnf(c_1595,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | sK0(X1,X1,X0) = u1_struct_0(X1)
    | k8_tmap_1(X1,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_1594])).

cnf(c_3909,plain,
    ( ~ v1_pre_topc(X0_57)
    | ~ v2_pre_topc(X1_57)
    | ~ v2_pre_topc(X0_57)
    | v2_struct_0(X1_57)
    | ~ l1_pre_topc(X1_57)
    | ~ l1_pre_topc(X0_57)
    | sK0(X1_57,X1_57,X0_57) = u1_struct_0(X1_57)
    | k8_tmap_1(X1_57,X1_57) = X0_57 ),
    inference(subtyping,[status(esa)],[c_1595])).

cnf(c_4952,plain,
    ( sK0(X0_57,X0_57,X1_57) = u1_struct_0(X0_57)
    | k8_tmap_1(X0_57,X0_57) = X1_57
    | v1_pre_topc(X1_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(X1_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | l1_pre_topc(X1_57) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3909])).

cnf(c_18176,plain,
    ( sK0(sK3,sK3,X0_57) = u1_struct_0(sK3)
    | k8_tmap_1(sK3,sK3) = X0_57
    | v1_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4942,c_4952])).

cnf(c_18763,plain,
    ( l1_pre_topc(X0_57) != iProver_top
    | sK0(sK3,sK3,X0_57) = u1_struct_0(sK3)
    | k8_tmap_1(sK3,sK3) = X0_57
    | v1_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18176,c_51,c_53])).

cnf(c_18764,plain,
    ( sK0(sK3,sK3,X0_57) = u1_struct_0(sK3)
    | k8_tmap_1(sK3,sK3) = X0_57
    | v1_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top ),
    inference(renaming,[status(thm)],[c_18763])).

cnf(c_18774,plain,
    ( sK0(sK3,sK3,k6_tmap_1(X0_57,u1_struct_0(X0_57))) = u1_struct_0(sK3)
    | k6_tmap_1(X0_57,u1_struct_0(X0_57)) = k8_tmap_1(sK3,sK3)
    | v2_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(k6_tmap_1(X0_57,u1_struct_0(X0_57))) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(k6_tmap_1(X0_57,u1_struct_0(X0_57))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9047,c_18764])).

cnf(c_4029,plain,
    ( m1_subset_1(u1_struct_0(X0_57),k1_zfmisc_1(u1_struct_0(X0_57))) = iProver_top
    | l1_pre_topc(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3915])).

cnf(c_5680,plain,
    ( ~ m1_subset_1(u1_struct_0(X0_57),k1_zfmisc_1(u1_struct_0(X0_57)))
    | ~ v2_pre_topc(X0_57)
    | v2_pre_topc(k6_tmap_1(X0_57,u1_struct_0(X0_57)))
    | v2_struct_0(X0_57)
    | ~ l1_pre_topc(X0_57) ),
    inference(instantiation,[status(thm)],[c_3928])).

cnf(c_5681,plain,
    ( m1_subset_1(u1_struct_0(X0_57),k1_zfmisc_1(u1_struct_0(X0_57))) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(k6_tmap_1(X0_57,u1_struct_0(X0_57))) = iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | l1_pre_topc(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5680])).

cnf(c_5688,plain,
    ( ~ m1_subset_1(u1_struct_0(X0_57),k1_zfmisc_1(u1_struct_0(X0_57)))
    | ~ v2_pre_topc(X0_57)
    | v2_struct_0(X0_57)
    | ~ l1_pre_topc(X0_57)
    | l1_pre_topc(k6_tmap_1(X0_57,u1_struct_0(X0_57))) ),
    inference(instantiation,[status(thm)],[c_3929])).

cnf(c_5689,plain,
    ( m1_subset_1(u1_struct_0(X0_57),k1_zfmisc_1(u1_struct_0(X0_57))) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(k6_tmap_1(X0_57,u1_struct_0(X0_57))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5688])).

cnf(c_19248,plain,
    ( l1_pre_topc(X0_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | sK0(sK3,sK3,k6_tmap_1(X0_57,u1_struct_0(X0_57))) = u1_struct_0(sK3)
    | k6_tmap_1(X0_57,u1_struct_0(X0_57)) = k8_tmap_1(sK3,sK3)
    | v2_pre_topc(X0_57) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18774,c_4029,c_5681,c_5689])).

cnf(c_19249,plain,
    ( sK0(sK3,sK3,k6_tmap_1(X0_57,u1_struct_0(X0_57))) = u1_struct_0(sK3)
    | k6_tmap_1(X0_57,u1_struct_0(X0_57)) = k8_tmap_1(sK3,sK3)
    | v2_pre_topc(X0_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | l1_pre_topc(X0_57) != iProver_top ),
    inference(renaming,[status(thm)],[c_19248])).

cnf(c_19259,plain,
    ( sK0(sK3,sK3,k6_tmap_1(sK3,u1_struct_0(sK3))) = u1_struct_0(sK3)
    | k6_tmap_1(sK3,u1_struct_0(sK3)) = k8_tmap_1(sK3,sK3)
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4942,c_19249])).

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
    inference(cnf_transformation,[],[f120])).

cnf(c_367,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(k8_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(k8_tmap_1(X1,X0))
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8,c_36])).

cnf(c_1444,plain,
    ( ~ v1_pre_topc(k8_tmap_1(X0,X1))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(k8_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(k8_tmap_1(X0,X1))
    | X2 != X0
    | X2 != X1
    | k6_tmap_1(X0,u1_struct_0(X1)) = k8_tmap_1(X0,X1) ),
    inference(resolution_lifted,[status(thm)],[c_367,c_37])).

cnf(c_1445,plain,
    ( ~ v1_pre_topc(k8_tmap_1(X0,X0))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(k8_tmap_1(X0,X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(k8_tmap_1(X0,X0))
    | k6_tmap_1(X0,u1_struct_0(X0)) = k8_tmap_1(X0,X0) ),
    inference(unflattening,[status(thm)],[c_1444])).

cnf(c_3916,plain,
    ( ~ v1_pre_topc(k8_tmap_1(X0_57,X0_57))
    | ~ v2_pre_topc(X0_57)
    | ~ v2_pre_topc(k8_tmap_1(X0_57,X0_57))
    | v2_struct_0(X0_57)
    | ~ l1_pre_topc(X0_57)
    | ~ l1_pre_topc(k8_tmap_1(X0_57,X0_57))
    | k6_tmap_1(X0_57,u1_struct_0(X0_57)) = k8_tmap_1(X0_57,X0_57) ),
    inference(subtyping,[status(esa)],[c_1445])).

cnf(c_4027,plain,
    ( ~ v1_pre_topc(k8_tmap_1(sK3,sK3))
    | ~ v2_pre_topc(k8_tmap_1(sK3,sK3))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(k8_tmap_1(sK3,sK3))
    | ~ l1_pre_topc(sK3)
    | k6_tmap_1(sK3,u1_struct_0(sK3)) = k8_tmap_1(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_3916])).

cnf(c_5633,plain,
    ( ~ m1_subset_1(u1_struct_0(X0_57),k1_zfmisc_1(u1_struct_0(X0_57)))
    | v1_pre_topc(k6_tmap_1(X0_57,u1_struct_0(X0_57)))
    | ~ v2_pre_topc(X0_57)
    | v2_struct_0(X0_57)
    | ~ l1_pre_topc(X0_57) ),
    inference(instantiation,[status(thm)],[c_3927])).

cnf(c_5635,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_pre_topc(k6_tmap_1(sK3,u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_5633])).

cnf(c_5682,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_pre_topc(k6_tmap_1(sK3,u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_5680])).

cnf(c_5690,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | l1_pre_topc(k6_tmap_1(sK3,u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_5688])).

cnf(c_1624,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X2)
    | X2 != X1
    | X2 != X3
    | k6_tmap_1(X1,sK0(X1,X3,X0)) != X0
    | k8_tmap_1(X1,X3) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_37])).

cnf(c_1625,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(X1,sK0(X1,X1,X0)) != X0
    | k8_tmap_1(X1,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_1624])).

cnf(c_3908,plain,
    ( ~ v1_pre_topc(X0_57)
    | ~ v2_pre_topc(X1_57)
    | ~ v2_pre_topc(X0_57)
    | v2_struct_0(X1_57)
    | ~ l1_pre_topc(X1_57)
    | ~ l1_pre_topc(X0_57)
    | k6_tmap_1(X1_57,sK0(X1_57,X1_57,X0_57)) != X0_57
    | k8_tmap_1(X1_57,X1_57) = X0_57 ),
    inference(subtyping,[status(esa)],[c_1625])).

cnf(c_6282,plain,
    ( ~ v1_pre_topc(k6_tmap_1(X0_57,u1_struct_0(X0_57)))
    | ~ v2_pre_topc(X1_57)
    | ~ v2_pre_topc(k6_tmap_1(X0_57,u1_struct_0(X0_57)))
    | v2_struct_0(X1_57)
    | ~ l1_pre_topc(X1_57)
    | ~ l1_pre_topc(k6_tmap_1(X0_57,u1_struct_0(X0_57)))
    | k6_tmap_1(X1_57,sK0(X1_57,X1_57,k6_tmap_1(X0_57,u1_struct_0(X0_57)))) != k6_tmap_1(X0_57,u1_struct_0(X0_57))
    | k8_tmap_1(X1_57,X1_57) = k6_tmap_1(X0_57,u1_struct_0(X0_57)) ),
    inference(instantiation,[status(thm)],[c_3908])).

cnf(c_6304,plain,
    ( ~ v1_pre_topc(k6_tmap_1(sK3,u1_struct_0(sK3)))
    | ~ v2_pre_topc(k6_tmap_1(sK3,u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(k6_tmap_1(sK3,u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | k6_tmap_1(sK3,sK0(sK3,sK3,k6_tmap_1(sK3,u1_struct_0(sK3)))) != k6_tmap_1(sK3,u1_struct_0(sK3))
    | k8_tmap_1(sK3,sK3) = k6_tmap_1(sK3,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_6282])).

cnf(c_3952,plain,
    ( ~ v2_pre_topc(X0_57)
    | v2_pre_topc(X1_57)
    | X1_57 != X0_57 ),
    theory(equality)).

cnf(c_7381,plain,
    ( ~ v2_pre_topc(X0_57)
    | v2_pre_topc(k8_tmap_1(X1_57,X1_57))
    | k8_tmap_1(X1_57,X1_57) != X0_57 ),
    inference(instantiation,[status(thm)],[c_3952])).

cnf(c_9376,plain,
    ( ~ v2_pre_topc(k6_tmap_1(X0_57,u1_struct_0(X0_57)))
    | v2_pre_topc(k8_tmap_1(X1_57,X1_57))
    | k8_tmap_1(X1_57,X1_57) != k6_tmap_1(X0_57,u1_struct_0(X0_57)) ),
    inference(instantiation,[status(thm)],[c_7381])).

cnf(c_9378,plain,
    ( ~ v2_pre_topc(k6_tmap_1(sK3,u1_struct_0(sK3)))
    | v2_pre_topc(k8_tmap_1(sK3,sK3))
    | k8_tmap_1(sK3,sK3) != k6_tmap_1(sK3,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_9376])).

cnf(c_3956,plain,
    ( ~ v1_pre_topc(X0_57)
    | v1_pre_topc(X1_57)
    | X1_57 != X0_57 ),
    theory(equality)).

cnf(c_6281,plain,
    ( v1_pre_topc(X0_57)
    | ~ v1_pre_topc(k6_tmap_1(X1_57,u1_struct_0(X1_57)))
    | X0_57 != k6_tmap_1(X1_57,u1_struct_0(X1_57)) ),
    inference(instantiation,[status(thm)],[c_3956])).

cnf(c_9381,plain,
    ( ~ v1_pre_topc(k6_tmap_1(X0_57,u1_struct_0(X0_57)))
    | v1_pre_topc(k8_tmap_1(X1_57,X1_57))
    | k8_tmap_1(X1_57,X1_57) != k6_tmap_1(X0_57,u1_struct_0(X0_57)) ),
    inference(instantiation,[status(thm)],[c_6281])).

cnf(c_9383,plain,
    ( ~ v1_pre_topc(k6_tmap_1(sK3,u1_struct_0(sK3)))
    | v1_pre_topc(k8_tmap_1(sK3,sK3))
    | k8_tmap_1(sK3,sK3) != k6_tmap_1(sK3,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_9381])).

cnf(c_3940,plain,
    ( ~ l1_pre_topc(X0_57)
    | l1_pre_topc(X1_57)
    | X1_57 != X0_57 ),
    theory(equality)).

cnf(c_6700,plain,
    ( ~ l1_pre_topc(X0_57)
    | l1_pre_topc(k8_tmap_1(X1_57,X2_57))
    | k8_tmap_1(X1_57,X2_57) != X0_57 ),
    inference(instantiation,[status(thm)],[c_3940])).

cnf(c_9386,plain,
    ( ~ l1_pre_topc(k6_tmap_1(X0_57,u1_struct_0(X0_57)))
    | l1_pre_topc(k8_tmap_1(X1_57,X1_57))
    | k8_tmap_1(X1_57,X1_57) != k6_tmap_1(X0_57,u1_struct_0(X0_57)) ),
    inference(instantiation,[status(thm)],[c_6700])).

cnf(c_9388,plain,
    ( ~ l1_pre_topc(k6_tmap_1(sK3,u1_struct_0(sK3)))
    | l1_pre_topc(k8_tmap_1(sK3,sK3))
    | k8_tmap_1(sK3,sK3) != k6_tmap_1(sK3,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_9386])).

cnf(c_8322,plain,
    ( X0_58 != u1_struct_0(X0_57)
    | X1_57 != X0_57
    | k6_tmap_1(X1_57,X0_58) = k6_tmap_1(X0_57,u1_struct_0(X0_57)) ),
    inference(instantiation,[status(thm)],[c_3955])).

cnf(c_13152,plain,
    ( sK0(X0_57,X0_57,k6_tmap_1(X1_57,u1_struct_0(X1_57))) != u1_struct_0(X0_57)
    | X2_57 != X0_57
    | k6_tmap_1(X2_57,sK0(X0_57,X0_57,k6_tmap_1(X1_57,u1_struct_0(X1_57)))) = k6_tmap_1(X0_57,u1_struct_0(X0_57)) ),
    inference(instantiation,[status(thm)],[c_8322])).

cnf(c_13153,plain,
    ( sK0(sK3,sK3,k6_tmap_1(sK3,u1_struct_0(sK3))) != u1_struct_0(sK3)
    | k6_tmap_1(sK3,sK0(sK3,sK3,k6_tmap_1(sK3,u1_struct_0(sK3)))) = k6_tmap_1(sK3,u1_struct_0(sK3))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_13152])).

cnf(c_19361,plain,
    ( v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | sK0(sK3,sK3,k6_tmap_1(sK3,u1_struct_0(sK3))) = u1_struct_0(sK3)
    | k6_tmap_1(sK3,u1_struct_0(sK3)) = k8_tmap_1(sK3,sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_19259])).

cnf(c_19534,plain,
    ( k6_tmap_1(sK3,u1_struct_0(sK3)) = k8_tmap_1(sK3,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19259,c_50,c_49,c_48,c_65,c_68,c_3985,c_4027,c_5635,c_5682,c_5690,c_6304,c_9378,c_9383,c_9388,c_13153,c_19361])).

cnf(c_31030,plain,
    ( k9_tmap_1(sK3,sK4) != k6_partfun1(u1_struct_0(sK3))
    | k8_tmap_1(sK3,sK3) != k8_tmap_1(sK3,sK4)
    | v1_tsep_1(sK4,sK3) != iProver_top
    | v1_tsep_1(sK3,sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4976,c_10943,c_19534])).

cnf(c_1676,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK4 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_348,c_298])).

cnf(c_1677,plain,
    ( v3_pre_topc(u1_struct_0(sK4),sK3)
    | ~ v1_tsep_1(sK4,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1676])).

cnf(c_1679,plain,
    ( ~ v1_tsep_1(sK4,sK3)
    | v3_pre_topc(u1_struct_0(sK4),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1677,c_48])).

cnf(c_1680,plain,
    ( v3_pre_topc(u1_struct_0(sK4),sK3)
    | ~ v1_tsep_1(sK4,sK3) ),
    inference(renaming,[status(thm)],[c_1679])).

cnf(c_2317,plain,
    ( ~ v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4)
    | u1_struct_0(sK4) != X0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_2250,c_1680])).

cnf(c_2318,plain,
    ( ~ v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | k6_tmap_1(sK3,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,u1_struct_0(sK4)) != k9_tmap_1(sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_2317])).

cnf(c_2320,plain,
    ( ~ v1_tsep_1(sK4,sK3)
    | k6_tmap_1(sK3,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,u1_struct_0(sK4)) != k9_tmap_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2318,c_48,c_1691])).

cnf(c_3886,plain,
    ( ~ v1_tsep_1(sK4,sK3)
    | k7_tmap_1(sK3,u1_struct_0(sK4)) != k9_tmap_1(sK3,sK4)
    | k6_tmap_1(sK3,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4) ),
    inference(subtyping,[status(esa)],[c_2320])).

cnf(c_4975,plain,
    ( k7_tmap_1(sK3,u1_struct_0(sK4)) != k9_tmap_1(sK3,sK4)
    | k6_tmap_1(sK3,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4)
    | v1_tsep_1(sK4,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3886])).

cnf(c_7521,plain,
    ( k9_tmap_1(sK3,sK4) != k6_partfun1(u1_struct_0(sK3))
    | k6_tmap_1(sK3,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4)
    | v1_tsep_1(sK4,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7517,c_4975])).

cnf(c_31036,plain,
    ( v1_tsep_1(sK4,sK3) != iProver_top
    | k9_tmap_1(sK3,sK4) != k6_partfun1(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_31030,c_50,c_51,c_49,c_52,c_48,c_53,c_1691,c_1692,c_3985,c_5630,c_5677,c_5678,c_5685,c_5686,c_5955,c_6485,c_6486,c_7398,c_7521,c_8449])).

cnf(c_31037,plain,
    ( k9_tmap_1(sK3,sK4) != k6_partfun1(u1_struct_0(sK3))
    | v1_tsep_1(sK4,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_31036])).

cnf(c_161674,plain,
    ( k6_partfun1(u1_struct_0(sK3)) != k6_partfun1(u1_struct_0(sK3))
    | v1_tsep_1(sK4,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_161657,c_31037])).

cnf(c_161698,plain,
    ( v1_tsep_1(sK4,sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_161674])).

cnf(c_31,plain,
    ( ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
    | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | v3_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k7_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_326,plain,
    ( ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
    | v3_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k7_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_31,c_21])).

cnf(c_42,negated_conjecture,
    ( v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4))
    | v1_tsep_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_744,plain,
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
    inference(resolution_lifted,[status(thm)],[c_326,c_42])).

cnf(c_745,plain,
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
    inference(unflattening,[status(thm)],[c_744])).

cnf(c_749,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_tsep_1(sK4,sK3)
    | v3_pre_topc(X0,sK3)
    | ~ v1_funct_1(k7_tmap_1(sK3,X0))
    | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_745,c_50,c_49,c_48])).

cnf(c_750,plain,
    ( v3_pre_topc(X0,sK3)
    | v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))))
    | ~ v1_funct_1(k7_tmap_1(sK3,X0))
    | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4) ),
    inference(renaming,[status(thm)],[c_749])).

cnf(c_13,plain,
    ( ~ v3_pre_topc(sK2(X0,X1),X0)
    | v1_tsep_1(X1,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1959,plain,
    ( ~ v3_pre_topc(sK2(X0,X1),X0)
    | v1_tsep_1(X1,X0)
    | ~ l1_pre_topc(X0)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_298])).

cnf(c_1960,plain,
    ( ~ v3_pre_topc(sK2(sK3,sK4),sK3)
    | v1_tsep_1(sK4,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1959])).

cnf(c_1962,plain,
    ( v1_tsep_1(sK4,sK3)
    | ~ v3_pre_topc(sK2(sK3,sK4),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1960,c_48])).

cnf(c_1963,plain,
    ( ~ v3_pre_topc(sK2(sK3,sK4),sK3)
    | v1_tsep_1(sK4,sK3) ),
    inference(renaming,[status(thm)],[c_1962])).

cnf(c_2294,plain,
    ( v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))))
    | ~ v1_funct_1(k7_tmap_1(sK3,X0))
    | sK2(sK3,sK4) != X0
    | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4)
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_750,c_1963])).

cnf(c_2295,plain,
    ( v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(sK2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4))))))
    | ~ v1_funct_1(k7_tmap_1(sK3,sK2(sK3,sK4)))
    | k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,sK2(sK3,sK4)) != k9_tmap_1(sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_2294])).

cnf(c_15,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1723,plain,
    ( v1_tsep_1(X0,X1)
    | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK4 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_298])).

cnf(c_1724,plain,
    ( v1_tsep_1(sK4,sK3)
    | m1_subset_1(sK2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1723])).

cnf(c_2297,plain,
    ( v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4))))))
    | ~ v1_funct_1(k7_tmap_1(sK3,sK2(sK3,sK4)))
    | k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,sK2(sK3,sK4)) != k9_tmap_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2295,c_48,c_1724])).

cnf(c_3887,plain,
    ( v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4))))))
    | ~ v1_funct_1(k7_tmap_1(sK3,sK2(sK3,sK4)))
    | k7_tmap_1(sK3,sK2(sK3,sK4)) != k9_tmap_1(sK3,sK4)
    | k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4) ),
    inference(subtyping,[status(esa)],[c_2297])).

cnf(c_4974,plain,
    ( k7_tmap_1(sK3,sK2(sK3,sK4)) != k9_tmap_1(sK3,sK4)
    | k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4)
    | v1_tsep_1(sK4,sK3) = iProver_top
    | m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4)))))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK3,sK2(sK3,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3887])).

cnf(c_4085,plain,
    ( k7_tmap_1(sK3,sK2(sK3,sK4)) != k9_tmap_1(sK3,sK4)
    | k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4)
    | v1_tsep_1(sK4,sK3) = iProver_top
    | m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4)))))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK3,sK2(sK3,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3887])).

cnf(c_1726,plain,
    ( m1_subset_1(sK2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_tsep_1(sK4,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1724,c_48])).

cnf(c_1727,plain,
    ( v1_tsep_1(sK4,sK3)
    | m1_subset_1(sK2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(renaming,[status(thm)],[c_1726])).

cnf(c_3903,plain,
    ( v1_tsep_1(sK4,sK3)
    | m1_subset_1(sK2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subtyping,[status(esa)],[c_1727])).

cnf(c_4958,plain,
    ( v1_tsep_1(sK4,sK3) = iProver_top
    | m1_subset_1(sK2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3903])).

cnf(c_6194,plain,
    ( v1_tsep_1(sK4,sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(k7_tmap_1(sK3,sK2(sK3,sK4))) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4958,c_4937])).

cnf(c_7178,plain,
    ( m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4)))))) != iProver_top
    | v1_tsep_1(sK4,sK3) = iProver_top
    | k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,sK2(sK3,sK4)) != k9_tmap_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4974,c_51,c_52,c_53,c_4085,c_6194])).

cnf(c_7179,plain,
    ( k7_tmap_1(sK3,sK2(sK3,sK4)) != k9_tmap_1(sK3,sK4)
    | k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4)
    | v1_tsep_1(sK4,sK3) = iProver_top
    | m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4)))))) != iProver_top ),
    inference(renaming,[status(thm)],[c_7178])).

cnf(c_161676,plain,
    ( k7_tmap_1(sK3,sK2(sK3,sK4)) != k6_partfun1(u1_struct_0(sK3))
    | k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4)
    | v1_tsep_1(sK4,sK3) = iProver_top
    | m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4)))))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_161657,c_7179])).

cnf(c_161701,plain,
    ( k7_tmap_1(sK3,sK2(sK3,sK4)) != k6_partfun1(u1_struct_0(sK3))
    | k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4)
    | m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4)))))) != iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_161698,c_161676])).

cnf(c_117690,plain,
    ( ~ m1_subset_1(sK2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4))))))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_3926])).

cnf(c_117712,plain,
    ( m1_subset_1(sK2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4)))))) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_117690])).

cnf(c_6195,plain,
    ( v1_tsep_1(sK4,sK3) = iProver_top
    | v1_pre_topc(k6_tmap_1(sK3,sK2(sK3,sK4))) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4958,c_4934])).

cnf(c_8117,plain,
    ( v1_pre_topc(k6_tmap_1(sK3,sK2(sK3,sK4))) = iProver_top
    | v1_tsep_1(sK4,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6195,c_51,c_52,c_53])).

cnf(c_8118,plain,
    ( v1_tsep_1(sK4,sK3) = iProver_top
    | v1_pre_topc(k6_tmap_1(sK3,sK2(sK3,sK4))) = iProver_top ),
    inference(renaming,[status(thm)],[c_8117])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(sK0(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k8_tmap_1(X1,X0) = X2 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1751,plain,
    ( m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_pre_topc(X2)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X2)
    | k8_tmap_1(X0,X1) = X2
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_298])).

cnf(c_1752,plain,
    ( m1_subset_1(sK0(sK3,sK4,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3)
    | k8_tmap_1(sK3,sK4) = X0 ),
    inference(unflattening,[status(thm)],[c_1751])).

cnf(c_1756,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | m1_subset_1(sK0(sK3,sK4,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | k8_tmap_1(sK3,sK4) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1752,c_50,c_49,c_48])).

cnf(c_1757,plain,
    ( m1_subset_1(sK0(sK3,sK4,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k8_tmap_1(sK3,sK4) = X0 ),
    inference(renaming,[status(thm)],[c_1756])).

cnf(c_3901,plain,
    ( m1_subset_1(sK0(sK3,sK4,X0_57),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_pre_topc(X0_57)
    | ~ v2_pre_topc(X0_57)
    | ~ l1_pre_topc(X0_57)
    | k8_tmap_1(sK3,sK4) = X0_57 ),
    inference(subtyping,[status(esa)],[c_1757])).

cnf(c_4960,plain,
    ( k8_tmap_1(sK3,sK4) = X0_57
    | m1_subset_1(sK0(sK3,sK4,X0_57),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | v1_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3901])).

cnf(c_6411,plain,
    ( k7_tmap_1(sK3,sK0(sK3,sK4,X0_57)) = k6_partfun1(u1_struct_0(sK3))
    | k8_tmap_1(sK3,sK4) = X0_57
    | v1_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4960,c_4931])).

cnf(c_9433,plain,
    ( l1_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | v1_pre_topc(X0_57) != iProver_top
    | k8_tmap_1(sK3,sK4) = X0_57
    | k7_tmap_1(sK3,sK0(sK3,sK4,X0_57)) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6411,c_51,c_52,c_53])).

cnf(c_9434,plain,
    ( k7_tmap_1(sK3,sK0(sK3,sK4,X0_57)) = k6_partfun1(u1_struct_0(sK3))
    | k8_tmap_1(sK3,sK4) = X0_57
    | v1_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top ),
    inference(renaming,[status(thm)],[c_9433])).

cnf(c_9445,plain,
    ( k7_tmap_1(sK3,sK0(sK3,sK4,k6_tmap_1(sK3,sK2(sK3,sK4)))) = k6_partfun1(u1_struct_0(sK3))
    | k6_tmap_1(sK3,sK2(sK3,sK4)) = k8_tmap_1(sK3,sK4)
    | v1_tsep_1(sK4,sK3) = iProver_top
    | v2_pre_topc(k6_tmap_1(sK3,sK2(sK3,sK4))) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK3,sK2(sK3,sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8118,c_9434])).

cnf(c_6196,plain,
    ( v1_tsep_1(sK4,sK3) = iProver_top
    | v2_pre_topc(k6_tmap_1(sK3,sK2(sK3,sK4))) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4958,c_4933])).

cnf(c_6197,plain,
    ( v1_tsep_1(sK4,sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(k6_tmap_1(sK3,sK2(sK3,sK4))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4958,c_4932])).

cnf(c_5866,plain,
    ( k6_tmap_1(sK3,sK2(sK3,sK4)) != X0_57
    | k6_tmap_1(sK3,sK2(sK3,sK4)) = k8_tmap_1(sK3,sK4)
    | k8_tmap_1(sK3,sK4) != X0_57 ),
    inference(instantiation,[status(thm)],[c_3937])).

cnf(c_6492,plain,
    ( k6_tmap_1(sK3,sK2(sK3,sK4)) != k6_tmap_1(sK3,sK2(sK3,sK4))
    | k6_tmap_1(sK3,sK2(sK3,sK4)) = k8_tmap_1(sK3,sK4)
    | k8_tmap_1(sK3,sK4) != k6_tmap_1(sK3,sK2(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_5866])).

cnf(c_6493,plain,
    ( k6_tmap_1(sK3,sK2(sK3,sK4)) = k6_tmap_1(sK3,sK2(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_3933])).

cnf(c_7364,plain,
    ( X0_57 != X1_57
    | X1_57 = X0_57 ),
    inference(resolution,[status(thm)],[c_3937,c_3933])).

cnf(c_10897,plain,
    ( X0_58 != X1_58
    | X0_57 != X1_57
    | k6_tmap_1(X1_57,X1_58) = k6_tmap_1(X0_57,X0_58) ),
    inference(resolution,[status(thm)],[c_7364,c_3955])).

cnf(c_50348,plain,
    ( ~ v1_pre_topc(k6_tmap_1(X0_57,X0_58))
    | ~ v2_pre_topc(k6_tmap_1(X0_57,X0_58))
    | ~ l1_pre_topc(k6_tmap_1(X0_57,X0_58))
    | X0_58 != sK0(sK3,sK4,k6_tmap_1(X0_57,X0_58))
    | X0_57 != sK3
    | k8_tmap_1(sK3,sK4) = k6_tmap_1(X0_57,X0_58) ),
    inference(resolution,[status(thm)],[c_10897,c_3899])).

cnf(c_3938,plain,
    ( X0_58 != X1_58
    | X2_58 != X1_58
    | X2_58 = X0_58 ),
    theory(equality)).

cnf(c_14,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK2(X1,X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1737,plain,
    ( v1_tsep_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK2(X1,X0) = u1_struct_0(X0)
    | sK4 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_298])).

cnf(c_1738,plain,
    ( v1_tsep_1(sK4,sK3)
    | ~ l1_pre_topc(sK3)
    | sK2(sK3,sK4) = u1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1737])).

cnf(c_1740,plain,
    ( v1_tsep_1(sK4,sK3)
    | sK2(sK3,sK4) = u1_struct_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1738,c_48])).

cnf(c_3902,plain,
    ( v1_tsep_1(sK4,sK3)
    | sK2(sK3,sK4) = u1_struct_0(sK4) ),
    inference(subtyping,[status(esa)],[c_1740])).

cnf(c_7406,plain,
    ( v1_tsep_1(sK4,sK3)
    | X0_58 != u1_struct_0(sK4)
    | sK2(sK3,sK4) = X0_58 ),
    inference(resolution,[status(thm)],[c_3938,c_3902])).

cnf(c_7568,plain,
    ( v1_tsep_1(sK4,sK3)
    | X0_58 != X1_58
    | X1_58 != u1_struct_0(sK4)
    | sK2(sK3,sK4) = X0_58 ),
    inference(resolution,[status(thm)],[c_7406,c_3938])).

cnf(c_3941,plain,
    ( u1_struct_0(X0_57) = u1_struct_0(X1_57)
    | X0_57 != X1_57 ),
    theory(equality)).

cnf(c_7948,plain,
    ( v1_tsep_1(sK4,sK3)
    | X0_58 != u1_struct_0(X0_57)
    | sK2(sK3,sK4) = X0_58
    | X0_57 != sK4 ),
    inference(resolution,[status(thm)],[c_7568,c_3941])).

cnf(c_13039,plain,
    ( v1_tsep_1(sK4,sK3)
    | ~ v1_pre_topc(X0_57)
    | ~ v2_pre_topc(X0_57)
    | ~ l1_pre_topc(X0_57)
    | sK2(sK3,sK4) = sK0(sK3,sK4,X0_57)
    | k8_tmap_1(sK3,sK4) = X0_57
    | sK4 != sK4 ),
    inference(resolution,[status(thm)],[c_3900,c_7948])).

cnf(c_13044,plain,
    ( v1_tsep_1(sK4,sK3)
    | ~ v1_pre_topc(X0_57)
    | ~ v2_pre_topc(X0_57)
    | ~ l1_pre_topc(X0_57)
    | sK2(sK3,sK4) = sK0(sK3,sK4,X0_57)
    | k8_tmap_1(sK3,sK4) = X0_57 ),
    inference(equality_resolution_simp,[status(thm)],[c_13039])).

cnf(c_51238,plain,
    ( v1_tsep_1(sK4,sK3)
    | ~ v1_pre_topc(k6_tmap_1(X0_57,sK2(sK3,sK4)))
    | ~ v2_pre_topc(k6_tmap_1(X0_57,sK2(sK3,sK4)))
    | ~ l1_pre_topc(k6_tmap_1(X0_57,sK2(sK3,sK4)))
    | X0_57 != sK3
    | k8_tmap_1(sK3,sK4) = k6_tmap_1(X0_57,sK2(sK3,sK4)) ),
    inference(resolution,[status(thm)],[c_50348,c_13044])).

cnf(c_51239,plain,
    ( X0_57 != sK3
    | k8_tmap_1(sK3,sK4) = k6_tmap_1(X0_57,sK2(sK3,sK4))
    | v1_tsep_1(sK4,sK3) = iProver_top
    | v1_pre_topc(k6_tmap_1(X0_57,sK2(sK3,sK4))) != iProver_top
    | v2_pre_topc(k6_tmap_1(X0_57,sK2(sK3,sK4))) != iProver_top
    | l1_pre_topc(k6_tmap_1(X0_57,sK2(sK3,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51238])).

cnf(c_51241,plain,
    ( k8_tmap_1(sK3,sK4) = k6_tmap_1(sK3,sK2(sK3,sK4))
    | sK3 != sK3
    | v1_tsep_1(sK4,sK3) = iProver_top
    | v1_pre_topc(k6_tmap_1(sK3,sK2(sK3,sK4))) != iProver_top
    | v2_pre_topc(k6_tmap_1(sK3,sK2(sK3,sK4))) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK3,sK2(sK3,sK4))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_51239])).

cnf(c_106317,plain,
    ( k6_tmap_1(sK3,sK2(sK3,sK4)) = k8_tmap_1(sK3,sK4)
    | v1_tsep_1(sK4,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9445,c_51,c_52,c_53,c_3985,c_6195,c_6196,c_6197,c_6492,c_6493,c_51241])).

cnf(c_6409,plain,
    ( k7_tmap_1(sK3,sK2(sK3,sK4)) = k6_partfun1(u1_struct_0(sK3))
    | v1_tsep_1(sK4,sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4958,c_4931])).

cnf(c_8366,plain,
    ( v1_tsep_1(sK4,sK3) = iProver_top
    | k7_tmap_1(sK3,sK2(sK3,sK4)) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6409,c_51,c_52,c_53])).

cnf(c_8367,plain,
    ( k7_tmap_1(sK3,sK2(sK3,sK4)) = k6_partfun1(u1_struct_0(sK3))
    | v1_tsep_1(sK4,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_8366])).

cnf(c_1725,plain,
    ( v1_tsep_1(sK4,sK3) = iProver_top
    | m1_subset_1(sK2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1724])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_161701,c_161543,c_117712,c_106317,c_31037,c_8367,c_1725,c_1692,c_53,c_52,c_51])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:38:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 51.28/7.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 51.28/7.00  
% 51.28/7.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 51.28/7.00  
% 51.28/7.00  ------  iProver source info
% 51.28/7.00  
% 51.28/7.00  git: date: 2020-06-30 10:37:57 +0100
% 51.28/7.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 51.28/7.00  git: non_committed_changes: false
% 51.28/7.00  git: last_make_outside_of_git: false
% 51.28/7.00  
% 51.28/7.00  ------ 
% 51.28/7.00  ------ Parsing...
% 51.28/7.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 51.28/7.00  
% 51.28/7.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 51.28/7.00  
% 51.28/7.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 51.28/7.00  
% 51.28/7.00  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 51.28/7.00  ------ Proving...
% 51.28/7.00  ------ Problem Properties 
% 51.28/7.00  
% 51.28/7.00  
% 51.28/7.00  clauses                                 50
% 51.28/7.00  conjectures                             3
% 51.28/7.00  EPR                                     3
% 51.28/7.00  Horn                                    20
% 51.28/7.00  unary                                   8
% 51.28/7.00  binary                                  4
% 51.28/7.00  lits                                    213
% 51.28/7.00  lits eq                                 35
% 51.28/7.00  fd_pure                                 0
% 51.28/7.00  fd_pseudo                               0
% 51.28/7.00  fd_cond                                 6
% 51.28/7.00  fd_pseudo_cond                          6
% 51.28/7.00  AC symbols                              0
% 51.28/7.00  
% 51.28/7.00  ------ Input Options Time Limit: Unbounded
% 51.28/7.00  
% 51.28/7.00  
% 51.28/7.00  ------ 
% 51.28/7.00  Current options:
% 51.28/7.00  ------ 
% 51.28/7.00  
% 51.28/7.00  
% 51.28/7.00  
% 51.28/7.00  
% 51.28/7.00  ------ Proving...
% 51.28/7.00  
% 51.28/7.00  
% 51.28/7.00  % SZS status Theorem for theBenchmark.p
% 51.28/7.00  
% 51.28/7.00  % SZS output start CNFRefutation for theBenchmark.p
% 51.28/7.00  
% 51.28/7.00  fof(f15,axiom,(
% 51.28/7.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 51.28/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.28/7.00  
% 51.28/7.00  fof(f45,plain,(
% 51.28/7.00    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 51.28/7.00    inference(ennf_transformation,[],[f15])).
% 51.28/7.00  
% 51.28/7.00  fof(f104,plain,(
% 51.28/7.00    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 51.28/7.00    inference(cnf_transformation,[],[f45])).
% 51.28/7.00  
% 51.28/7.00  fof(f17,conjecture,(
% 51.28/7.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))))))),
% 51.28/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.28/7.00  
% 51.28/7.00  fof(f18,negated_conjecture,(
% 51.28/7.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))))))),
% 51.28/7.00    inference(negated_conjecture,[],[f17])).
% 51.28/7.00  
% 51.28/7.00  fof(f47,plain,(
% 51.28/7.00    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1)))) & m1_pre_topc(X1,X0)) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 51.28/7.00    inference(ennf_transformation,[],[f18])).
% 51.28/7.00  
% 51.28/7.00  fof(f48,plain,(
% 51.28/7.00    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 51.28/7.00    inference(flattening,[],[f47])).
% 51.28/7.00  
% 51.28/7.00  fof(f63,plain,(
% 51.28/7.00    ? [X0] : (? [X1] : ((((~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) & ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 51.28/7.00    inference(nnf_transformation,[],[f48])).
% 51.28/7.00  
% 51.28/7.00  fof(f64,plain,(
% 51.28/7.00    ? [X0] : (? [X1] : ((~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 51.28/7.00    inference(flattening,[],[f63])).
% 51.28/7.00  
% 51.28/7.00  fof(f66,plain,(
% 51.28/7.00    ( ! [X0] : (? [X1] : ((~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0)) => ((~m1_subset_1(k9_tmap_1(X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,sK4))))) | ~v5_pre_topc(k9_tmap_1(X0,sK4),X0,k8_tmap_1(X0,sK4)) | ~v1_funct_2(k9_tmap_1(X0,sK4),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,sK4))) | ~v1_funct_1(k9_tmap_1(X0,sK4)) | ~m1_pre_topc(sK4,X0) | ~v1_tsep_1(sK4,X0)) & ((m1_subset_1(k9_tmap_1(X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,sK4))))) & v5_pre_topc(k9_tmap_1(X0,sK4),X0,k8_tmap_1(X0,sK4)) & v1_funct_2(k9_tmap_1(X0,sK4),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,sK4))) & v1_funct_1(k9_tmap_1(X0,sK4))) | (m1_pre_topc(sK4,X0) & v1_tsep_1(sK4,X0))) & m1_pre_topc(sK4,X0))) )),
% 51.28/7.00    introduced(choice_axiom,[])).
% 51.28/7.00  
% 51.28/7.00  fof(f65,plain,(
% 51.28/7.00    ? [X0] : (? [X1] : ((~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~m1_subset_1(k9_tmap_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X1))))) | ~v5_pre_topc(k9_tmap_1(sK3,X1),sK3,k8_tmap_1(sK3,X1)) | ~v1_funct_2(k9_tmap_1(sK3,X1),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X1))) | ~v1_funct_1(k9_tmap_1(sK3,X1)) | ~m1_pre_topc(X1,sK3) | ~v1_tsep_1(X1,sK3)) & ((m1_subset_1(k9_tmap_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X1))))) & v5_pre_topc(k9_tmap_1(sK3,X1),sK3,k8_tmap_1(sK3,X1)) & v1_funct_2(k9_tmap_1(sK3,X1),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X1))) & v1_funct_1(k9_tmap_1(sK3,X1))) | (m1_pre_topc(X1,sK3) & v1_tsep_1(X1,sK3))) & m1_pre_topc(X1,sK3)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 51.28/7.00    introduced(choice_axiom,[])).
% 51.28/7.00  
% 51.28/7.00  fof(f67,plain,(
% 51.28/7.00    ((~m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) | ~v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4)) | ~v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) | ~v1_funct_1(k9_tmap_1(sK3,sK4)) | ~m1_pre_topc(sK4,sK3) | ~v1_tsep_1(sK4,sK3)) & ((m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) & v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4)) & v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) & v1_funct_1(k9_tmap_1(sK3,sK4))) | (m1_pre_topc(sK4,sK3) & v1_tsep_1(sK4,sK3))) & m1_pre_topc(sK4,sK3)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 51.28/7.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f64,f66,f65])).
% 51.28/7.00  
% 51.28/7.00  fof(f117,plain,(
% 51.28/7.00    m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) | m1_pre_topc(sK4,sK3)),
% 51.28/7.00    inference(cnf_transformation,[],[f67])).
% 51.28/7.00  
% 51.28/7.00  fof(f109,plain,(
% 51.28/7.00    m1_pre_topc(sK4,sK3)),
% 51.28/7.00    inference(cnf_transformation,[],[f67])).
% 51.28/7.00  
% 51.28/7.00  fof(f108,plain,(
% 51.28/7.00    l1_pre_topc(sK3)),
% 51.28/7.00    inference(cnf_transformation,[],[f67])).
% 51.28/7.00  
% 51.28/7.00  fof(f5,axiom,(
% 51.28/7.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))))),
% 51.28/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.28/7.00  
% 51.28/7.00  fof(f25,plain,(
% 51.28/7.00    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 51.28/7.00    inference(ennf_transformation,[],[f5])).
% 51.28/7.00  
% 51.28/7.00  fof(f26,plain,(
% 51.28/7.00    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 51.28/7.00    inference(flattening,[],[f25])).
% 51.28/7.00  
% 51.28/7.00  fof(f72,plain,(
% 51.28/7.00    ( ! [X0,X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.28/7.00    inference(cnf_transformation,[],[f26])).
% 51.28/7.00  
% 51.28/7.00  fof(f106,plain,(
% 51.28/7.00    ~v2_struct_0(sK3)),
% 51.28/7.00    inference(cnf_transformation,[],[f67])).
% 51.28/7.00  
% 51.28/7.00  fof(f107,plain,(
% 51.28/7.00    v2_pre_topc(sK3)),
% 51.28/7.00    inference(cnf_transformation,[],[f67])).
% 51.28/7.00  
% 51.28/7.00  fof(f10,axiom,(
% 51.28/7.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 51.28/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.28/7.00  
% 51.28/7.00  fof(f35,plain,(
% 51.28/7.00    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 51.28/7.00    inference(ennf_transformation,[],[f10])).
% 51.28/7.00  
% 51.28/7.00  fof(f36,plain,(
% 51.28/7.00    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 51.28/7.00    inference(flattening,[],[f35])).
% 51.28/7.00  
% 51.28/7.00  fof(f90,plain,(
% 51.28/7.00    ( ! [X0,X1] : (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.28/7.00    inference(cnf_transformation,[],[f36])).
% 51.28/7.00  
% 51.28/7.00  fof(f12,axiom,(
% 51.28/7.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))))),
% 51.28/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.28/7.00  
% 51.28/7.00  fof(f39,plain,(
% 51.28/7.00    ! [X0,X1] : ((v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 51.28/7.00    inference(ennf_transformation,[],[f12])).
% 51.28/7.00  
% 51.28/7.00  fof(f40,plain,(
% 51.28/7.00    ! [X0,X1] : ((v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 51.28/7.00    inference(flattening,[],[f39])).
% 51.28/7.00  
% 51.28/7.00  fof(f95,plain,(
% 51.28/7.00    ( ! [X0,X1] : (v1_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.28/7.00    inference(cnf_transformation,[],[f40])).
% 51.28/7.00  
% 51.28/7.00  fof(f6,axiom,(
% 51.28/7.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & v1_pre_topc(X2)) => (k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => k6_tmap_1(X0,X3) = X2))))))),
% 51.28/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.28/7.00  
% 51.28/7.00  fof(f27,plain,(
% 51.28/7.00    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : ((k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 51.28/7.00    inference(ennf_transformation,[],[f6])).
% 51.28/7.00  
% 51.28/7.00  fof(f28,plain,(
% 51.28/7.00    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 51.28/7.00    inference(flattening,[],[f27])).
% 51.28/7.00  
% 51.28/7.00  fof(f49,plain,(
% 51.28/7.00    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 51.28/7.00    inference(nnf_transformation,[],[f28])).
% 51.28/7.00  
% 51.28/7.00  fof(f50,plain,(
% 51.28/7.00    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 51.28/7.00    inference(rectify,[],[f49])).
% 51.28/7.00  
% 51.28/7.00  fof(f51,plain,(
% 51.28/7.00    ! [X2,X1,X0] : (? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (k6_tmap_1(X0,sK0(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK0(X0,X1,X2) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 51.28/7.00    introduced(choice_axiom,[])).
% 51.28/7.00  
% 51.28/7.00  fof(f52,plain,(
% 51.28/7.00    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | (k6_tmap_1(X0,sK0(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK0(X0,X1,X2) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 51.28/7.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f50,f51])).
% 51.28/7.00  
% 51.28/7.00  fof(f75,plain,(
% 51.28/7.00    ( ! [X2,X0,X1] : (k8_tmap_1(X0,X1) = X2 | u1_struct_0(X1) = sK0(X0,X1,X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.28/7.00    inference(cnf_transformation,[],[f52])).
% 51.28/7.00  
% 51.28/7.00  fof(f96,plain,(
% 51.28/7.00    ( ! [X0,X1] : (v2_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.28/7.00    inference(cnf_transformation,[],[f40])).
% 51.28/7.00  
% 51.28/7.00  fof(f9,axiom,(
% 51.28/7.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))))),
% 51.28/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.28/7.00  
% 51.28/7.00  fof(f33,plain,(
% 51.28/7.00    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 51.28/7.00    inference(ennf_transformation,[],[f9])).
% 51.28/7.00  
% 51.28/7.00  fof(f34,plain,(
% 51.28/7.00    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 51.28/7.00    inference(flattening,[],[f33])).
% 51.28/7.00  
% 51.28/7.00  fof(f87,plain,(
% 51.28/7.00    ( ! [X0,X1] : (l1_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.28/7.00    inference(cnf_transformation,[],[f34])).
% 51.28/7.00  
% 51.28/7.00  fof(f76,plain,(
% 51.28/7.00    ( ! [X2,X0,X1] : (k8_tmap_1(X0,X1) = X2 | k6_tmap_1(X0,sK0(X0,X1,X2)) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.28/7.00    inference(cnf_transformation,[],[f52])).
% 51.28/7.00  
% 51.28/7.00  fof(f7,axiom,(
% 51.28/7.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(X2)) => (k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))))))))),
% 51.28/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.28/7.00  
% 51.28/7.00  fof(f29,plain,(
% 51.28/7.00    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : ((r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 51.28/7.00    inference(ennf_transformation,[],[f7])).
% 51.28/7.00  
% 51.28/7.00  fof(f30,plain,(
% 51.28/7.00    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 51.28/7.00    inference(flattening,[],[f29])).
% 51.28/7.00  
% 51.28/7.00  fof(f53,plain,(
% 51.28/7.00    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | ? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 51.28/7.00    inference(nnf_transformation,[],[f30])).
% 51.28/7.00  
% 51.28/7.00  fof(f54,plain,(
% 51.28/7.00    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | ? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 51.28/7.00    inference(rectify,[],[f53])).
% 51.28/7.00  
% 51.28/7.00  fof(f55,plain,(
% 51.28/7.00    ! [X2,X1,X0] : (? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2))) & u1_struct_0(X1) = sK1(X0,X1,X2) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 51.28/7.00    introduced(choice_axiom,[])).
% 51.28/7.00  
% 51.28/7.00  fof(f56,plain,(
% 51.28/7.00    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2))) & u1_struct_0(X1) = sK1(X0,X1,X2) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 51.28/7.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f54,f55])).
% 51.28/7.00  
% 51.28/7.00  fof(f78,plain,(
% 51.28/7.00    ( ! [X2,X0,X1] : (k9_tmap_1(X0,X1) = X2 | m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.28/7.00    inference(cnf_transformation,[],[f56])).
% 51.28/7.00  
% 51.28/7.00  fof(f88,plain,(
% 51.28/7.00    ( ! [X0,X1] : (v1_funct_1(k7_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.28/7.00    inference(cnf_transformation,[],[f36])).
% 51.28/7.00  
% 51.28/7.00  fof(f89,plain,(
% 51.28/7.00    ( ! [X0,X1] : (v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.28/7.00    inference(cnf_transformation,[],[f36])).
% 51.28/7.00  
% 51.28/7.00  fof(f13,axiom,(
% 51.28/7.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 51.28/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.28/7.00  
% 51.28/7.00  fof(f41,plain,(
% 51.28/7.00    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 51.28/7.00    inference(ennf_transformation,[],[f13])).
% 51.28/7.00  
% 51.28/7.00  fof(f42,plain,(
% 51.28/7.00    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 51.28/7.00    inference(flattening,[],[f41])).
% 51.28/7.00  
% 51.28/7.00  fof(f97,plain,(
% 51.28/7.00    ( ! [X0,X1] : (u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.28/7.00    inference(cnf_transformation,[],[f42])).
% 51.28/7.00  
% 51.28/7.00  fof(f94,plain,(
% 51.28/7.00    ( ! [X0,X1] : (~v2_struct_0(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.28/7.00    inference(cnf_transformation,[],[f40])).
% 51.28/7.00  
% 51.28/7.00  fof(f1,axiom,(
% 51.28/7.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 51.28/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.28/7.00  
% 51.28/7.00  fof(f19,plain,(
% 51.28/7.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 51.28/7.00    inference(ennf_transformation,[],[f1])).
% 51.28/7.00  
% 51.28/7.00  fof(f68,plain,(
% 51.28/7.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 51.28/7.00    inference(cnf_transformation,[],[f19])).
% 51.28/7.00  
% 51.28/7.00  fof(f2,axiom,(
% 51.28/7.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 51.28/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.28/7.00  
% 51.28/7.00  fof(f20,plain,(
% 51.28/7.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 51.28/7.00    inference(ennf_transformation,[],[f2])).
% 51.28/7.00  
% 51.28/7.00  fof(f21,plain,(
% 51.28/7.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 51.28/7.00    inference(flattening,[],[f20])).
% 51.28/7.00  
% 51.28/7.00  fof(f69,plain,(
% 51.28/7.00    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 51.28/7.00    inference(cnf_transformation,[],[f21])).
% 51.28/7.00  
% 51.28/7.00  fof(f4,axiom,(
% 51.28/7.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => r1_funct_2(X0,X1,X2,X3,X4,X4))),
% 51.28/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.28/7.00  
% 51.28/7.00  fof(f23,plain,(
% 51.28/7.00    ! [X0,X1,X2,X3,X4,X5] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 51.28/7.00    inference(ennf_transformation,[],[f4])).
% 51.28/7.00  
% 51.28/7.00  fof(f24,plain,(
% 51.28/7.00    ! [X0,X1,X2,X3,X4,X5] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 51.28/7.00    inference(flattening,[],[f23])).
% 51.28/7.00  
% 51.28/7.00  fof(f71,plain,(
% 51.28/7.00    ( ! [X4,X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 51.28/7.00    inference(cnf_transformation,[],[f24])).
% 51.28/7.00  
% 51.28/7.00  fof(f80,plain,(
% 51.28/7.00    ( ! [X2,X0,X1] : (k9_tmap_1(X0,X1) = X2 | ~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.28/7.00    inference(cnf_transformation,[],[f56])).
% 51.28/7.00  
% 51.28/7.00  fof(f11,axiom,(
% 51.28/7.00    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))))),
% 51.28/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.28/7.00  
% 51.28/7.00  fof(f37,plain,(
% 51.28/7.00    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 51.28/7.00    inference(ennf_transformation,[],[f11])).
% 51.28/7.00  
% 51.28/7.00  fof(f38,plain,(
% 51.28/7.00    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 51.28/7.00    inference(flattening,[],[f37])).
% 51.28/7.00  
% 51.28/7.00  fof(f92,plain,(
% 51.28/7.00    ( ! [X0,X1] : (v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.28/7.00    inference(cnf_transformation,[],[f38])).
% 51.28/7.00  
% 51.28/7.00  fof(f93,plain,(
% 51.28/7.00    ( ! [X0,X1] : (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.28/7.00    inference(cnf_transformation,[],[f38])).
% 51.28/7.00  
% 51.28/7.00  fof(f91,plain,(
% 51.28/7.00    ( ! [X0,X1] : (v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.28/7.00    inference(cnf_transformation,[],[f38])).
% 51.28/7.00  
% 51.28/7.00  fof(f14,axiom,(
% 51.28/7.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))))),
% 51.28/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.28/7.00  
% 51.28/7.00  fof(f43,plain,(
% 51.28/7.00    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 51.28/7.00    inference(ennf_transformation,[],[f14])).
% 51.28/7.00  
% 51.28/7.00  fof(f44,plain,(
% 51.28/7.00    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 51.28/7.00    inference(flattening,[],[f43])).
% 51.28/7.00  
% 51.28/7.00  fof(f61,plain,(
% 51.28/7.00    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | (~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1)))) & ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 51.28/7.00    inference(nnf_transformation,[],[f44])).
% 51.28/7.00  
% 51.28/7.00  fof(f62,plain,(
% 51.28/7.00    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1))) & ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 51.28/7.00    inference(flattening,[],[f61])).
% 51.28/7.00  
% 51.28/7.00  fof(f101,plain,(
% 51.28/7.00    ( ! [X0,X1] : (v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.28/7.00    inference(cnf_transformation,[],[f62])).
% 51.28/7.00  
% 51.28/7.00  fof(f118,plain,(
% 51.28/7.00    ~m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) | ~v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4)) | ~v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) | ~v1_funct_1(k9_tmap_1(sK3,sK4)) | ~m1_pre_topc(sK4,sK3) | ~v1_tsep_1(sK4,sK3)),
% 51.28/7.00    inference(cnf_transformation,[],[f67])).
% 51.28/7.00  
% 51.28/7.00  fof(f8,axiom,(
% 51.28/7.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tsep_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v3_pre_topc(X2,X0))))))),
% 51.28/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.28/7.00  
% 51.28/7.00  fof(f31,plain,(
% 51.28/7.00    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 51.28/7.00    inference(ennf_transformation,[],[f8])).
% 51.28/7.00  
% 51.28/7.00  fof(f32,plain,(
% 51.28/7.00    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 51.28/7.00    inference(flattening,[],[f31])).
% 51.28/7.00  
% 51.28/7.00  fof(f57,plain,(
% 51.28/7.00    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 51.28/7.00    inference(nnf_transformation,[],[f32])).
% 51.28/7.00  
% 51.28/7.00  fof(f58,plain,(
% 51.28/7.00    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 51.28/7.00    inference(rectify,[],[f57])).
% 51.28/7.00  
% 51.28/7.00  fof(f59,plain,(
% 51.28/7.00    ! [X1,X0] : (? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK2(X0,X1),X0) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 51.28/7.00    introduced(choice_axiom,[])).
% 51.28/7.00  
% 51.28/7.00  fof(f60,plain,(
% 51.28/7.00    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | (~v3_pre_topc(sK2(X0,X1),X0) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 51.28/7.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f58,f59])).
% 51.28/7.00  
% 51.28/7.00  fof(f81,plain,(
% 51.28/7.00    ( ! [X0,X3,X1] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 51.28/7.00    inference(cnf_transformation,[],[f60])).
% 51.28/7.00  
% 51.28/7.00  fof(f123,plain,(
% 51.28/7.00    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 51.28/7.00    inference(equality_resolution,[],[f81])).
% 51.28/7.00  
% 51.28/7.00  fof(f16,axiom,(
% 51.28/7.00    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 51.28/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.28/7.00  
% 51.28/7.00  fof(f46,plain,(
% 51.28/7.00    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 51.28/7.00    inference(ennf_transformation,[],[f16])).
% 51.28/7.00  
% 51.28/7.00  fof(f105,plain,(
% 51.28/7.00    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 51.28/7.00    inference(cnf_transformation,[],[f46])).
% 51.28/7.00  
% 51.28/7.00  fof(f73,plain,(
% 51.28/7.00    ( ! [X4,X2,X0,X1] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.28/7.00    inference(cnf_transformation,[],[f52])).
% 51.28/7.00  
% 51.28/7.00  fof(f119,plain,(
% 51.28/7.00    ( ! [X2,X0,X1] : (k6_tmap_1(X0,u1_struct_0(X1)) = X2 | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.28/7.00    inference(equality_resolution,[],[f73])).
% 51.28/7.00  
% 51.28/7.00  fof(f120,plain,(
% 51.28/7.00    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.28/7.00    inference(equality_resolution,[],[f119])).
% 51.28/7.00  
% 51.28/7.00  fof(f103,plain,(
% 51.28/7.00    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.28/7.00    inference(cnf_transformation,[],[f62])).
% 51.28/7.00  
% 51.28/7.00  fof(f114,plain,(
% 51.28/7.00    v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4)) | v1_tsep_1(sK4,sK3)),
% 51.28/7.00    inference(cnf_transformation,[],[f67])).
% 51.28/7.00  
% 51.28/7.00  fof(f84,plain,(
% 51.28/7.00    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(sK2(X0,X1),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 51.28/7.00    inference(cnf_transformation,[],[f60])).
% 51.28/7.00  
% 51.28/7.00  fof(f82,plain,(
% 51.28/7.00    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 51.28/7.00    inference(cnf_transformation,[],[f60])).
% 51.28/7.00  
% 51.28/7.00  fof(f74,plain,(
% 51.28/7.00    ( ! [X2,X0,X1] : (k8_tmap_1(X0,X1) = X2 | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.28/7.00    inference(cnf_transformation,[],[f52])).
% 51.28/7.00  
% 51.28/7.00  fof(f83,plain,(
% 51.28/7.00    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | u1_struct_0(X1) = sK2(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 51.28/7.00    inference(cnf_transformation,[],[f60])).
% 51.28/7.00  
% 51.28/7.00  cnf(c_36,plain,
% 51.28/7.00      ( ~ m1_pre_topc(X0,X1)
% 51.28/7.00      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 51.28/7.00      | ~ l1_pre_topc(X1) ),
% 51.28/7.00      inference(cnf_transformation,[],[f104]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_39,negated_conjecture,
% 51.28/7.00      ( m1_pre_topc(sK4,sK3)
% 51.28/7.00      | m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) ),
% 51.28/7.00      inference(cnf_transformation,[],[f117]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_47,negated_conjecture,
% 51.28/7.00      ( m1_pre_topc(sK4,sK3) ),
% 51.28/7.00      inference(cnf_transformation,[],[f109]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_298,negated_conjecture,
% 51.28/7.00      ( m1_pre_topc(sK4,sK3) ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_39,c_47]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1690,plain,
% 51.28/7.00      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 51.28/7.00      | ~ l1_pre_topc(X1)
% 51.28/7.00      | sK4 != X0
% 51.28/7.00      | sK3 != X1 ),
% 51.28/7.00      inference(resolution_lifted,[status(thm)],[c_36,c_298]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1691,plain,
% 51.28/7.00      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 51.28/7.00      | ~ l1_pre_topc(sK3) ),
% 51.28/7.00      inference(unflattening,[status(thm)],[c_1690]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_48,negated_conjecture,
% 51.28/7.00      ( l1_pre_topc(sK3) ),
% 51.28/7.00      inference(cnf_transformation,[],[f108]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1693,plain,
% 51.28/7.00      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_1691,c_48]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_3906,plain,
% 51.28/7.00      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 51.28/7.00      inference(subtyping,[status(esa)],[c_1693]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_4955,plain,
% 51.28/7.00      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 51.28/7.00      inference(predicate_to_equality,[status(thm)],[c_3906]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_4,plain,
% 51.28/7.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 51.28/7.00      | ~ v2_pre_topc(X1)
% 51.28/7.00      | v2_struct_0(X1)
% 51.28/7.00      | ~ l1_pre_topc(X1)
% 51.28/7.00      | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1)) ),
% 51.28/7.00      inference(cnf_transformation,[],[f72]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_3930,plain,
% 51.28/7.00      ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_57)))
% 51.28/7.00      | ~ v2_pre_topc(X0_57)
% 51.28/7.00      | v2_struct_0(X0_57)
% 51.28/7.00      | ~ l1_pre_topc(X0_57)
% 51.28/7.00      | k7_tmap_1(X0_57,X0_58) = k6_partfun1(u1_struct_0(X0_57)) ),
% 51.28/7.00      inference(subtyping,[status(esa)],[c_4]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_4931,plain,
% 51.28/7.00      ( k7_tmap_1(X0_57,X0_58) = k6_partfun1(u1_struct_0(X0_57))
% 51.28/7.00      | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_57))) != iProver_top
% 51.28/7.00      | v2_pre_topc(X0_57) != iProver_top
% 51.28/7.00      | v2_struct_0(X0_57) = iProver_top
% 51.28/7.00      | l1_pre_topc(X0_57) != iProver_top ),
% 51.28/7.00      inference(predicate_to_equality,[status(thm)],[c_3930]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_6410,plain,
% 51.28/7.00      ( k7_tmap_1(sK3,u1_struct_0(sK4)) = k6_partfun1(u1_struct_0(sK3))
% 51.28/7.00      | v2_pre_topc(sK3) != iProver_top
% 51.28/7.00      | v2_struct_0(sK3) = iProver_top
% 51.28/7.00      | l1_pre_topc(sK3) != iProver_top ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_4955,c_4931]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_50,negated_conjecture,
% 51.28/7.00      ( ~ v2_struct_0(sK3) ),
% 51.28/7.00      inference(cnf_transformation,[],[f106]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_49,negated_conjecture,
% 51.28/7.00      ( v2_pre_topc(sK3) ),
% 51.28/7.00      inference(cnf_transformation,[],[f107]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_5701,plain,
% 51.28/7.00      ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 51.28/7.00      | ~ v2_pre_topc(sK3)
% 51.28/7.00      | v2_struct_0(sK3)
% 51.28/7.00      | ~ l1_pre_topc(sK3)
% 51.28/7.00      | k7_tmap_1(sK3,u1_struct_0(sK4)) = k6_partfun1(u1_struct_0(sK3)) ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_3930]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_7517,plain,
% 51.28/7.00      ( k7_tmap_1(sK3,u1_struct_0(sK4)) = k6_partfun1(u1_struct_0(sK3)) ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_6410,c_50,c_49,c_48,c_1691,c_5701]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_20,plain,
% 51.28/7.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 51.28/7.00      | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
% 51.28/7.00      | ~ v2_pre_topc(X1)
% 51.28/7.00      | v2_struct_0(X1)
% 51.28/7.00      | ~ l1_pre_topc(X1) ),
% 51.28/7.00      inference(cnf_transformation,[],[f90]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_3926,plain,
% 51.28/7.00      ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_57)))
% 51.28/7.00      | m1_subset_1(k7_tmap_1(X0_57,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(k6_tmap_1(X0_57,X0_58)))))
% 51.28/7.00      | ~ v2_pre_topc(X0_57)
% 51.28/7.00      | v2_struct_0(X0_57)
% 51.28/7.00      | ~ l1_pre_topc(X0_57) ),
% 51.28/7.00      inference(subtyping,[status(esa)],[c_20]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_4935,plain,
% 51.28/7.00      ( m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_57))) != iProver_top
% 51.28/7.00      | m1_subset_1(k7_tmap_1(X0_57,X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(k6_tmap_1(X0_57,X0_58))))) = iProver_top
% 51.28/7.00      | v2_pre_topc(X0_57) != iProver_top
% 51.28/7.00      | v2_struct_0(X0_57) = iProver_top
% 51.28/7.00      | l1_pre_topc(X0_57) != iProver_top ),
% 51.28/7.00      inference(predicate_to_equality,[status(thm)],[c_3926]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_7536,plain,
% 51.28/7.00      ( m1_subset_1(k6_partfun1(u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))))) = iProver_top
% 51.28/7.00      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 51.28/7.00      | v2_pre_topc(sK3) != iProver_top
% 51.28/7.00      | v2_struct_0(sK3) = iProver_top
% 51.28/7.00      | l1_pre_topc(sK3) != iProver_top ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_7517,c_4935]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_51,plain,
% 51.28/7.00      ( v2_struct_0(sK3) != iProver_top ),
% 51.28/7.00      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_52,plain,
% 51.28/7.00      ( v2_pre_topc(sK3) = iProver_top ),
% 51.28/7.00      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_53,plain,
% 51.28/7.00      ( l1_pre_topc(sK3) = iProver_top ),
% 51.28/7.00      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1692,plain,
% 51.28/7.00      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 51.28/7.00      | l1_pre_topc(sK3) != iProver_top ),
% 51.28/7.00      inference(predicate_to_equality,[status(thm)],[c_1691]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_21416,plain,
% 51.28/7.00      ( m1_subset_1(k6_partfun1(u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))))) = iProver_top ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_7536,c_51,c_52,c_53,c_1692]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_27,plain,
% 51.28/7.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 51.28/7.00      | v1_pre_topc(k6_tmap_1(X1,X0))
% 51.28/7.00      | ~ v2_pre_topc(X1)
% 51.28/7.00      | v2_struct_0(X1)
% 51.28/7.00      | ~ l1_pre_topc(X1) ),
% 51.28/7.00      inference(cnf_transformation,[],[f95]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_3927,plain,
% 51.28/7.00      ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_57)))
% 51.28/7.00      | v1_pre_topc(k6_tmap_1(X0_57,X0_58))
% 51.28/7.00      | ~ v2_pre_topc(X0_57)
% 51.28/7.00      | v2_struct_0(X0_57)
% 51.28/7.00      | ~ l1_pre_topc(X0_57) ),
% 51.28/7.00      inference(subtyping,[status(esa)],[c_27]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_4934,plain,
% 51.28/7.00      ( m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_57))) != iProver_top
% 51.28/7.00      | v1_pre_topc(k6_tmap_1(X0_57,X0_58)) = iProver_top
% 51.28/7.00      | v2_pre_topc(X0_57) != iProver_top
% 51.28/7.00      | v2_struct_0(X0_57) = iProver_top
% 51.28/7.00      | l1_pre_topc(X0_57) != iProver_top ),
% 51.28/7.00      inference(predicate_to_equality,[status(thm)],[c_3927]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_5797,plain,
% 51.28/7.00      ( v1_pre_topc(k6_tmap_1(sK3,u1_struct_0(sK4))) = iProver_top
% 51.28/7.00      | v2_pre_topc(sK3) != iProver_top
% 51.28/7.00      | v2_struct_0(sK3) = iProver_top
% 51.28/7.00      | l1_pre_topc(sK3) != iProver_top ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_4955,c_4934]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_5630,plain,
% 51.28/7.00      ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 51.28/7.00      | v1_pre_topc(k6_tmap_1(sK3,u1_struct_0(sK4)))
% 51.28/7.00      | ~ v2_pre_topc(sK3)
% 51.28/7.00      | v2_struct_0(sK3)
% 51.28/7.00      | ~ l1_pre_topc(sK3) ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_3927]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_5631,plain,
% 51.28/7.00      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 51.28/7.00      | v1_pre_topc(k6_tmap_1(sK3,u1_struct_0(sK4))) = iProver_top
% 51.28/7.00      | v2_pre_topc(sK3) != iProver_top
% 51.28/7.00      | v2_struct_0(sK3) = iProver_top
% 51.28/7.00      | l1_pre_topc(sK3) != iProver_top ),
% 51.28/7.00      inference(predicate_to_equality,[status(thm)],[c_5630]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_7393,plain,
% 51.28/7.00      ( v1_pre_topc(k6_tmap_1(sK3,u1_struct_0(sK4))) = iProver_top ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_5797,c_51,c_52,c_53,c_1692,c_5631]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_6,plain,
% 51.28/7.00      ( ~ m1_pre_topc(X0,X1)
% 51.28/7.00      | ~ v1_pre_topc(X2)
% 51.28/7.00      | ~ v2_pre_topc(X1)
% 51.28/7.00      | ~ v2_pre_topc(X2)
% 51.28/7.00      | v2_struct_0(X1)
% 51.28/7.00      | ~ l1_pre_topc(X1)
% 51.28/7.00      | ~ l1_pre_topc(X2)
% 51.28/7.00      | sK0(X1,X0,X2) = u1_struct_0(X0)
% 51.28/7.00      | k8_tmap_1(X1,X0) = X2 ),
% 51.28/7.00      inference(cnf_transformation,[],[f75]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1778,plain,
% 51.28/7.00      ( ~ v1_pre_topc(X0)
% 51.28/7.00      | ~ v2_pre_topc(X1)
% 51.28/7.00      | ~ v2_pre_topc(X0)
% 51.28/7.00      | v2_struct_0(X1)
% 51.28/7.00      | ~ l1_pre_topc(X1)
% 51.28/7.00      | ~ l1_pre_topc(X0)
% 51.28/7.00      | sK0(X1,X2,X0) = u1_struct_0(X2)
% 51.28/7.00      | k8_tmap_1(X1,X2) = X0
% 51.28/7.00      | sK4 != X2
% 51.28/7.00      | sK3 != X1 ),
% 51.28/7.00      inference(resolution_lifted,[status(thm)],[c_6,c_298]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1779,plain,
% 51.28/7.00      ( ~ v1_pre_topc(X0)
% 51.28/7.00      | ~ v2_pre_topc(X0)
% 51.28/7.00      | ~ v2_pre_topc(sK3)
% 51.28/7.00      | v2_struct_0(sK3)
% 51.28/7.00      | ~ l1_pre_topc(X0)
% 51.28/7.00      | ~ l1_pre_topc(sK3)
% 51.28/7.00      | sK0(sK3,sK4,X0) = u1_struct_0(sK4)
% 51.28/7.00      | k8_tmap_1(sK3,sK4) = X0 ),
% 51.28/7.00      inference(unflattening,[status(thm)],[c_1778]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1783,plain,
% 51.28/7.00      ( ~ l1_pre_topc(X0)
% 51.28/7.00      | ~ v2_pre_topc(X0)
% 51.28/7.00      | ~ v1_pre_topc(X0)
% 51.28/7.00      | sK0(sK3,sK4,X0) = u1_struct_0(sK4)
% 51.28/7.00      | k8_tmap_1(sK3,sK4) = X0 ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_1779,c_50,c_49,c_48]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1784,plain,
% 51.28/7.00      ( ~ v1_pre_topc(X0)
% 51.28/7.00      | ~ v2_pre_topc(X0)
% 51.28/7.00      | ~ l1_pre_topc(X0)
% 51.28/7.00      | sK0(sK3,sK4,X0) = u1_struct_0(sK4)
% 51.28/7.00      | k8_tmap_1(sK3,sK4) = X0 ),
% 51.28/7.00      inference(renaming,[status(thm)],[c_1783]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_3900,plain,
% 51.28/7.00      ( ~ v1_pre_topc(X0_57)
% 51.28/7.00      | ~ v2_pre_topc(X0_57)
% 51.28/7.00      | ~ l1_pre_topc(X0_57)
% 51.28/7.00      | sK0(sK3,sK4,X0_57) = u1_struct_0(sK4)
% 51.28/7.00      | k8_tmap_1(sK3,sK4) = X0_57 ),
% 51.28/7.00      inference(subtyping,[status(esa)],[c_1784]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_4961,plain,
% 51.28/7.00      ( sK0(sK3,sK4,X0_57) = u1_struct_0(sK4)
% 51.28/7.00      | k8_tmap_1(sK3,sK4) = X0_57
% 51.28/7.00      | v1_pre_topc(X0_57) != iProver_top
% 51.28/7.00      | v2_pre_topc(X0_57) != iProver_top
% 51.28/7.00      | l1_pre_topc(X0_57) != iProver_top ),
% 51.28/7.00      inference(predicate_to_equality,[status(thm)],[c_3900]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_7398,plain,
% 51.28/7.00      ( sK0(sK3,sK4,k6_tmap_1(sK3,u1_struct_0(sK4))) = u1_struct_0(sK4)
% 51.28/7.00      | k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4)
% 51.28/7.00      | v2_pre_topc(k6_tmap_1(sK3,u1_struct_0(sK4))) != iProver_top
% 51.28/7.00      | l1_pre_topc(k6_tmap_1(sK3,u1_struct_0(sK4))) != iProver_top ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_7393,c_4961]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_3933,plain,( X0_57 = X0_57 ),theory(equality) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_3985,plain,
% 51.28/7.00      ( sK3 = sK3 ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_3933]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_26,plain,
% 51.28/7.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 51.28/7.00      | ~ v2_pre_topc(X1)
% 51.28/7.00      | v2_pre_topc(k6_tmap_1(X1,X0))
% 51.28/7.00      | v2_struct_0(X1)
% 51.28/7.00      | ~ l1_pre_topc(X1) ),
% 51.28/7.00      inference(cnf_transformation,[],[f96]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_3928,plain,
% 51.28/7.00      ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_57)))
% 51.28/7.00      | ~ v2_pre_topc(X0_57)
% 51.28/7.00      | v2_pre_topc(k6_tmap_1(X0_57,X0_58))
% 51.28/7.00      | v2_struct_0(X0_57)
% 51.28/7.00      | ~ l1_pre_topc(X0_57) ),
% 51.28/7.00      inference(subtyping,[status(esa)],[c_26]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_5677,plain,
% 51.28/7.00      ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 51.28/7.00      | v2_pre_topc(k6_tmap_1(sK3,u1_struct_0(sK4)))
% 51.28/7.00      | ~ v2_pre_topc(sK3)
% 51.28/7.00      | v2_struct_0(sK3)
% 51.28/7.00      | ~ l1_pre_topc(sK3) ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_3928]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_5678,plain,
% 51.28/7.00      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 51.28/7.00      | v2_pre_topc(k6_tmap_1(sK3,u1_struct_0(sK4))) = iProver_top
% 51.28/7.00      | v2_pre_topc(sK3) != iProver_top
% 51.28/7.00      | v2_struct_0(sK3) = iProver_top
% 51.28/7.00      | l1_pre_topc(sK3) != iProver_top ),
% 51.28/7.00      inference(predicate_to_equality,[status(thm)],[c_5677]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_17,plain,
% 51.28/7.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 51.28/7.00      | ~ v2_pre_topc(X1)
% 51.28/7.00      | v2_struct_0(X1)
% 51.28/7.00      | ~ l1_pre_topc(X1)
% 51.28/7.00      | l1_pre_topc(k6_tmap_1(X1,X0)) ),
% 51.28/7.00      inference(cnf_transformation,[],[f87]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_3929,plain,
% 51.28/7.00      ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_57)))
% 51.28/7.00      | ~ v2_pre_topc(X0_57)
% 51.28/7.00      | v2_struct_0(X0_57)
% 51.28/7.00      | ~ l1_pre_topc(X0_57)
% 51.28/7.00      | l1_pre_topc(k6_tmap_1(X0_57,X0_58)) ),
% 51.28/7.00      inference(subtyping,[status(esa)],[c_17]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_5685,plain,
% 51.28/7.00      ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 51.28/7.00      | ~ v2_pre_topc(sK3)
% 51.28/7.00      | v2_struct_0(sK3)
% 51.28/7.00      | l1_pre_topc(k6_tmap_1(sK3,u1_struct_0(sK4)))
% 51.28/7.00      | ~ l1_pre_topc(sK3) ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_3929]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_5686,plain,
% 51.28/7.00      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 51.28/7.00      | v2_pre_topc(sK3) != iProver_top
% 51.28/7.00      | v2_struct_0(sK3) = iProver_top
% 51.28/7.00      | l1_pre_topc(k6_tmap_1(sK3,u1_struct_0(sK4))) = iProver_top
% 51.28/7.00      | l1_pre_topc(sK3) != iProver_top ),
% 51.28/7.00      inference(predicate_to_equality,[status(thm)],[c_5685]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_5,plain,
% 51.28/7.00      ( ~ m1_pre_topc(X0,X1)
% 51.28/7.00      | ~ v1_pre_topc(X2)
% 51.28/7.00      | ~ v2_pre_topc(X1)
% 51.28/7.00      | ~ v2_pre_topc(X2)
% 51.28/7.00      | v2_struct_0(X1)
% 51.28/7.00      | ~ l1_pre_topc(X1)
% 51.28/7.00      | ~ l1_pre_topc(X2)
% 51.28/7.00      | k6_tmap_1(X1,sK0(X1,X0,X2)) != X2
% 51.28/7.00      | k8_tmap_1(X1,X0) = X2 ),
% 51.28/7.00      inference(cnf_transformation,[],[f76]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1805,plain,
% 51.28/7.00      ( ~ v1_pre_topc(X0)
% 51.28/7.00      | ~ v2_pre_topc(X1)
% 51.28/7.00      | ~ v2_pre_topc(X0)
% 51.28/7.00      | v2_struct_0(X1)
% 51.28/7.00      | ~ l1_pre_topc(X1)
% 51.28/7.00      | ~ l1_pre_topc(X0)
% 51.28/7.00      | k6_tmap_1(X1,sK0(X1,X2,X0)) != X0
% 51.28/7.00      | k8_tmap_1(X1,X2) = X0
% 51.28/7.00      | sK4 != X2
% 51.28/7.00      | sK3 != X1 ),
% 51.28/7.00      inference(resolution_lifted,[status(thm)],[c_5,c_298]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1806,plain,
% 51.28/7.00      ( ~ v1_pre_topc(X0)
% 51.28/7.00      | ~ v2_pre_topc(X0)
% 51.28/7.00      | ~ v2_pre_topc(sK3)
% 51.28/7.00      | v2_struct_0(sK3)
% 51.28/7.00      | ~ l1_pre_topc(X0)
% 51.28/7.00      | ~ l1_pre_topc(sK3)
% 51.28/7.00      | k6_tmap_1(sK3,sK0(sK3,sK4,X0)) != X0
% 51.28/7.00      | k8_tmap_1(sK3,sK4) = X0 ),
% 51.28/7.00      inference(unflattening,[status(thm)],[c_1805]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1810,plain,
% 51.28/7.00      ( ~ l1_pre_topc(X0)
% 51.28/7.00      | ~ v2_pre_topc(X0)
% 51.28/7.00      | ~ v1_pre_topc(X0)
% 51.28/7.00      | k6_tmap_1(sK3,sK0(sK3,sK4,X0)) != X0
% 51.28/7.00      | k8_tmap_1(sK3,sK4) = X0 ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_1806,c_50,c_49,c_48]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1811,plain,
% 51.28/7.00      ( ~ v1_pre_topc(X0)
% 51.28/7.00      | ~ v2_pre_topc(X0)
% 51.28/7.00      | ~ l1_pre_topc(X0)
% 51.28/7.00      | k6_tmap_1(sK3,sK0(sK3,sK4,X0)) != X0
% 51.28/7.00      | k8_tmap_1(sK3,sK4) = X0 ),
% 51.28/7.00      inference(renaming,[status(thm)],[c_1810]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_3899,plain,
% 51.28/7.00      ( ~ v1_pre_topc(X0_57)
% 51.28/7.00      | ~ v2_pre_topc(X0_57)
% 51.28/7.00      | ~ l1_pre_topc(X0_57)
% 51.28/7.00      | k6_tmap_1(sK3,sK0(sK3,sK4,X0_57)) != X0_57
% 51.28/7.00      | k8_tmap_1(sK3,sK4) = X0_57 ),
% 51.28/7.00      inference(subtyping,[status(esa)],[c_1811]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_5955,plain,
% 51.28/7.00      ( ~ v1_pre_topc(k6_tmap_1(sK3,u1_struct_0(sK4)))
% 51.28/7.00      | ~ v2_pre_topc(k6_tmap_1(sK3,u1_struct_0(sK4)))
% 51.28/7.00      | ~ l1_pre_topc(k6_tmap_1(sK3,u1_struct_0(sK4)))
% 51.28/7.00      | k6_tmap_1(sK3,sK0(sK3,sK4,k6_tmap_1(sK3,u1_struct_0(sK4)))) != k6_tmap_1(sK3,u1_struct_0(sK4))
% 51.28/7.00      | k8_tmap_1(sK3,sK4) = k6_tmap_1(sK3,u1_struct_0(sK4)) ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_3899]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_3937,plain,
% 51.28/7.00      ( X0_57 != X1_57 | X2_57 != X1_57 | X2_57 = X0_57 ),
% 51.28/7.00      theory(equality) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_5864,plain,
% 51.28/7.00      ( k6_tmap_1(sK3,u1_struct_0(sK4)) != X0_57
% 51.28/7.00      | k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4)
% 51.28/7.00      | k8_tmap_1(sK3,sK4) != X0_57 ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_3937]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_6485,plain,
% 51.28/7.00      ( k6_tmap_1(sK3,u1_struct_0(sK4)) != k6_tmap_1(sK3,u1_struct_0(sK4))
% 51.28/7.00      | k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4)
% 51.28/7.00      | k8_tmap_1(sK3,sK4) != k6_tmap_1(sK3,u1_struct_0(sK4)) ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_5864]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_6486,plain,
% 51.28/7.00      ( k6_tmap_1(sK3,u1_struct_0(sK4)) = k6_tmap_1(sK3,u1_struct_0(sK4)) ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_3933]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_3955,plain,
% 51.28/7.00      ( X0_58 != X1_58
% 51.28/7.00      | X0_57 != X1_57
% 51.28/7.00      | k6_tmap_1(X0_57,X0_58) = k6_tmap_1(X1_57,X1_58) ),
% 51.28/7.00      theory(equality) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_6523,plain,
% 51.28/7.00      ( X0_58 != u1_struct_0(sK4)
% 51.28/7.00      | X0_57 != sK3
% 51.28/7.00      | k6_tmap_1(X0_57,X0_58) = k6_tmap_1(sK3,u1_struct_0(sK4)) ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_3955]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_8448,plain,
% 51.28/7.00      ( sK0(sK3,sK4,k6_tmap_1(sK3,u1_struct_0(sK4))) != u1_struct_0(sK4)
% 51.28/7.00      | X0_57 != sK3
% 51.28/7.00      | k6_tmap_1(X0_57,sK0(sK3,sK4,k6_tmap_1(sK3,u1_struct_0(sK4)))) = k6_tmap_1(sK3,u1_struct_0(sK4)) ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_6523]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_8449,plain,
% 51.28/7.00      ( sK0(sK3,sK4,k6_tmap_1(sK3,u1_struct_0(sK4))) != u1_struct_0(sK4)
% 51.28/7.00      | k6_tmap_1(sK3,sK0(sK3,sK4,k6_tmap_1(sK3,u1_struct_0(sK4)))) = k6_tmap_1(sK3,u1_struct_0(sK4))
% 51.28/7.00      | sK3 != sK3 ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_8448]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_8631,plain,
% 51.28/7.00      ( k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4) ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_7398,c_50,c_51,c_49,c_52,c_48,c_53,c_1691,c_1692,
% 51.28/7.00                 c_3985,c_5630,c_5677,c_5678,c_5685,c_5686,c_5955,c_6485,
% 51.28/7.00                 c_6486,c_8449]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_21420,plain,
% 51.28/7.00      ( m1_subset_1(k6_partfun1(u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) = iProver_top ),
% 51.28/7.00      inference(light_normalisation,[status(thm)],[c_21416,c_8631]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_11,plain,
% 51.28/7.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
% 51.28/7.00      | ~ m1_pre_topc(X2,X1)
% 51.28/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
% 51.28/7.00      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 51.28/7.00      | ~ v2_pre_topc(X1)
% 51.28/7.00      | ~ v1_funct_1(X0)
% 51.28/7.00      | v2_struct_0(X1)
% 51.28/7.00      | ~ l1_pre_topc(X1)
% 51.28/7.00      | k9_tmap_1(X1,X2) = X0 ),
% 51.28/7.00      inference(cnf_transformation,[],[f78]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_2060,plain,
% 51.28/7.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
% 51.28/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
% 51.28/7.00      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 51.28/7.00      | ~ v2_pre_topc(X1)
% 51.28/7.00      | ~ v1_funct_1(X0)
% 51.28/7.00      | v2_struct_0(X1)
% 51.28/7.00      | ~ l1_pre_topc(X1)
% 51.28/7.00      | k9_tmap_1(X1,X2) = X0
% 51.28/7.00      | sK4 != X2
% 51.28/7.00      | sK3 != X1 ),
% 51.28/7.00      inference(resolution_lifted,[status(thm)],[c_11,c_298]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_2061,plain,
% 51.28/7.00      ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 51.28/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 51.28/7.00      | m1_subset_1(sK1(sK3,sK4,X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 51.28/7.00      | ~ v2_pre_topc(sK3)
% 51.28/7.00      | ~ v1_funct_1(X0)
% 51.28/7.00      | v2_struct_0(sK3)
% 51.28/7.00      | ~ l1_pre_topc(sK3)
% 51.28/7.00      | k9_tmap_1(sK3,sK4) = X0 ),
% 51.28/7.00      inference(unflattening,[status(thm)],[c_2060]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_2065,plain,
% 51.28/7.00      ( m1_subset_1(sK1(sK3,sK4,X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 51.28/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 51.28/7.00      | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 51.28/7.00      | ~ v1_funct_1(X0)
% 51.28/7.00      | k9_tmap_1(sK3,sK4) = X0 ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_2061,c_50,c_49,c_48]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_2066,plain,
% 51.28/7.00      ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 51.28/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 51.28/7.00      | m1_subset_1(sK1(sK3,sK4,X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 51.28/7.00      | ~ v1_funct_1(X0)
% 51.28/7.00      | k9_tmap_1(sK3,sK4) = X0 ),
% 51.28/7.00      inference(renaming,[status(thm)],[c_2065]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_3889,plain,
% 51.28/7.00      ( ~ v1_funct_2(X0_58,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 51.28/7.00      | ~ m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 51.28/7.00      | m1_subset_1(sK1(sK3,sK4,X0_58),k1_zfmisc_1(u1_struct_0(sK3)))
% 51.28/7.00      | ~ v1_funct_1(X0_58)
% 51.28/7.00      | k9_tmap_1(sK3,sK4) = X0_58 ),
% 51.28/7.00      inference(subtyping,[status(esa)],[c_2066]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_4972,plain,
% 51.28/7.00      ( k9_tmap_1(sK3,sK4) = X0_58
% 51.28/7.00      | v1_funct_2(X0_58,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
% 51.28/7.00      | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) != iProver_top
% 51.28/7.00      | m1_subset_1(sK1(sK3,sK4,X0_58),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 51.28/7.00      | v1_funct_1(X0_58) != iProver_top ),
% 51.28/7.00      inference(predicate_to_equality,[status(thm)],[c_3889]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_21423,plain,
% 51.28/7.00      ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
% 51.28/7.00      | v1_funct_2(k6_partfun1(u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
% 51.28/7.00      | m1_subset_1(sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 51.28/7.00      | v1_funct_1(k6_partfun1(u1_struct_0(sK3))) != iProver_top ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_21420,c_4972]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_22,plain,
% 51.28/7.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 51.28/7.00      | ~ v2_pre_topc(X1)
% 51.28/7.00      | v1_funct_1(k7_tmap_1(X1,X0))
% 51.28/7.00      | v2_struct_0(X1)
% 51.28/7.00      | ~ l1_pre_topc(X1) ),
% 51.28/7.00      inference(cnf_transformation,[],[f88]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_3924,plain,
% 51.28/7.00      ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_57)))
% 51.28/7.00      | ~ v2_pre_topc(X0_57)
% 51.28/7.00      | v1_funct_1(k7_tmap_1(X0_57,X0_58))
% 51.28/7.00      | v2_struct_0(X0_57)
% 51.28/7.00      | ~ l1_pre_topc(X0_57) ),
% 51.28/7.00      inference(subtyping,[status(esa)],[c_22]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_4937,plain,
% 51.28/7.00      ( m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_57))) != iProver_top
% 51.28/7.00      | v2_pre_topc(X0_57) != iProver_top
% 51.28/7.00      | v1_funct_1(k7_tmap_1(X0_57,X0_58)) = iProver_top
% 51.28/7.00      | v2_struct_0(X0_57) = iProver_top
% 51.28/7.00      | l1_pre_topc(X0_57) != iProver_top ),
% 51.28/7.00      inference(predicate_to_equality,[status(thm)],[c_3924]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_5878,plain,
% 51.28/7.00      ( v2_pre_topc(sK3) != iProver_top
% 51.28/7.00      | v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4))) = iProver_top
% 51.28/7.00      | v2_struct_0(sK3) = iProver_top
% 51.28/7.00      | l1_pre_topc(sK3) != iProver_top ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_4955,c_4937]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_5622,plain,
% 51.28/7.00      ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 51.28/7.00      | ~ v2_pre_topc(sK3)
% 51.28/7.00      | v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4)))
% 51.28/7.00      | v2_struct_0(sK3)
% 51.28/7.00      | ~ l1_pre_topc(sK3) ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_3924]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_5623,plain,
% 51.28/7.00      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 51.28/7.00      | v2_pre_topc(sK3) != iProver_top
% 51.28/7.00      | v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4))) = iProver_top
% 51.28/7.00      | v2_struct_0(sK3) = iProver_top
% 51.28/7.00      | l1_pre_topc(sK3) != iProver_top ),
% 51.28/7.00      inference(predicate_to_equality,[status(thm)],[c_5622]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_7511,plain,
% 51.28/7.00      ( v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4))) = iProver_top ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_5878,c_51,c_52,c_53,c_1692,c_5623]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_7520,plain,
% 51.28/7.00      ( v1_funct_1(k6_partfun1(u1_struct_0(sK3))) = iProver_top ),
% 51.28/7.00      inference(demodulation,[status(thm)],[c_7517,c_7511]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_21,plain,
% 51.28/7.00      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
% 51.28/7.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 51.28/7.00      | ~ v2_pre_topc(X0)
% 51.28/7.00      | v2_struct_0(X0)
% 51.28/7.00      | ~ l1_pre_topc(X0) ),
% 51.28/7.00      inference(cnf_transformation,[],[f89]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_3925,plain,
% 51.28/7.00      ( v1_funct_2(k7_tmap_1(X0_57,X0_58),u1_struct_0(X0_57),u1_struct_0(k6_tmap_1(X0_57,X0_58)))
% 51.28/7.00      | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_57)))
% 51.28/7.00      | ~ v2_pre_topc(X0_57)
% 51.28/7.00      | v2_struct_0(X0_57)
% 51.28/7.00      | ~ l1_pre_topc(X0_57) ),
% 51.28/7.00      inference(subtyping,[status(esa)],[c_21]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_4936,plain,
% 51.28/7.00      ( v1_funct_2(k7_tmap_1(X0_57,X0_58),u1_struct_0(X0_57),u1_struct_0(k6_tmap_1(X0_57,X0_58))) = iProver_top
% 51.28/7.00      | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_57))) != iProver_top
% 51.28/7.00      | v2_pre_topc(X0_57) != iProver_top
% 51.28/7.00      | v2_struct_0(X0_57) = iProver_top
% 51.28/7.00      | l1_pre_topc(X0_57) != iProver_top ),
% 51.28/7.00      inference(predicate_to_equality,[status(thm)],[c_3925]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_8657,plain,
% 51.28/7.00      ( v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) = iProver_top
% 51.28/7.00      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 51.28/7.00      | v2_pre_topc(sK3) != iProver_top
% 51.28/7.00      | v2_struct_0(sK3) = iProver_top
% 51.28/7.00      | l1_pre_topc(sK3) != iProver_top ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_8631,c_4936]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_8663,plain,
% 51.28/7.00      ( v1_funct_2(k6_partfun1(u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) = iProver_top
% 51.28/7.00      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 51.28/7.00      | v2_pre_topc(sK3) != iProver_top
% 51.28/7.00      | v2_struct_0(sK3) = iProver_top
% 51.28/7.00      | l1_pre_topc(sK3) != iProver_top ),
% 51.28/7.00      inference(light_normalisation,[status(thm)],[c_8657,c_7517]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_29944,plain,
% 51.28/7.00      ( m1_subset_1(sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 51.28/7.00      | k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3)) ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_21423,c_51,c_52,c_53,c_1692,c_7520,c_8663]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_29945,plain,
% 51.28/7.00      ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
% 51.28/7.00      | m1_subset_1(sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 51.28/7.00      inference(renaming,[status(thm)],[c_29944]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_30,plain,
% 51.28/7.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 51.28/7.00      | ~ v2_pre_topc(X1)
% 51.28/7.00      | v2_struct_0(X1)
% 51.28/7.00      | ~ l1_pre_topc(X1)
% 51.28/7.00      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
% 51.28/7.00      inference(cnf_transformation,[],[f97]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_3921,plain,
% 51.28/7.00      ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_57)))
% 51.28/7.00      | ~ v2_pre_topc(X0_57)
% 51.28/7.00      | v2_struct_0(X0_57)
% 51.28/7.00      | ~ l1_pre_topc(X0_57)
% 51.28/7.00      | u1_struct_0(k6_tmap_1(X0_57,X0_58)) = u1_struct_0(X0_57) ),
% 51.28/7.00      inference(subtyping,[status(esa)],[c_30]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_4940,plain,
% 51.28/7.00      ( u1_struct_0(k6_tmap_1(X0_57,X0_58)) = u1_struct_0(X0_57)
% 51.28/7.00      | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_57))) != iProver_top
% 51.28/7.00      | v2_pre_topc(X0_57) != iProver_top
% 51.28/7.00      | v2_struct_0(X0_57) = iProver_top
% 51.28/7.00      | l1_pre_topc(X0_57) != iProver_top ),
% 51.28/7.00      inference(predicate_to_equality,[status(thm)],[c_3921]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_29957,plain,
% 51.28/7.00      ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
% 51.28/7.00      | u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))) = u1_struct_0(sK3)
% 51.28/7.00      | v2_pre_topc(sK3) != iProver_top
% 51.28/7.00      | v2_struct_0(sK3) = iProver_top
% 51.28/7.00      | l1_pre_topc(sK3) != iProver_top ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_29945,c_4940]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_30067,plain,
% 51.28/7.00      ( ~ v2_pre_topc(sK3)
% 51.28/7.00      | v2_struct_0(sK3)
% 51.28/7.00      | ~ l1_pre_topc(sK3)
% 51.28/7.00      | k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
% 51.28/7.00      | u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))) = u1_struct_0(sK3) ),
% 51.28/7.00      inference(predicate_to_equality_rev,[status(thm)],[c_29957]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_33106,plain,
% 51.28/7.00      ( u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))) = u1_struct_0(sK3)
% 51.28/7.00      | k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3)) ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_29957,c_50,c_49,c_48,c_30067]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_33107,plain,
% 51.28/7.00      ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
% 51.28/7.00      | u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))) = u1_struct_0(sK3) ),
% 51.28/7.00      inference(renaming,[status(thm)],[c_33106]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_33134,plain,
% 51.28/7.00      ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
% 51.28/7.00      | u1_struct_0(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),X0_58)) = u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))))
% 51.28/7.00      | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 51.28/7.00      | v2_pre_topc(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))) != iProver_top
% 51.28/7.00      | v2_struct_0(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))) = iProver_top
% 51.28/7.00      | l1_pre_topc(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))) != iProver_top ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_33107,c_4940]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_4933,plain,
% 51.28/7.00      ( m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_57))) != iProver_top
% 51.28/7.00      | v2_pre_topc(X0_57) != iProver_top
% 51.28/7.00      | v2_pre_topc(k6_tmap_1(X0_57,X0_58)) = iProver_top
% 51.28/7.00      | v2_struct_0(X0_57) = iProver_top
% 51.28/7.00      | l1_pre_topc(X0_57) != iProver_top ),
% 51.28/7.00      inference(predicate_to_equality,[status(thm)],[c_3928]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_29962,plain,
% 51.28/7.00      ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
% 51.28/7.00      | v2_pre_topc(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))) = iProver_top
% 51.28/7.00      | v2_pre_topc(sK3) != iProver_top
% 51.28/7.00      | v2_struct_0(sK3) = iProver_top
% 51.28/7.00      | l1_pre_topc(sK3) != iProver_top ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_29945,c_4933]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_31581,plain,
% 51.28/7.00      ( v2_pre_topc(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))) = iProver_top
% 51.28/7.00      | k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3)) ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_29962,c_51,c_52,c_53]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_31582,plain,
% 51.28/7.00      ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
% 51.28/7.00      | v2_pre_topc(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))) = iProver_top ),
% 51.28/7.00      inference(renaming,[status(thm)],[c_31581]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_4932,plain,
% 51.28/7.00      ( m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_57))) != iProver_top
% 51.28/7.00      | v2_pre_topc(X0_57) != iProver_top
% 51.28/7.00      | v2_struct_0(X0_57) = iProver_top
% 51.28/7.00      | l1_pre_topc(X0_57) != iProver_top
% 51.28/7.00      | l1_pre_topc(k6_tmap_1(X0_57,X0_58)) = iProver_top ),
% 51.28/7.00      inference(predicate_to_equality,[status(thm)],[c_3929]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_29963,plain,
% 51.28/7.00      ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
% 51.28/7.00      | v2_pre_topc(sK3) != iProver_top
% 51.28/7.00      | v2_struct_0(sK3) = iProver_top
% 51.28/7.00      | l1_pre_topc(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))) = iProver_top
% 51.28/7.00      | l1_pre_topc(sK3) != iProver_top ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_29945,c_4932]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_31686,plain,
% 51.28/7.00      ( l1_pre_topc(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))) = iProver_top
% 51.28/7.00      | k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3)) ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_29963,c_51,c_52,c_53]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_31687,plain,
% 51.28/7.00      ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
% 51.28/7.00      | l1_pre_topc(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))) = iProver_top ),
% 51.28/7.00      inference(renaming,[status(thm)],[c_31686]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_28,plain,
% 51.28/7.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 51.28/7.00      | ~ v2_pre_topc(X1)
% 51.28/7.00      | v2_struct_0(X1)
% 51.28/7.00      | ~ v2_struct_0(k6_tmap_1(X1,X0))
% 51.28/7.00      | ~ l1_pre_topc(X1) ),
% 51.28/7.00      inference(cnf_transformation,[],[f94]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_3923,plain,
% 51.28/7.00      ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_57)))
% 51.28/7.00      | ~ v2_pre_topc(X0_57)
% 51.28/7.00      | v2_struct_0(X0_57)
% 51.28/7.00      | ~ v2_struct_0(k6_tmap_1(X0_57,X0_58))
% 51.28/7.00      | ~ l1_pre_topc(X0_57) ),
% 51.28/7.00      inference(subtyping,[status(esa)],[c_28]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_4938,plain,
% 51.28/7.00      ( m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(X0_57))) != iProver_top
% 51.28/7.00      | v2_pre_topc(X0_57) != iProver_top
% 51.28/7.00      | v2_struct_0(X0_57) = iProver_top
% 51.28/7.00      | v2_struct_0(k6_tmap_1(X0_57,X0_58)) != iProver_top
% 51.28/7.00      | l1_pre_topc(X0_57) != iProver_top ),
% 51.28/7.00      inference(predicate_to_equality,[status(thm)],[c_3923]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_29958,plain,
% 51.28/7.00      ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
% 51.28/7.00      | v2_pre_topc(sK3) != iProver_top
% 51.28/7.00      | v2_struct_0(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))) != iProver_top
% 51.28/7.00      | v2_struct_0(sK3) = iProver_top
% 51.28/7.00      | l1_pre_topc(sK3) != iProver_top ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_29945,c_4938]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_33791,plain,
% 51.28/7.00      ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
% 51.28/7.00      | v2_struct_0(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))) != iProver_top ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_29958,c_51,c_52,c_53]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_103302,plain,
% 51.28/7.00      ( m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 51.28/7.00      | u1_struct_0(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),X0_58)) = u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))))
% 51.28/7.00      | k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3)) ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_33134,c_31582,c_31687,c_33791]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_103303,plain,
% 51.28/7.00      ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
% 51.28/7.00      | u1_struct_0(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),X0_58)) = u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))))
% 51.28/7.00      | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 51.28/7.00      inference(renaming,[status(thm)],[c_103302]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_103313,plain,
% 51.28/7.00      ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
% 51.28/7.00      | u1_struct_0(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),u1_struct_0(sK4))) = u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))) ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_4955,c_103303]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_104013,plain,
% 51.28/7.00      ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
% 51.28/7.00      | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))))) != iProver_top
% 51.28/7.00      | v2_pre_topc(k6_tmap_1(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),u1_struct_0(sK4)),X0_58)) = iProver_top
% 51.28/7.00      | v2_pre_topc(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),u1_struct_0(sK4))) != iProver_top
% 51.28/7.00      | v2_struct_0(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),u1_struct_0(sK4))) = iProver_top
% 51.28/7.00      | l1_pre_topc(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),u1_struct_0(sK4))) != iProver_top ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_103313,c_4933]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_104012,plain,
% 51.28/7.00      ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
% 51.28/7.00      | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))))) != iProver_top
% 51.28/7.00      | v1_pre_topc(k6_tmap_1(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),u1_struct_0(sK4)),X0_58)) = iProver_top
% 51.28/7.00      | v2_pre_topc(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),u1_struct_0(sK4))) != iProver_top
% 51.28/7.00      | v2_struct_0(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),u1_struct_0(sK4))) = iProver_top
% 51.28/7.00      | l1_pre_topc(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),u1_struct_0(sK4))) != iProver_top ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_103313,c_4934]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_33140,plain,
% 51.28/7.00      ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
% 51.28/7.00      | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 51.28/7.00      | v2_pre_topc(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))) != iProver_top
% 51.28/7.00      | v2_struct_0(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))) = iProver_top
% 51.28/7.00      | l1_pre_topc(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),X0_58)) = iProver_top
% 51.28/7.00      | l1_pre_topc(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))) != iProver_top ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_33107,c_4932]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_89121,plain,
% 51.28/7.00      ( l1_pre_topc(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),X0_58)) = iProver_top
% 51.28/7.00      | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 51.28/7.00      | k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3)) ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_33140,c_51,c_52,c_53,c_29958,c_31582,c_31687]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_89122,plain,
% 51.28/7.00      ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
% 51.28/7.00      | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 51.28/7.00      | l1_pre_topc(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),X0_58)) = iProver_top ),
% 51.28/7.00      inference(renaming,[status(thm)],[c_89121]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_104011,plain,
% 51.28/7.00      ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
% 51.28/7.00      | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))))) != iProver_top
% 51.28/7.00      | v2_pre_topc(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),u1_struct_0(sK4))) != iProver_top
% 51.28/7.00      | v1_funct_1(k7_tmap_1(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),u1_struct_0(sK4)),X0_58)) = iProver_top
% 51.28/7.00      | v2_struct_0(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),u1_struct_0(sK4))) = iProver_top
% 51.28/7.00      | l1_pre_topc(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),u1_struct_0(sK4))) != iProver_top ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_103313,c_4937]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_5749,plain,
% 51.28/7.00      ( v2_pre_topc(sK3) != iProver_top
% 51.28/7.00      | v2_struct_0(sK3) = iProver_top
% 51.28/7.00      | l1_pre_topc(k6_tmap_1(sK3,u1_struct_0(sK4))) = iProver_top
% 51.28/7.00      | l1_pre_topc(sK3) != iProver_top ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_4955,c_4932]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_7187,plain,
% 51.28/7.00      ( l1_pre_topc(k6_tmap_1(sK3,u1_struct_0(sK4))) = iProver_top ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_5749,c_51,c_52,c_53,c_1692,c_5686]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_8638,plain,
% 51.28/7.00      ( l1_pre_topc(k8_tmap_1(sK3,sK4)) = iProver_top ),
% 51.28/7.00      inference(demodulation,[status(thm)],[c_8631,c_7187]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_6561,plain,
% 51.28/7.00      ( v2_pre_topc(sK3) != iProver_top
% 51.28/7.00      | v2_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))) != iProver_top
% 51.28/7.00      | v2_struct_0(sK3) = iProver_top
% 51.28/7.00      | l1_pre_topc(sK3) != iProver_top ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_4955,c_4938]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_7077,plain,
% 51.28/7.00      ( v2_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))) != iProver_top ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_6561,c_51,c_52,c_53]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_8639,plain,
% 51.28/7.00      ( v2_struct_0(k8_tmap_1(sK3,sK4)) != iProver_top ),
% 51.28/7.00      inference(demodulation,[status(thm)],[c_8631,c_7077]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_8656,plain,
% 51.28/7.00      ( m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) = iProver_top
% 51.28/7.00      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 51.28/7.00      | v2_pre_topc(sK3) != iProver_top
% 51.28/7.00      | v2_struct_0(sK3) = iProver_top
% 51.28/7.00      | l1_pre_topc(sK3) != iProver_top ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_8631,c_4935]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_8674,plain,
% 51.28/7.00      ( m1_subset_1(k6_partfun1(u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) = iProver_top
% 51.28/7.00      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 51.28/7.00      | v2_pre_topc(sK3) != iProver_top
% 51.28/7.00      | v2_struct_0(sK3) = iProver_top
% 51.28/7.00      | l1_pre_topc(sK3) != iProver_top ),
% 51.28/7.00      inference(light_normalisation,[status(thm)],[c_8656,c_7517]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_0,plain,
% 51.28/7.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 51.28/7.00      inference(cnf_transformation,[],[f68]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1,plain,
% 51.28/7.00      ( v2_struct_0(X0)
% 51.28/7.00      | ~ v1_xboole_0(u1_struct_0(X0))
% 51.28/7.00      | ~ l1_struct_0(X0) ),
% 51.28/7.00      inference(cnf_transformation,[],[f69]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_580,plain,
% 51.28/7.00      ( v2_struct_0(X0)
% 51.28/7.00      | ~ v1_xboole_0(u1_struct_0(X0))
% 51.28/7.00      | ~ l1_pre_topc(X0) ),
% 51.28/7.00      inference(resolution,[status(thm)],[c_0,c_1]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_3917,plain,
% 51.28/7.00      ( v2_struct_0(X0_57)
% 51.28/7.00      | ~ v1_xboole_0(u1_struct_0(X0_57))
% 51.28/7.00      | ~ l1_pre_topc(X0_57) ),
% 51.28/7.00      inference(subtyping,[status(esa)],[c_580]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_11053,plain,
% 51.28/7.00      ( v2_struct_0(k8_tmap_1(sK3,sK4))
% 51.28/7.00      | ~ v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4)))
% 51.28/7.00      | ~ l1_pre_topc(k8_tmap_1(sK3,sK4)) ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_3917]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_11054,plain,
% 51.28/7.00      ( v2_struct_0(k8_tmap_1(sK3,sK4)) = iProver_top
% 51.28/7.00      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
% 51.28/7.00      | l1_pre_topc(k8_tmap_1(sK3,sK4)) != iProver_top ),
% 51.28/7.00      inference(predicate_to_equality,[status(thm)],[c_11053]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_3,plain,
% 51.28/7.00      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
% 51.28/7.00      | ~ v1_funct_2(X5,X2,X3)
% 51.28/7.00      | ~ v1_funct_2(X4,X0,X1)
% 51.28/7.00      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 51.28/7.00      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 51.28/7.00      | ~ v1_funct_1(X5)
% 51.28/7.00      | ~ v1_funct_1(X4)
% 51.28/7.00      | v1_xboole_0(X1)
% 51.28/7.00      | v1_xboole_0(X3) ),
% 51.28/7.00      inference(cnf_transformation,[],[f71]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_3931,plain,
% 51.28/7.00      ( r1_funct_2(X0_58,X1_58,X2_58,X3_58,X4_58,X4_58)
% 51.28/7.00      | ~ v1_funct_2(X5_58,X2_58,X3_58)
% 51.28/7.00      | ~ v1_funct_2(X4_58,X0_58,X1_58)
% 51.28/7.00      | ~ m1_subset_1(X5_58,k1_zfmisc_1(k2_zfmisc_1(X2_58,X3_58)))
% 51.28/7.00      | ~ m1_subset_1(X4_58,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58)))
% 51.28/7.00      | ~ v1_funct_1(X5_58)
% 51.28/7.00      | ~ v1_funct_1(X4_58)
% 51.28/7.00      | v1_xboole_0(X1_58)
% 51.28/7.00      | v1_xboole_0(X3_58) ),
% 51.28/7.00      inference(subtyping,[status(esa)],[c_3]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_4930,plain,
% 51.28/7.00      ( r1_funct_2(X0_58,X1_58,X2_58,X3_58,X4_58,X4_58) = iProver_top
% 51.28/7.00      | v1_funct_2(X5_58,X2_58,X3_58) != iProver_top
% 51.28/7.00      | v1_funct_2(X4_58,X0_58,X1_58) != iProver_top
% 51.28/7.00      | m1_subset_1(X5_58,k1_zfmisc_1(k2_zfmisc_1(X2_58,X3_58))) != iProver_top
% 51.28/7.00      | m1_subset_1(X4_58,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58))) != iProver_top
% 51.28/7.00      | v1_funct_1(X5_58) != iProver_top
% 51.28/7.00      | v1_funct_1(X4_58) != iProver_top
% 51.28/7.00      | v1_xboole_0(X1_58) = iProver_top
% 51.28/7.00      | v1_xboole_0(X3_58) = iProver_top ),
% 51.28/7.00      inference(predicate_to_equality,[status(thm)],[c_3931]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_7328,plain,
% 51.28/7.00      ( r1_funct_2(X0_58,X1_58,u1_struct_0(X0_57),u1_struct_0(k6_tmap_1(X0_57,X2_58)),X3_58,X3_58) = iProver_top
% 51.28/7.00      | v1_funct_2(X3_58,X0_58,X1_58) != iProver_top
% 51.28/7.00      | v1_funct_2(k7_tmap_1(X0_57,X2_58),u1_struct_0(X0_57),u1_struct_0(k6_tmap_1(X0_57,X2_58))) != iProver_top
% 51.28/7.00      | m1_subset_1(X3_58,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58))) != iProver_top
% 51.28/7.00      | m1_subset_1(X2_58,k1_zfmisc_1(u1_struct_0(X0_57))) != iProver_top
% 51.28/7.00      | v2_pre_topc(X0_57) != iProver_top
% 51.28/7.00      | v1_funct_1(X3_58) != iProver_top
% 51.28/7.00      | v1_funct_1(k7_tmap_1(X0_57,X2_58)) != iProver_top
% 51.28/7.00      | v2_struct_0(X0_57) = iProver_top
% 51.28/7.00      | v1_xboole_0(X1_58) = iProver_top
% 51.28/7.00      | v1_xboole_0(u1_struct_0(k6_tmap_1(X0_57,X2_58))) = iProver_top
% 51.28/7.00      | l1_pre_topc(X0_57) != iProver_top ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_4935,c_4930]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_36697,plain,
% 51.28/7.00      ( r1_funct_2(X0_58,X1_58,u1_struct_0(X0_57),u1_struct_0(k6_tmap_1(X0_57,X2_58)),X3_58,X3_58) = iProver_top
% 51.28/7.00      | v1_funct_2(X3_58,X0_58,X1_58) != iProver_top
% 51.28/7.00      | m1_subset_1(X3_58,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58))) != iProver_top
% 51.28/7.00      | m1_subset_1(X2_58,k1_zfmisc_1(u1_struct_0(X0_57))) != iProver_top
% 51.28/7.00      | v2_pre_topc(X0_57) != iProver_top
% 51.28/7.00      | v1_funct_1(X3_58) != iProver_top
% 51.28/7.00      | v2_struct_0(X0_57) = iProver_top
% 51.28/7.00      | v1_xboole_0(X1_58) = iProver_top
% 51.28/7.00      | v1_xboole_0(u1_struct_0(k6_tmap_1(X0_57,X2_58))) = iProver_top
% 51.28/7.00      | l1_pre_topc(X0_57) != iProver_top ),
% 51.28/7.00      inference(forward_subsumption_resolution,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_7328,c_4937,c_4936]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_29959,plain,
% 51.28/7.00      ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
% 51.28/7.00      | k7_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))) = k6_partfun1(u1_struct_0(sK3))
% 51.28/7.00      | v2_pre_topc(sK3) != iProver_top
% 51.28/7.00      | v2_struct_0(sK3) = iProver_top
% 51.28/7.00      | l1_pre_topc(sK3) != iProver_top ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_29945,c_4931]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_30069,plain,
% 51.28/7.00      ( ~ v2_pre_topc(sK3)
% 51.28/7.00      | v2_struct_0(sK3)
% 51.28/7.00      | ~ l1_pre_topc(sK3)
% 51.28/7.00      | k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
% 51.28/7.00      | k7_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))) = k6_partfun1(u1_struct_0(sK3)) ),
% 51.28/7.00      inference(predicate_to_equality_rev,[status(thm)],[c_29959]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_33800,plain,
% 51.28/7.00      ( k7_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))) = k6_partfun1(u1_struct_0(sK3))
% 51.28/7.00      | k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3)) ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_29959,c_50,c_49,c_48,c_30069]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_33801,plain,
% 51.28/7.00      ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
% 51.28/7.00      | k7_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))) = k6_partfun1(u1_struct_0(sK3)) ),
% 51.28/7.00      inference(renaming,[status(thm)],[c_33800]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_9,plain,
% 51.28/7.00      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2)))
% 51.28/7.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 51.28/7.00      | ~ m1_pre_topc(X1,X0)
% 51.28/7.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 51.28/7.00      | ~ v2_pre_topc(X0)
% 51.28/7.00      | ~ v1_funct_1(X2)
% 51.28/7.00      | v2_struct_0(X0)
% 51.28/7.00      | ~ l1_pre_topc(X0)
% 51.28/7.00      | k9_tmap_1(X0,X1) = X2 ),
% 51.28/7.00      inference(cnf_transformation,[],[f80]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1973,plain,
% 51.28/7.00      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2)))
% 51.28/7.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 51.28/7.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 51.28/7.00      | ~ v2_pre_topc(X0)
% 51.28/7.00      | ~ v1_funct_1(X2)
% 51.28/7.00      | v2_struct_0(X0)
% 51.28/7.00      | ~ l1_pre_topc(X0)
% 51.28/7.00      | k9_tmap_1(X0,X1) = X2
% 51.28/7.00      | sK4 != X1
% 51.28/7.00      | sK3 != X0 ),
% 51.28/7.00      inference(resolution_lifted,[status(thm)],[c_9,c_298]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1974,plain,
% 51.28/7.00      ( ~ r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK4,X0))),X0,k7_tmap_1(sK3,sK1(sK3,sK4,X0)))
% 51.28/7.00      | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 51.28/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 51.28/7.00      | ~ v2_pre_topc(sK3)
% 51.28/7.00      | ~ v1_funct_1(X0)
% 51.28/7.00      | v2_struct_0(sK3)
% 51.28/7.00      | ~ l1_pre_topc(sK3)
% 51.28/7.00      | k9_tmap_1(sK3,sK4) = X0 ),
% 51.28/7.00      inference(unflattening,[status(thm)],[c_1973]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1978,plain,
% 51.28/7.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 51.28/7.00      | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 51.28/7.00      | ~ r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK4,X0))),X0,k7_tmap_1(sK3,sK1(sK3,sK4,X0)))
% 51.28/7.00      | ~ v1_funct_1(X0)
% 51.28/7.00      | k9_tmap_1(sK3,sK4) = X0 ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_1974,c_50,c_49,c_48]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1979,plain,
% 51.28/7.00      ( ~ r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK4,X0))),X0,k7_tmap_1(sK3,sK1(sK3,sK4,X0)))
% 51.28/7.00      | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 51.28/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 51.28/7.00      | ~ v1_funct_1(X0)
% 51.28/7.00      | k9_tmap_1(sK3,sK4) = X0 ),
% 51.28/7.00      inference(renaming,[status(thm)],[c_1978]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_3892,plain,
% 51.28/7.00      ( ~ r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK4,X0_58))),X0_58,k7_tmap_1(sK3,sK1(sK3,sK4,X0_58)))
% 51.28/7.00      | ~ v1_funct_2(X0_58,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 51.28/7.00      | ~ m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 51.28/7.00      | ~ v1_funct_1(X0_58)
% 51.28/7.00      | k9_tmap_1(sK3,sK4) = X0_58 ),
% 51.28/7.00      inference(subtyping,[status(esa)],[c_1979]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_4969,plain,
% 51.28/7.00      ( k9_tmap_1(sK3,sK4) = X0_58
% 51.28/7.00      | r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK4,X0_58))),X0_58,k7_tmap_1(sK3,sK1(sK3,sK4,X0_58))) != iProver_top
% 51.28/7.00      | v1_funct_2(X0_58,u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
% 51.28/7.00      | m1_subset_1(X0_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) != iProver_top
% 51.28/7.00      | v1_funct_1(X0_58) != iProver_top ),
% 51.28/7.00      inference(predicate_to_equality,[status(thm)],[c_3892]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_33805,plain,
% 51.28/7.00      ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
% 51.28/7.00      | r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))),k6_partfun1(u1_struct_0(sK3)),k6_partfun1(u1_struct_0(sK3))) != iProver_top
% 51.28/7.00      | v1_funct_2(k6_partfun1(u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
% 51.28/7.00      | m1_subset_1(k6_partfun1(u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) != iProver_top
% 51.28/7.00      | v1_funct_1(k6_partfun1(u1_struct_0(sK3))) != iProver_top ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_33801,c_4969]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_34380,plain,
% 51.28/7.00      ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))),k6_partfun1(u1_struct_0(sK3)),k6_partfun1(u1_struct_0(sK3))) != iProver_top
% 51.28/7.00      | k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3)) ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_33805,c_51,c_52,c_53,c_1692,c_7520,c_8663,c_8674]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_34381,plain,
% 51.28/7.00      ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
% 51.28/7.00      | r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))),k6_partfun1(u1_struct_0(sK3)),k6_partfun1(u1_struct_0(sK3))) != iProver_top ),
% 51.28/7.00      inference(renaming,[status(thm)],[c_34380]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_36712,plain,
% 51.28/7.00      ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
% 51.28/7.00      | v1_funct_2(k6_partfun1(u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
% 51.28/7.00      | m1_subset_1(sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 51.28/7.00      | m1_subset_1(k6_partfun1(u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) != iProver_top
% 51.28/7.00      | v2_pre_topc(sK3) != iProver_top
% 51.28/7.00      | v1_funct_1(k6_partfun1(u1_struct_0(sK3))) != iProver_top
% 51.28/7.00      | v2_struct_0(sK3) = iProver_top
% 51.28/7.00      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))))) = iProver_top
% 51.28/7.00      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4))) = iProver_top
% 51.28/7.00      | l1_pre_topc(sK3) != iProver_top ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_36697,c_34381]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_4944,plain,
% 51.28/7.00      ( v2_struct_0(X0_57) = iProver_top
% 51.28/7.00      | v1_xboole_0(u1_struct_0(X0_57)) != iProver_top
% 51.28/7.00      | l1_pre_topc(X0_57) != iProver_top ),
% 51.28/7.00      inference(predicate_to_equality,[status(thm)],[c_3917]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_104004,plain,
% 51.28/7.00      ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
% 51.28/7.00      | v2_struct_0(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),u1_struct_0(sK4))) = iProver_top
% 51.28/7.00      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))))) != iProver_top
% 51.28/7.00      | l1_pre_topc(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),u1_struct_0(sK4))) != iProver_top ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_103313,c_4944]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_161511,plain,
% 51.28/7.00      ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
% 51.28/7.00      | v2_struct_0(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),u1_struct_0(sK4))) = iProver_top
% 51.28/7.00      | l1_pre_topc(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),u1_struct_0(sK4))) != iProver_top ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_104011,c_51,c_52,c_53,c_1692,c_7520,c_8638,c_8639,
% 51.28/7.00                 c_8663,c_8674,c_11054,c_21423,c_36712,c_104004]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_161518,plain,
% 51.28/7.00      ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
% 51.28/7.00      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 51.28/7.00      | v2_struct_0(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),u1_struct_0(sK4))) = iProver_top ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_89122,c_161511]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_161536,plain,
% 51.28/7.00      ( v2_struct_0(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),u1_struct_0(sK4))) = iProver_top
% 51.28/7.00      | k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3)) ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_104012,c_53,c_1692,c_161518]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_161537,plain,
% 51.28/7.00      ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
% 51.28/7.00      | v2_struct_0(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),u1_struct_0(sK4))) = iProver_top ),
% 51.28/7.00      inference(renaming,[status(thm)],[c_161536]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_33135,plain,
% 51.28/7.00      ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
% 51.28/7.00      | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 51.28/7.00      | v2_pre_topc(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))) != iProver_top
% 51.28/7.00      | v2_struct_0(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),X0_58)) != iProver_top
% 51.28/7.00      | v2_struct_0(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))) = iProver_top
% 51.28/7.00      | l1_pre_topc(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3))))) != iProver_top ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_33107,c_4938]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_93909,plain,
% 51.28/7.00      ( m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 51.28/7.00      | k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
% 51.28/7.00      | v2_struct_0(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),X0_58)) != iProver_top ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_33135,c_51,c_52,c_53,c_29958,c_29962,c_29963]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_93910,plain,
% 51.28/7.00      ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
% 51.28/7.00      | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 51.28/7.00      | v2_struct_0(k6_tmap_1(k6_tmap_1(sK3,sK1(sK3,sK4,k6_partfun1(u1_struct_0(sK3)))),X0_58)) != iProver_top ),
% 51.28/7.00      inference(renaming,[status(thm)],[c_93909]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_161543,plain,
% 51.28/7.00      ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
% 51.28/7.00      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_161537,c_93910]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_161657,plain,
% 51.28/7.00      ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3)) ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_104013,c_53,c_1692,c_161543]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_24,plain,
% 51.28/7.00      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 51.28/7.00      | ~ m1_pre_topc(X1,X0)
% 51.28/7.00      | ~ v2_pre_topc(X0)
% 51.28/7.00      | v2_struct_0(X0)
% 51.28/7.00      | ~ l1_pre_topc(X0) ),
% 51.28/7.00      inference(cnf_transformation,[],[f92]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1948,plain,
% 51.28/7.00      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 51.28/7.00      | ~ v2_pre_topc(X0)
% 51.28/7.00      | v2_struct_0(X0)
% 51.28/7.00      | ~ l1_pre_topc(X0)
% 51.28/7.00      | sK4 != X1
% 51.28/7.00      | sK3 != X0 ),
% 51.28/7.00      inference(resolution_lifted,[status(thm)],[c_24,c_298]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1949,plain,
% 51.28/7.00      ( v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 51.28/7.00      | ~ v2_pre_topc(sK3)
% 51.28/7.00      | v2_struct_0(sK3)
% 51.28/7.00      | ~ l1_pre_topc(sK3) ),
% 51.28/7.00      inference(unflattening,[status(thm)],[c_1948]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1951,plain,
% 51.28/7.00      ( v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_1949,c_50,c_49,c_48]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_23,plain,
% 51.28/7.00      ( ~ m1_pre_topc(X0,X1)
% 51.28/7.00      | m1_subset_1(k9_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X0)))))
% 51.28/7.00      | ~ v2_pre_topc(X1)
% 51.28/7.00      | v2_struct_0(X1)
% 51.28/7.00      | ~ l1_pre_topc(X1) ),
% 51.28/7.00      inference(cnf_transformation,[],[f93]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1712,plain,
% 51.28/7.00      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 51.28/7.00      | ~ v2_pre_topc(X0)
% 51.28/7.00      | v2_struct_0(X0)
% 51.28/7.00      | ~ l1_pre_topc(X0)
% 51.28/7.00      | sK4 != X1
% 51.28/7.00      | sK3 != X0 ),
% 51.28/7.00      inference(resolution_lifted,[status(thm)],[c_23,c_298]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1713,plain,
% 51.28/7.00      ( m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 51.28/7.00      | ~ v2_pre_topc(sK3)
% 51.28/7.00      | v2_struct_0(sK3)
% 51.28/7.00      | ~ l1_pre_topc(sK3) ),
% 51.28/7.00      inference(unflattening,[status(thm)],[c_1712]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1715,plain,
% 51.28/7.00      ( m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_1713,c_50,c_49,c_48]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_25,plain,
% 51.28/7.00      ( ~ m1_pre_topc(X0,X1)
% 51.28/7.00      | ~ v2_pre_topc(X1)
% 51.28/7.00      | v1_funct_1(k9_tmap_1(X1,X0))
% 51.28/7.00      | v2_struct_0(X1)
% 51.28/7.00      | ~ l1_pre_topc(X1) ),
% 51.28/7.00      inference(cnf_transformation,[],[f91]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1701,plain,
% 51.28/7.00      ( ~ v2_pre_topc(X0)
% 51.28/7.00      | v1_funct_1(k9_tmap_1(X0,X1))
% 51.28/7.00      | v2_struct_0(X0)
% 51.28/7.00      | ~ l1_pre_topc(X0)
% 51.28/7.00      | sK4 != X1
% 51.28/7.00      | sK3 != X0 ),
% 51.28/7.00      inference(resolution_lifted,[status(thm)],[c_25,c_298]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1702,plain,
% 51.28/7.00      ( ~ v2_pre_topc(sK3)
% 51.28/7.00      | v1_funct_1(k9_tmap_1(sK3,sK4))
% 51.28/7.00      | v2_struct_0(sK3)
% 51.28/7.00      | ~ l1_pre_topc(sK3) ),
% 51.28/7.00      inference(unflattening,[status(thm)],[c_1701]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1704,plain,
% 51.28/7.00      ( v1_funct_1(k9_tmap_1(sK3,sK4)) ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_1702,c_50,c_49,c_48]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_33,plain,
% 51.28/7.00      ( v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
% 51.28/7.00      | ~ v3_pre_topc(X1,X0)
% 51.28/7.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 51.28/7.00      | ~ v2_pre_topc(X0)
% 51.28/7.00      | v2_struct_0(X0)
% 51.28/7.00      | ~ l1_pre_topc(X0) ),
% 51.28/7.00      inference(cnf_transformation,[],[f101]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_38,negated_conjecture,
% 51.28/7.00      ( ~ v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4))
% 51.28/7.00      | ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 51.28/7.00      | ~ v1_tsep_1(sK4,sK3)
% 51.28/7.00      | ~ m1_pre_topc(sK4,sK3)
% 51.28/7.00      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 51.28/7.00      | ~ v1_funct_1(k9_tmap_1(sK3,sK4)) ),
% 51.28/7.00      inference(cnf_transformation,[],[f118]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_303,plain,
% 51.28/7.00      ( ~ v1_tsep_1(sK4,sK3)
% 51.28/7.00      | ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 51.28/7.00      | ~ v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4))
% 51.28/7.00      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 51.28/7.00      | ~ v1_funct_1(k9_tmap_1(sK3,sK4)) ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_38,c_47]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_304,negated_conjecture,
% 51.28/7.00      ( ~ v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4))
% 51.28/7.00      | ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 51.28/7.00      | ~ v1_tsep_1(sK4,sK3)
% 51.28/7.00      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 51.28/7.00      | ~ v1_funct_1(k9_tmap_1(sK3,sK4)) ),
% 51.28/7.00      inference(renaming,[status(thm)],[c_303]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_708,plain,
% 51.28/7.00      ( ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 51.28/7.00      | ~ v3_pre_topc(X0,X1)
% 51.28/7.00      | ~ v1_tsep_1(sK4,sK3)
% 51.28/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 51.28/7.00      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 51.28/7.00      | ~ v2_pre_topc(X1)
% 51.28/7.00      | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
% 51.28/7.00      | v2_struct_0(X1)
% 51.28/7.00      | ~ l1_pre_topc(X1)
% 51.28/7.00      | k6_tmap_1(X1,X0) != k8_tmap_1(sK3,sK4)
% 51.28/7.00      | k7_tmap_1(X1,X0) != k9_tmap_1(sK3,sK4)
% 51.28/7.00      | sK3 != X1 ),
% 51.28/7.00      inference(resolution_lifted,[status(thm)],[c_33,c_304]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_709,plain,
% 51.28/7.00      ( ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 51.28/7.00      | ~ v3_pre_topc(X0,sK3)
% 51.28/7.00      | ~ v1_tsep_1(sK4,sK3)
% 51.28/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 51.28/7.00      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 51.28/7.00      | ~ v2_pre_topc(sK3)
% 51.28/7.00      | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
% 51.28/7.00      | v2_struct_0(sK3)
% 51.28/7.00      | ~ l1_pre_topc(sK3)
% 51.28/7.00      | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
% 51.28/7.00      | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4) ),
% 51.28/7.00      inference(unflattening,[status(thm)],[c_708]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_713,plain,
% 51.28/7.00      ( ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 51.28/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 51.28/7.00      | ~ v1_tsep_1(sK4,sK3)
% 51.28/7.00      | ~ v3_pre_topc(X0,sK3)
% 51.28/7.00      | ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 51.28/7.00      | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
% 51.28/7.00      | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
% 51.28/7.00      | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4) ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_709,c_50,c_49,c_48]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_714,plain,
% 51.28/7.00      ( ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 51.28/7.00      | ~ v3_pre_topc(X0,sK3)
% 51.28/7.00      | ~ v1_tsep_1(sK4,sK3)
% 51.28/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 51.28/7.00      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 51.28/7.00      | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
% 51.28/7.00      | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
% 51.28/7.00      | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4) ),
% 51.28/7.00      inference(renaming,[status(thm)],[c_713]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_2186,plain,
% 51.28/7.00      ( ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 51.28/7.00      | ~ v3_pre_topc(X0,sK3)
% 51.28/7.00      | ~ v1_tsep_1(sK4,sK3)
% 51.28/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 51.28/7.00      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 51.28/7.00      | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
% 51.28/7.00      | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4) ),
% 51.28/7.00      inference(backward_subsumption_resolution,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_1704,c_714]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_2192,plain,
% 51.28/7.00      ( ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 51.28/7.00      | ~ v3_pre_topc(X0,sK3)
% 51.28/7.00      | ~ v1_tsep_1(sK4,sK3)
% 51.28/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 51.28/7.00      | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
% 51.28/7.00      | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4) ),
% 51.28/7.00      inference(backward_subsumption_resolution,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_1715,c_2186]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_2250,plain,
% 51.28/7.00      ( ~ v3_pre_topc(X0,sK3)
% 51.28/7.00      | ~ v1_tsep_1(sK4,sK3)
% 51.28/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 51.28/7.00      | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
% 51.28/7.00      | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4) ),
% 51.28/7.00      inference(backward_subsumption_resolution,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_1951,c_2192]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_16,plain,
% 51.28/7.00      ( v3_pre_topc(u1_struct_0(X0),X1)
% 51.28/7.00      | ~ v1_tsep_1(X0,X1)
% 51.28/7.00      | ~ m1_pre_topc(X0,X1)
% 51.28/7.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 51.28/7.00      | ~ l1_pre_topc(X1) ),
% 51.28/7.00      inference(cnf_transformation,[],[f123]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_347,plain,
% 51.28/7.00      ( ~ m1_pre_topc(X0,X1)
% 51.28/7.00      | ~ v1_tsep_1(X0,X1)
% 51.28/7.00      | v3_pre_topc(u1_struct_0(X0),X1)
% 51.28/7.00      | ~ l1_pre_topc(X1) ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_16,c_36]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_348,plain,
% 51.28/7.00      ( v3_pre_topc(u1_struct_0(X0),X1)
% 51.28/7.00      | ~ v1_tsep_1(X0,X1)
% 51.28/7.00      | ~ m1_pre_topc(X0,X1)
% 51.28/7.00      | ~ l1_pre_topc(X1) ),
% 51.28/7.00      inference(renaming,[status(thm)],[c_347]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_37,plain,
% 51.28/7.00      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 51.28/7.00      inference(cnf_transformation,[],[f105]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1471,plain,
% 51.28/7.00      ( v3_pre_topc(u1_struct_0(X0),X1)
% 51.28/7.00      | ~ v1_tsep_1(X0,X1)
% 51.28/7.00      | ~ l1_pre_topc(X1)
% 51.28/7.00      | ~ l1_pre_topc(X2)
% 51.28/7.00      | X2 != X1
% 51.28/7.00      | X2 != X0 ),
% 51.28/7.00      inference(resolution_lifted,[status(thm)],[c_348,c_37]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1472,plain,
% 51.28/7.00      ( v3_pre_topc(u1_struct_0(X0),X0)
% 51.28/7.00      | ~ v1_tsep_1(X0,X0)
% 51.28/7.00      | ~ l1_pre_topc(X0) ),
% 51.28/7.00      inference(unflattening,[status(thm)],[c_1471]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_2334,plain,
% 51.28/7.00      ( ~ v1_tsep_1(X0,X0)
% 51.28/7.00      | ~ v1_tsep_1(sK4,sK3)
% 51.28/7.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 51.28/7.00      | ~ l1_pre_topc(X0)
% 51.28/7.00      | k6_tmap_1(sK3,X1) != k8_tmap_1(sK3,sK4)
% 51.28/7.00      | k7_tmap_1(sK3,X1) != k9_tmap_1(sK3,sK4)
% 51.28/7.00      | u1_struct_0(X0) != X1
% 51.28/7.00      | sK3 != X0 ),
% 51.28/7.00      inference(resolution_lifted,[status(thm)],[c_2250,c_1472]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_2335,plain,
% 51.28/7.00      ( ~ v1_tsep_1(sK4,sK3)
% 51.28/7.00      | ~ v1_tsep_1(sK3,sK3)
% 51.28/7.00      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 51.28/7.00      | ~ l1_pre_topc(sK3)
% 51.28/7.00      | k6_tmap_1(sK3,u1_struct_0(sK3)) != k8_tmap_1(sK3,sK4)
% 51.28/7.00      | k7_tmap_1(sK3,u1_struct_0(sK3)) != k9_tmap_1(sK3,sK4) ),
% 51.28/7.00      inference(unflattening,[status(thm)],[c_2334]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_65,plain,
% 51.28/7.00      ( m1_pre_topc(sK3,sK3) | ~ l1_pre_topc(sK3) ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_37]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_68,plain,
% 51.28/7.00      ( ~ m1_pre_topc(sK3,sK3)
% 51.28/7.00      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 51.28/7.00      | ~ l1_pre_topc(sK3) ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_36]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_853,plain,
% 51.28/7.00      ( ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 51.28/7.00      | ~ v1_tsep_1(X0,X1)
% 51.28/7.00      | ~ v1_tsep_1(sK4,sK3)
% 51.28/7.00      | ~ m1_pre_topc(X0,X1)
% 51.28/7.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 51.28/7.00      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 51.28/7.00      | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
% 51.28/7.00      | ~ l1_pre_topc(X1)
% 51.28/7.00      | k6_tmap_1(sK3,X2) != k8_tmap_1(sK3,sK4)
% 51.28/7.00      | k7_tmap_1(sK3,X2) != k9_tmap_1(sK3,sK4)
% 51.28/7.00      | u1_struct_0(X0) != X2
% 51.28/7.00      | sK3 != X1 ),
% 51.28/7.00      inference(resolution_lifted,[status(thm)],[c_348,c_714]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_854,plain,
% 51.28/7.00      ( ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 51.28/7.00      | ~ v1_tsep_1(X0,sK3)
% 51.28/7.00      | ~ v1_tsep_1(sK4,sK3)
% 51.28/7.00      | ~ m1_pre_topc(X0,sK3)
% 51.28/7.00      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 51.28/7.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 51.28/7.00      | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
% 51.28/7.00      | ~ l1_pre_topc(sK3)
% 51.28/7.00      | k6_tmap_1(sK3,u1_struct_0(X0)) != k8_tmap_1(sK3,sK4)
% 51.28/7.00      | k7_tmap_1(sK3,u1_struct_0(X0)) != k9_tmap_1(sK3,sK4) ),
% 51.28/7.00      inference(unflattening,[status(thm)],[c_853]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_856,plain,
% 51.28/7.00      ( ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 51.28/7.00      | ~ v1_tsep_1(sK4,sK3)
% 51.28/7.00      | ~ v1_tsep_1(sK3,sK3)
% 51.28/7.00      | ~ m1_pre_topc(sK3,sK3)
% 51.28/7.00      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 51.28/7.00      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 51.28/7.00      | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
% 51.28/7.00      | ~ l1_pre_topc(sK3)
% 51.28/7.00      | k6_tmap_1(sK3,u1_struct_0(sK3)) != k8_tmap_1(sK3,sK4)
% 51.28/7.00      | k7_tmap_1(sK3,u1_struct_0(sK3)) != k9_tmap_1(sK3,sK4) ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_854]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_2337,plain,
% 51.28/7.00      ( ~ v1_tsep_1(sK4,sK3)
% 51.28/7.00      | ~ v1_tsep_1(sK3,sK3)
% 51.28/7.00      | k6_tmap_1(sK3,u1_struct_0(sK3)) != k8_tmap_1(sK3,sK4)
% 51.28/7.00      | k7_tmap_1(sK3,u1_struct_0(sK3)) != k9_tmap_1(sK3,sK4) ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_2335,c_50,c_49,c_48,c_65,c_68,c_856,c_1702,c_1713,
% 51.28/7.00                 c_1949]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_3885,plain,
% 51.28/7.00      ( ~ v1_tsep_1(sK4,sK3)
% 51.28/7.00      | ~ v1_tsep_1(sK3,sK3)
% 51.28/7.00      | k7_tmap_1(sK3,u1_struct_0(sK3)) != k9_tmap_1(sK3,sK4)
% 51.28/7.00      | k6_tmap_1(sK3,u1_struct_0(sK3)) != k8_tmap_1(sK3,sK4) ),
% 51.28/7.00      inference(subtyping,[status(esa)],[c_2337]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_4976,plain,
% 51.28/7.00      ( k7_tmap_1(sK3,u1_struct_0(sK3)) != k9_tmap_1(sK3,sK4)
% 51.28/7.00      | k6_tmap_1(sK3,u1_struct_0(sK3)) != k8_tmap_1(sK3,sK4)
% 51.28/7.00      | v1_tsep_1(sK4,sK3) != iProver_top
% 51.28/7.00      | v1_tsep_1(sK3,sK3) != iProver_top ),
% 51.28/7.00      inference(predicate_to_equality,[status(thm)],[c_3885]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_3919,negated_conjecture,
% 51.28/7.00      ( v2_pre_topc(sK3) ),
% 51.28/7.00      inference(subtyping,[status(esa)],[c_49]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_4942,plain,
% 51.28/7.00      ( v2_pre_topc(sK3) = iProver_top ),
% 51.28/7.00      inference(predicate_to_equality,[status(thm)],[c_3919]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1486,plain,
% 51.28/7.00      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 51.28/7.00      | ~ l1_pre_topc(X1)
% 51.28/7.00      | ~ l1_pre_topc(X2)
% 51.28/7.00      | X2 != X1
% 51.28/7.00      | X2 != X0 ),
% 51.28/7.00      inference(resolution_lifted,[status(thm)],[c_36,c_37]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1487,plain,
% 51.28/7.00      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 51.28/7.00      | ~ l1_pre_topc(X0) ),
% 51.28/7.00      inference(unflattening,[status(thm)],[c_1486]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_3915,plain,
% 51.28/7.00      ( m1_subset_1(u1_struct_0(X0_57),k1_zfmisc_1(u1_struct_0(X0_57)))
% 51.28/7.00      | ~ l1_pre_topc(X0_57) ),
% 51.28/7.00      inference(subtyping,[status(esa)],[c_1487]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_4946,plain,
% 51.28/7.00      ( m1_subset_1(u1_struct_0(X0_57),k1_zfmisc_1(u1_struct_0(X0_57))) = iProver_top
% 51.28/7.00      | l1_pre_topc(X0_57) != iProver_top ),
% 51.28/7.00      inference(predicate_to_equality,[status(thm)],[c_3915]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_9045,plain,
% 51.28/7.00      ( k7_tmap_1(X0_57,u1_struct_0(X0_57)) = k6_partfun1(u1_struct_0(X0_57))
% 51.28/7.00      | v2_pre_topc(X0_57) != iProver_top
% 51.28/7.00      | v2_struct_0(X0_57) = iProver_top
% 51.28/7.00      | l1_pre_topc(X0_57) != iProver_top ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_4946,c_4931]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_10816,plain,
% 51.28/7.00      ( k7_tmap_1(sK3,u1_struct_0(sK3)) = k6_partfun1(u1_struct_0(sK3))
% 51.28/7.00      | v2_struct_0(sK3) = iProver_top
% 51.28/7.00      | l1_pre_topc(sK3) != iProver_top ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_4942,c_9045]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_5704,plain,
% 51.28/7.00      ( ~ m1_subset_1(u1_struct_0(X0_57),k1_zfmisc_1(u1_struct_0(X0_57)))
% 51.28/7.00      | ~ v2_pre_topc(X0_57)
% 51.28/7.00      | v2_struct_0(X0_57)
% 51.28/7.00      | ~ l1_pre_topc(X0_57)
% 51.28/7.00      | k7_tmap_1(X0_57,u1_struct_0(X0_57)) = k6_partfun1(u1_struct_0(X0_57)) ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_3930]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_5706,plain,
% 51.28/7.00      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 51.28/7.00      | ~ v2_pre_topc(sK3)
% 51.28/7.00      | v2_struct_0(sK3)
% 51.28/7.00      | ~ l1_pre_topc(sK3)
% 51.28/7.00      | k7_tmap_1(sK3,u1_struct_0(sK3)) = k6_partfun1(u1_struct_0(sK3)) ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_5704]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_10943,plain,
% 51.28/7.00      ( k7_tmap_1(sK3,u1_struct_0(sK3)) = k6_partfun1(u1_struct_0(sK3)) ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_10816,c_50,c_49,c_48,c_65,c_68,c_5706]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_9047,plain,
% 51.28/7.00      ( v1_pre_topc(k6_tmap_1(X0_57,u1_struct_0(X0_57))) = iProver_top
% 51.28/7.00      | v2_pre_topc(X0_57) != iProver_top
% 51.28/7.00      | v2_struct_0(X0_57) = iProver_top
% 51.28/7.00      | l1_pre_topc(X0_57) != iProver_top ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_4946,c_4934]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1594,plain,
% 51.28/7.00      ( ~ v1_pre_topc(X0)
% 51.28/7.00      | ~ v2_pre_topc(X1)
% 51.28/7.00      | ~ v2_pre_topc(X0)
% 51.28/7.00      | v2_struct_0(X1)
% 51.28/7.00      | ~ l1_pre_topc(X1)
% 51.28/7.00      | ~ l1_pre_topc(X0)
% 51.28/7.00      | ~ l1_pre_topc(X2)
% 51.28/7.00      | X2 != X1
% 51.28/7.00      | X2 != X3
% 51.28/7.00      | sK0(X1,X3,X0) = u1_struct_0(X3)
% 51.28/7.00      | k8_tmap_1(X1,X3) = X0 ),
% 51.28/7.00      inference(resolution_lifted,[status(thm)],[c_6,c_37]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1595,plain,
% 51.28/7.00      ( ~ v1_pre_topc(X0)
% 51.28/7.00      | ~ v2_pre_topc(X0)
% 51.28/7.00      | ~ v2_pre_topc(X1)
% 51.28/7.00      | v2_struct_0(X1)
% 51.28/7.00      | ~ l1_pre_topc(X0)
% 51.28/7.00      | ~ l1_pre_topc(X1)
% 51.28/7.00      | sK0(X1,X1,X0) = u1_struct_0(X1)
% 51.28/7.00      | k8_tmap_1(X1,X1) = X0 ),
% 51.28/7.00      inference(unflattening,[status(thm)],[c_1594]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_3909,plain,
% 51.28/7.00      ( ~ v1_pre_topc(X0_57)
% 51.28/7.00      | ~ v2_pre_topc(X1_57)
% 51.28/7.00      | ~ v2_pre_topc(X0_57)
% 51.28/7.00      | v2_struct_0(X1_57)
% 51.28/7.00      | ~ l1_pre_topc(X1_57)
% 51.28/7.00      | ~ l1_pre_topc(X0_57)
% 51.28/7.00      | sK0(X1_57,X1_57,X0_57) = u1_struct_0(X1_57)
% 51.28/7.00      | k8_tmap_1(X1_57,X1_57) = X0_57 ),
% 51.28/7.00      inference(subtyping,[status(esa)],[c_1595]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_4952,plain,
% 51.28/7.00      ( sK0(X0_57,X0_57,X1_57) = u1_struct_0(X0_57)
% 51.28/7.00      | k8_tmap_1(X0_57,X0_57) = X1_57
% 51.28/7.00      | v1_pre_topc(X1_57) != iProver_top
% 51.28/7.00      | v2_pre_topc(X0_57) != iProver_top
% 51.28/7.00      | v2_pre_topc(X1_57) != iProver_top
% 51.28/7.00      | v2_struct_0(X0_57) = iProver_top
% 51.28/7.00      | l1_pre_topc(X1_57) != iProver_top
% 51.28/7.00      | l1_pre_topc(X0_57) != iProver_top ),
% 51.28/7.00      inference(predicate_to_equality,[status(thm)],[c_3909]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_18176,plain,
% 51.28/7.00      ( sK0(sK3,sK3,X0_57) = u1_struct_0(sK3)
% 51.28/7.00      | k8_tmap_1(sK3,sK3) = X0_57
% 51.28/7.00      | v1_pre_topc(X0_57) != iProver_top
% 51.28/7.00      | v2_pre_topc(X0_57) != iProver_top
% 51.28/7.00      | v2_struct_0(sK3) = iProver_top
% 51.28/7.00      | l1_pre_topc(X0_57) != iProver_top
% 51.28/7.00      | l1_pre_topc(sK3) != iProver_top ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_4942,c_4952]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_18763,plain,
% 51.28/7.00      ( l1_pre_topc(X0_57) != iProver_top
% 51.28/7.00      | sK0(sK3,sK3,X0_57) = u1_struct_0(sK3)
% 51.28/7.00      | k8_tmap_1(sK3,sK3) = X0_57
% 51.28/7.00      | v1_pre_topc(X0_57) != iProver_top
% 51.28/7.00      | v2_pre_topc(X0_57) != iProver_top ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_18176,c_51,c_53]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_18764,plain,
% 51.28/7.00      ( sK0(sK3,sK3,X0_57) = u1_struct_0(sK3)
% 51.28/7.00      | k8_tmap_1(sK3,sK3) = X0_57
% 51.28/7.00      | v1_pre_topc(X0_57) != iProver_top
% 51.28/7.00      | v2_pre_topc(X0_57) != iProver_top
% 51.28/7.00      | l1_pre_topc(X0_57) != iProver_top ),
% 51.28/7.00      inference(renaming,[status(thm)],[c_18763]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_18774,plain,
% 51.28/7.00      ( sK0(sK3,sK3,k6_tmap_1(X0_57,u1_struct_0(X0_57))) = u1_struct_0(sK3)
% 51.28/7.00      | k6_tmap_1(X0_57,u1_struct_0(X0_57)) = k8_tmap_1(sK3,sK3)
% 51.28/7.00      | v2_pre_topc(X0_57) != iProver_top
% 51.28/7.00      | v2_pre_topc(k6_tmap_1(X0_57,u1_struct_0(X0_57))) != iProver_top
% 51.28/7.00      | v2_struct_0(X0_57) = iProver_top
% 51.28/7.00      | l1_pre_topc(X0_57) != iProver_top
% 51.28/7.00      | l1_pre_topc(k6_tmap_1(X0_57,u1_struct_0(X0_57))) != iProver_top ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_9047,c_18764]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_4029,plain,
% 51.28/7.00      ( m1_subset_1(u1_struct_0(X0_57),k1_zfmisc_1(u1_struct_0(X0_57))) = iProver_top
% 51.28/7.00      | l1_pre_topc(X0_57) != iProver_top ),
% 51.28/7.00      inference(predicate_to_equality,[status(thm)],[c_3915]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_5680,plain,
% 51.28/7.00      ( ~ m1_subset_1(u1_struct_0(X0_57),k1_zfmisc_1(u1_struct_0(X0_57)))
% 51.28/7.00      | ~ v2_pre_topc(X0_57)
% 51.28/7.00      | v2_pre_topc(k6_tmap_1(X0_57,u1_struct_0(X0_57)))
% 51.28/7.00      | v2_struct_0(X0_57)
% 51.28/7.00      | ~ l1_pre_topc(X0_57) ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_3928]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_5681,plain,
% 51.28/7.00      ( m1_subset_1(u1_struct_0(X0_57),k1_zfmisc_1(u1_struct_0(X0_57))) != iProver_top
% 51.28/7.00      | v2_pre_topc(X0_57) != iProver_top
% 51.28/7.00      | v2_pre_topc(k6_tmap_1(X0_57,u1_struct_0(X0_57))) = iProver_top
% 51.28/7.00      | v2_struct_0(X0_57) = iProver_top
% 51.28/7.00      | l1_pre_topc(X0_57) != iProver_top ),
% 51.28/7.00      inference(predicate_to_equality,[status(thm)],[c_5680]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_5688,plain,
% 51.28/7.00      ( ~ m1_subset_1(u1_struct_0(X0_57),k1_zfmisc_1(u1_struct_0(X0_57)))
% 51.28/7.00      | ~ v2_pre_topc(X0_57)
% 51.28/7.00      | v2_struct_0(X0_57)
% 51.28/7.00      | ~ l1_pre_topc(X0_57)
% 51.28/7.00      | l1_pre_topc(k6_tmap_1(X0_57,u1_struct_0(X0_57))) ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_3929]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_5689,plain,
% 51.28/7.00      ( m1_subset_1(u1_struct_0(X0_57),k1_zfmisc_1(u1_struct_0(X0_57))) != iProver_top
% 51.28/7.00      | v2_pre_topc(X0_57) != iProver_top
% 51.28/7.00      | v2_struct_0(X0_57) = iProver_top
% 51.28/7.00      | l1_pre_topc(X0_57) != iProver_top
% 51.28/7.00      | l1_pre_topc(k6_tmap_1(X0_57,u1_struct_0(X0_57))) = iProver_top ),
% 51.28/7.00      inference(predicate_to_equality,[status(thm)],[c_5688]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_19248,plain,
% 51.28/7.00      ( l1_pre_topc(X0_57) != iProver_top
% 51.28/7.00      | v2_struct_0(X0_57) = iProver_top
% 51.28/7.00      | sK0(sK3,sK3,k6_tmap_1(X0_57,u1_struct_0(X0_57))) = u1_struct_0(sK3)
% 51.28/7.00      | k6_tmap_1(X0_57,u1_struct_0(X0_57)) = k8_tmap_1(sK3,sK3)
% 51.28/7.00      | v2_pre_topc(X0_57) != iProver_top ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_18774,c_4029,c_5681,c_5689]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_19249,plain,
% 51.28/7.00      ( sK0(sK3,sK3,k6_tmap_1(X0_57,u1_struct_0(X0_57))) = u1_struct_0(sK3)
% 51.28/7.00      | k6_tmap_1(X0_57,u1_struct_0(X0_57)) = k8_tmap_1(sK3,sK3)
% 51.28/7.00      | v2_pre_topc(X0_57) != iProver_top
% 51.28/7.00      | v2_struct_0(X0_57) = iProver_top
% 51.28/7.00      | l1_pre_topc(X0_57) != iProver_top ),
% 51.28/7.00      inference(renaming,[status(thm)],[c_19248]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_19259,plain,
% 51.28/7.00      ( sK0(sK3,sK3,k6_tmap_1(sK3,u1_struct_0(sK3))) = u1_struct_0(sK3)
% 51.28/7.00      | k6_tmap_1(sK3,u1_struct_0(sK3)) = k8_tmap_1(sK3,sK3)
% 51.28/7.00      | v2_struct_0(sK3) = iProver_top
% 51.28/7.00      | l1_pre_topc(sK3) != iProver_top ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_4942,c_19249]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_8,plain,
% 51.28/7.00      ( ~ m1_pre_topc(X0,X1)
% 51.28/7.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 51.28/7.00      | ~ v1_pre_topc(k8_tmap_1(X1,X0))
% 51.28/7.00      | ~ v2_pre_topc(X1)
% 51.28/7.00      | ~ v2_pre_topc(k8_tmap_1(X1,X0))
% 51.28/7.00      | v2_struct_0(X1)
% 51.28/7.00      | ~ l1_pre_topc(X1)
% 51.28/7.00      | ~ l1_pre_topc(k8_tmap_1(X1,X0))
% 51.28/7.00      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 51.28/7.00      inference(cnf_transformation,[],[f120]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_367,plain,
% 51.28/7.00      ( ~ m1_pre_topc(X0,X1)
% 51.28/7.00      | ~ v1_pre_topc(k8_tmap_1(X1,X0))
% 51.28/7.00      | ~ v2_pre_topc(X1)
% 51.28/7.00      | ~ v2_pre_topc(k8_tmap_1(X1,X0))
% 51.28/7.00      | v2_struct_0(X1)
% 51.28/7.00      | ~ l1_pre_topc(X1)
% 51.28/7.00      | ~ l1_pre_topc(k8_tmap_1(X1,X0))
% 51.28/7.00      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_8,c_36]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1444,plain,
% 51.28/7.00      ( ~ v1_pre_topc(k8_tmap_1(X0,X1))
% 51.28/7.00      | ~ v2_pre_topc(X0)
% 51.28/7.00      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
% 51.28/7.00      | v2_struct_0(X0)
% 51.28/7.00      | ~ l1_pre_topc(X0)
% 51.28/7.00      | ~ l1_pre_topc(X2)
% 51.28/7.00      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
% 51.28/7.00      | X2 != X0
% 51.28/7.00      | X2 != X1
% 51.28/7.00      | k6_tmap_1(X0,u1_struct_0(X1)) = k8_tmap_1(X0,X1) ),
% 51.28/7.00      inference(resolution_lifted,[status(thm)],[c_367,c_37]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1445,plain,
% 51.28/7.00      ( ~ v1_pre_topc(k8_tmap_1(X0,X0))
% 51.28/7.00      | ~ v2_pre_topc(X0)
% 51.28/7.00      | ~ v2_pre_topc(k8_tmap_1(X0,X0))
% 51.28/7.00      | v2_struct_0(X0)
% 51.28/7.00      | ~ l1_pre_topc(X0)
% 51.28/7.00      | ~ l1_pre_topc(k8_tmap_1(X0,X0))
% 51.28/7.00      | k6_tmap_1(X0,u1_struct_0(X0)) = k8_tmap_1(X0,X0) ),
% 51.28/7.00      inference(unflattening,[status(thm)],[c_1444]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_3916,plain,
% 51.28/7.00      ( ~ v1_pre_topc(k8_tmap_1(X0_57,X0_57))
% 51.28/7.00      | ~ v2_pre_topc(X0_57)
% 51.28/7.00      | ~ v2_pre_topc(k8_tmap_1(X0_57,X0_57))
% 51.28/7.00      | v2_struct_0(X0_57)
% 51.28/7.00      | ~ l1_pre_topc(X0_57)
% 51.28/7.00      | ~ l1_pre_topc(k8_tmap_1(X0_57,X0_57))
% 51.28/7.00      | k6_tmap_1(X0_57,u1_struct_0(X0_57)) = k8_tmap_1(X0_57,X0_57) ),
% 51.28/7.00      inference(subtyping,[status(esa)],[c_1445]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_4027,plain,
% 51.28/7.00      ( ~ v1_pre_topc(k8_tmap_1(sK3,sK3))
% 51.28/7.00      | ~ v2_pre_topc(k8_tmap_1(sK3,sK3))
% 51.28/7.00      | ~ v2_pre_topc(sK3)
% 51.28/7.00      | v2_struct_0(sK3)
% 51.28/7.00      | ~ l1_pre_topc(k8_tmap_1(sK3,sK3))
% 51.28/7.00      | ~ l1_pre_topc(sK3)
% 51.28/7.00      | k6_tmap_1(sK3,u1_struct_0(sK3)) = k8_tmap_1(sK3,sK3) ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_3916]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_5633,plain,
% 51.28/7.00      ( ~ m1_subset_1(u1_struct_0(X0_57),k1_zfmisc_1(u1_struct_0(X0_57)))
% 51.28/7.00      | v1_pre_topc(k6_tmap_1(X0_57,u1_struct_0(X0_57)))
% 51.28/7.00      | ~ v2_pre_topc(X0_57)
% 51.28/7.00      | v2_struct_0(X0_57)
% 51.28/7.00      | ~ l1_pre_topc(X0_57) ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_3927]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_5635,plain,
% 51.28/7.00      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 51.28/7.00      | v1_pre_topc(k6_tmap_1(sK3,u1_struct_0(sK3)))
% 51.28/7.00      | ~ v2_pre_topc(sK3)
% 51.28/7.00      | v2_struct_0(sK3)
% 51.28/7.00      | ~ l1_pre_topc(sK3) ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_5633]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_5682,plain,
% 51.28/7.00      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 51.28/7.00      | v2_pre_topc(k6_tmap_1(sK3,u1_struct_0(sK3)))
% 51.28/7.00      | ~ v2_pre_topc(sK3)
% 51.28/7.00      | v2_struct_0(sK3)
% 51.28/7.00      | ~ l1_pre_topc(sK3) ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_5680]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_5690,plain,
% 51.28/7.00      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 51.28/7.00      | ~ v2_pre_topc(sK3)
% 51.28/7.00      | v2_struct_0(sK3)
% 51.28/7.00      | l1_pre_topc(k6_tmap_1(sK3,u1_struct_0(sK3)))
% 51.28/7.00      | ~ l1_pre_topc(sK3) ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_5688]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1624,plain,
% 51.28/7.00      ( ~ v1_pre_topc(X0)
% 51.28/7.00      | ~ v2_pre_topc(X1)
% 51.28/7.00      | ~ v2_pre_topc(X0)
% 51.28/7.00      | v2_struct_0(X1)
% 51.28/7.00      | ~ l1_pre_topc(X1)
% 51.28/7.00      | ~ l1_pre_topc(X0)
% 51.28/7.00      | ~ l1_pre_topc(X2)
% 51.28/7.00      | X2 != X1
% 51.28/7.00      | X2 != X3
% 51.28/7.00      | k6_tmap_1(X1,sK0(X1,X3,X0)) != X0
% 51.28/7.00      | k8_tmap_1(X1,X3) = X0 ),
% 51.28/7.00      inference(resolution_lifted,[status(thm)],[c_5,c_37]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1625,plain,
% 51.28/7.00      ( ~ v1_pre_topc(X0)
% 51.28/7.00      | ~ v2_pre_topc(X0)
% 51.28/7.00      | ~ v2_pre_topc(X1)
% 51.28/7.00      | v2_struct_0(X1)
% 51.28/7.00      | ~ l1_pre_topc(X0)
% 51.28/7.00      | ~ l1_pre_topc(X1)
% 51.28/7.00      | k6_tmap_1(X1,sK0(X1,X1,X0)) != X0
% 51.28/7.00      | k8_tmap_1(X1,X1) = X0 ),
% 51.28/7.00      inference(unflattening,[status(thm)],[c_1624]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_3908,plain,
% 51.28/7.00      ( ~ v1_pre_topc(X0_57)
% 51.28/7.00      | ~ v2_pre_topc(X1_57)
% 51.28/7.00      | ~ v2_pre_topc(X0_57)
% 51.28/7.00      | v2_struct_0(X1_57)
% 51.28/7.00      | ~ l1_pre_topc(X1_57)
% 51.28/7.00      | ~ l1_pre_topc(X0_57)
% 51.28/7.00      | k6_tmap_1(X1_57,sK0(X1_57,X1_57,X0_57)) != X0_57
% 51.28/7.00      | k8_tmap_1(X1_57,X1_57) = X0_57 ),
% 51.28/7.00      inference(subtyping,[status(esa)],[c_1625]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_6282,plain,
% 51.28/7.00      ( ~ v1_pre_topc(k6_tmap_1(X0_57,u1_struct_0(X0_57)))
% 51.28/7.00      | ~ v2_pre_topc(X1_57)
% 51.28/7.00      | ~ v2_pre_topc(k6_tmap_1(X0_57,u1_struct_0(X0_57)))
% 51.28/7.00      | v2_struct_0(X1_57)
% 51.28/7.00      | ~ l1_pre_topc(X1_57)
% 51.28/7.00      | ~ l1_pre_topc(k6_tmap_1(X0_57,u1_struct_0(X0_57)))
% 51.28/7.00      | k6_tmap_1(X1_57,sK0(X1_57,X1_57,k6_tmap_1(X0_57,u1_struct_0(X0_57)))) != k6_tmap_1(X0_57,u1_struct_0(X0_57))
% 51.28/7.00      | k8_tmap_1(X1_57,X1_57) = k6_tmap_1(X0_57,u1_struct_0(X0_57)) ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_3908]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_6304,plain,
% 51.28/7.00      ( ~ v1_pre_topc(k6_tmap_1(sK3,u1_struct_0(sK3)))
% 51.28/7.00      | ~ v2_pre_topc(k6_tmap_1(sK3,u1_struct_0(sK3)))
% 51.28/7.00      | ~ v2_pre_topc(sK3)
% 51.28/7.00      | v2_struct_0(sK3)
% 51.28/7.00      | ~ l1_pre_topc(k6_tmap_1(sK3,u1_struct_0(sK3)))
% 51.28/7.00      | ~ l1_pre_topc(sK3)
% 51.28/7.00      | k6_tmap_1(sK3,sK0(sK3,sK3,k6_tmap_1(sK3,u1_struct_0(sK3)))) != k6_tmap_1(sK3,u1_struct_0(sK3))
% 51.28/7.00      | k8_tmap_1(sK3,sK3) = k6_tmap_1(sK3,u1_struct_0(sK3)) ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_6282]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_3952,plain,
% 51.28/7.00      ( ~ v2_pre_topc(X0_57) | v2_pre_topc(X1_57) | X1_57 != X0_57 ),
% 51.28/7.00      theory(equality) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_7381,plain,
% 51.28/7.00      ( ~ v2_pre_topc(X0_57)
% 51.28/7.00      | v2_pre_topc(k8_tmap_1(X1_57,X1_57))
% 51.28/7.00      | k8_tmap_1(X1_57,X1_57) != X0_57 ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_3952]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_9376,plain,
% 51.28/7.00      ( ~ v2_pre_topc(k6_tmap_1(X0_57,u1_struct_0(X0_57)))
% 51.28/7.00      | v2_pre_topc(k8_tmap_1(X1_57,X1_57))
% 51.28/7.00      | k8_tmap_1(X1_57,X1_57) != k6_tmap_1(X0_57,u1_struct_0(X0_57)) ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_7381]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_9378,plain,
% 51.28/7.00      ( ~ v2_pre_topc(k6_tmap_1(sK3,u1_struct_0(sK3)))
% 51.28/7.00      | v2_pre_topc(k8_tmap_1(sK3,sK3))
% 51.28/7.00      | k8_tmap_1(sK3,sK3) != k6_tmap_1(sK3,u1_struct_0(sK3)) ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_9376]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_3956,plain,
% 51.28/7.00      ( ~ v1_pre_topc(X0_57) | v1_pre_topc(X1_57) | X1_57 != X0_57 ),
% 51.28/7.00      theory(equality) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_6281,plain,
% 51.28/7.00      ( v1_pre_topc(X0_57)
% 51.28/7.00      | ~ v1_pre_topc(k6_tmap_1(X1_57,u1_struct_0(X1_57)))
% 51.28/7.00      | X0_57 != k6_tmap_1(X1_57,u1_struct_0(X1_57)) ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_3956]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_9381,plain,
% 51.28/7.00      ( ~ v1_pre_topc(k6_tmap_1(X0_57,u1_struct_0(X0_57)))
% 51.28/7.00      | v1_pre_topc(k8_tmap_1(X1_57,X1_57))
% 51.28/7.00      | k8_tmap_1(X1_57,X1_57) != k6_tmap_1(X0_57,u1_struct_0(X0_57)) ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_6281]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_9383,plain,
% 51.28/7.00      ( ~ v1_pre_topc(k6_tmap_1(sK3,u1_struct_0(sK3)))
% 51.28/7.00      | v1_pre_topc(k8_tmap_1(sK3,sK3))
% 51.28/7.00      | k8_tmap_1(sK3,sK3) != k6_tmap_1(sK3,u1_struct_0(sK3)) ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_9381]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_3940,plain,
% 51.28/7.00      ( ~ l1_pre_topc(X0_57) | l1_pre_topc(X1_57) | X1_57 != X0_57 ),
% 51.28/7.00      theory(equality) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_6700,plain,
% 51.28/7.00      ( ~ l1_pre_topc(X0_57)
% 51.28/7.00      | l1_pre_topc(k8_tmap_1(X1_57,X2_57))
% 51.28/7.00      | k8_tmap_1(X1_57,X2_57) != X0_57 ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_3940]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_9386,plain,
% 51.28/7.00      ( ~ l1_pre_topc(k6_tmap_1(X0_57,u1_struct_0(X0_57)))
% 51.28/7.00      | l1_pre_topc(k8_tmap_1(X1_57,X1_57))
% 51.28/7.00      | k8_tmap_1(X1_57,X1_57) != k6_tmap_1(X0_57,u1_struct_0(X0_57)) ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_6700]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_9388,plain,
% 51.28/7.00      ( ~ l1_pre_topc(k6_tmap_1(sK3,u1_struct_0(sK3)))
% 51.28/7.00      | l1_pre_topc(k8_tmap_1(sK3,sK3))
% 51.28/7.00      | k8_tmap_1(sK3,sK3) != k6_tmap_1(sK3,u1_struct_0(sK3)) ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_9386]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_8322,plain,
% 51.28/7.00      ( X0_58 != u1_struct_0(X0_57)
% 51.28/7.00      | X1_57 != X0_57
% 51.28/7.00      | k6_tmap_1(X1_57,X0_58) = k6_tmap_1(X0_57,u1_struct_0(X0_57)) ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_3955]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_13152,plain,
% 51.28/7.00      ( sK0(X0_57,X0_57,k6_tmap_1(X1_57,u1_struct_0(X1_57))) != u1_struct_0(X0_57)
% 51.28/7.00      | X2_57 != X0_57
% 51.28/7.00      | k6_tmap_1(X2_57,sK0(X0_57,X0_57,k6_tmap_1(X1_57,u1_struct_0(X1_57)))) = k6_tmap_1(X0_57,u1_struct_0(X0_57)) ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_8322]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_13153,plain,
% 51.28/7.00      ( sK0(sK3,sK3,k6_tmap_1(sK3,u1_struct_0(sK3))) != u1_struct_0(sK3)
% 51.28/7.00      | k6_tmap_1(sK3,sK0(sK3,sK3,k6_tmap_1(sK3,u1_struct_0(sK3)))) = k6_tmap_1(sK3,u1_struct_0(sK3))
% 51.28/7.00      | sK3 != sK3 ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_13152]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_19361,plain,
% 51.28/7.00      ( v2_struct_0(sK3)
% 51.28/7.00      | ~ l1_pre_topc(sK3)
% 51.28/7.00      | sK0(sK3,sK3,k6_tmap_1(sK3,u1_struct_0(sK3))) = u1_struct_0(sK3)
% 51.28/7.00      | k6_tmap_1(sK3,u1_struct_0(sK3)) = k8_tmap_1(sK3,sK3) ),
% 51.28/7.00      inference(predicate_to_equality_rev,[status(thm)],[c_19259]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_19534,plain,
% 51.28/7.00      ( k6_tmap_1(sK3,u1_struct_0(sK3)) = k8_tmap_1(sK3,sK3) ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_19259,c_50,c_49,c_48,c_65,c_68,c_3985,c_4027,c_5635,
% 51.28/7.00                 c_5682,c_5690,c_6304,c_9378,c_9383,c_9388,c_13153,
% 51.28/7.00                 c_19361]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_31030,plain,
% 51.28/7.00      ( k9_tmap_1(sK3,sK4) != k6_partfun1(u1_struct_0(sK3))
% 51.28/7.00      | k8_tmap_1(sK3,sK3) != k8_tmap_1(sK3,sK4)
% 51.28/7.00      | v1_tsep_1(sK4,sK3) != iProver_top
% 51.28/7.00      | v1_tsep_1(sK3,sK3) != iProver_top ),
% 51.28/7.00      inference(light_normalisation,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_4976,c_10943,c_19534]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1676,plain,
% 51.28/7.00      ( v3_pre_topc(u1_struct_0(X0),X1)
% 51.28/7.00      | ~ v1_tsep_1(X0,X1)
% 51.28/7.00      | ~ l1_pre_topc(X1)
% 51.28/7.00      | sK4 != X0
% 51.28/7.00      | sK3 != X1 ),
% 51.28/7.00      inference(resolution_lifted,[status(thm)],[c_348,c_298]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1677,plain,
% 51.28/7.00      ( v3_pre_topc(u1_struct_0(sK4),sK3)
% 51.28/7.00      | ~ v1_tsep_1(sK4,sK3)
% 51.28/7.00      | ~ l1_pre_topc(sK3) ),
% 51.28/7.00      inference(unflattening,[status(thm)],[c_1676]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1679,plain,
% 51.28/7.00      ( ~ v1_tsep_1(sK4,sK3) | v3_pre_topc(u1_struct_0(sK4),sK3) ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_1677,c_48]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1680,plain,
% 51.28/7.00      ( v3_pre_topc(u1_struct_0(sK4),sK3) | ~ v1_tsep_1(sK4,sK3) ),
% 51.28/7.00      inference(renaming,[status(thm)],[c_1679]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_2317,plain,
% 51.28/7.00      ( ~ v1_tsep_1(sK4,sK3)
% 51.28/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 51.28/7.00      | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
% 51.28/7.00      | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4)
% 51.28/7.00      | u1_struct_0(sK4) != X0
% 51.28/7.00      | sK3 != sK3 ),
% 51.28/7.00      inference(resolution_lifted,[status(thm)],[c_2250,c_1680]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_2318,plain,
% 51.28/7.00      ( ~ v1_tsep_1(sK4,sK3)
% 51.28/7.00      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 51.28/7.00      | k6_tmap_1(sK3,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4)
% 51.28/7.00      | k7_tmap_1(sK3,u1_struct_0(sK4)) != k9_tmap_1(sK3,sK4) ),
% 51.28/7.00      inference(unflattening,[status(thm)],[c_2317]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_2320,plain,
% 51.28/7.00      ( ~ v1_tsep_1(sK4,sK3)
% 51.28/7.00      | k6_tmap_1(sK3,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4)
% 51.28/7.00      | k7_tmap_1(sK3,u1_struct_0(sK4)) != k9_tmap_1(sK3,sK4) ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_2318,c_48,c_1691]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_3886,plain,
% 51.28/7.00      ( ~ v1_tsep_1(sK4,sK3)
% 51.28/7.00      | k7_tmap_1(sK3,u1_struct_0(sK4)) != k9_tmap_1(sK3,sK4)
% 51.28/7.00      | k6_tmap_1(sK3,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4) ),
% 51.28/7.00      inference(subtyping,[status(esa)],[c_2320]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_4975,plain,
% 51.28/7.00      ( k7_tmap_1(sK3,u1_struct_0(sK4)) != k9_tmap_1(sK3,sK4)
% 51.28/7.00      | k6_tmap_1(sK3,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4)
% 51.28/7.00      | v1_tsep_1(sK4,sK3) != iProver_top ),
% 51.28/7.00      inference(predicate_to_equality,[status(thm)],[c_3886]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_7521,plain,
% 51.28/7.00      ( k9_tmap_1(sK3,sK4) != k6_partfun1(u1_struct_0(sK3))
% 51.28/7.00      | k6_tmap_1(sK3,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4)
% 51.28/7.00      | v1_tsep_1(sK4,sK3) != iProver_top ),
% 51.28/7.00      inference(demodulation,[status(thm)],[c_7517,c_4975]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_31036,plain,
% 51.28/7.00      ( v1_tsep_1(sK4,sK3) != iProver_top
% 51.28/7.00      | k9_tmap_1(sK3,sK4) != k6_partfun1(u1_struct_0(sK3)) ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_31030,c_50,c_51,c_49,c_52,c_48,c_53,c_1691,c_1692,
% 51.28/7.00                 c_3985,c_5630,c_5677,c_5678,c_5685,c_5686,c_5955,c_6485,
% 51.28/7.00                 c_6486,c_7398,c_7521,c_8449]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_31037,plain,
% 51.28/7.00      ( k9_tmap_1(sK3,sK4) != k6_partfun1(u1_struct_0(sK3))
% 51.28/7.00      | v1_tsep_1(sK4,sK3) != iProver_top ),
% 51.28/7.00      inference(renaming,[status(thm)],[c_31036]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_161674,plain,
% 51.28/7.00      ( k6_partfun1(u1_struct_0(sK3)) != k6_partfun1(u1_struct_0(sK3))
% 51.28/7.00      | v1_tsep_1(sK4,sK3) != iProver_top ),
% 51.28/7.00      inference(demodulation,[status(thm)],[c_161657,c_31037]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_161698,plain,
% 51.28/7.00      ( v1_tsep_1(sK4,sK3) != iProver_top ),
% 51.28/7.00      inference(equality_resolution_simp,[status(thm)],[c_161674]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_31,plain,
% 51.28/7.00      ( ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
% 51.28/7.00      | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
% 51.28/7.00      | v3_pre_topc(X1,X0)
% 51.28/7.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 51.28/7.00      | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
% 51.28/7.00      | ~ v2_pre_topc(X0)
% 51.28/7.00      | ~ v1_funct_1(k7_tmap_1(X0,X1))
% 51.28/7.00      | v2_struct_0(X0)
% 51.28/7.00      | ~ l1_pre_topc(X0) ),
% 51.28/7.00      inference(cnf_transformation,[],[f103]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_326,plain,
% 51.28/7.00      ( ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
% 51.28/7.00      | v3_pre_topc(X1,X0)
% 51.28/7.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 51.28/7.00      | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
% 51.28/7.00      | ~ v2_pre_topc(X0)
% 51.28/7.00      | ~ v1_funct_1(k7_tmap_1(X0,X1))
% 51.28/7.00      | v2_struct_0(X0)
% 51.28/7.00      | ~ l1_pre_topc(X0) ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_31,c_21]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_42,negated_conjecture,
% 51.28/7.00      ( v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4))
% 51.28/7.00      | v1_tsep_1(sK4,sK3) ),
% 51.28/7.00      inference(cnf_transformation,[],[f114]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_744,plain,
% 51.28/7.00      ( v3_pre_topc(X0,X1)
% 51.28/7.00      | v1_tsep_1(sK4,sK3)
% 51.28/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 51.28/7.00      | ~ m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
% 51.28/7.00      | ~ v2_pre_topc(X1)
% 51.28/7.00      | ~ v1_funct_1(k7_tmap_1(X1,X0))
% 51.28/7.00      | v2_struct_0(X1)
% 51.28/7.00      | ~ l1_pre_topc(X1)
% 51.28/7.00      | k6_tmap_1(X1,X0) != k8_tmap_1(sK3,sK4)
% 51.28/7.00      | k7_tmap_1(X1,X0) != k9_tmap_1(sK3,sK4)
% 51.28/7.00      | sK3 != X1 ),
% 51.28/7.00      inference(resolution_lifted,[status(thm)],[c_326,c_42]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_745,plain,
% 51.28/7.00      ( v3_pre_topc(X0,sK3)
% 51.28/7.00      | v1_tsep_1(sK4,sK3)
% 51.28/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 51.28/7.00      | ~ m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))))
% 51.28/7.00      | ~ v2_pre_topc(sK3)
% 51.28/7.00      | ~ v1_funct_1(k7_tmap_1(sK3,X0))
% 51.28/7.00      | v2_struct_0(sK3)
% 51.28/7.00      | ~ l1_pre_topc(sK3)
% 51.28/7.00      | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
% 51.28/7.00      | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4) ),
% 51.28/7.00      inference(unflattening,[status(thm)],[c_744]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_749,plain,
% 51.28/7.00      ( ~ m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))))
% 51.28/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 51.28/7.00      | v1_tsep_1(sK4,sK3)
% 51.28/7.00      | v3_pre_topc(X0,sK3)
% 51.28/7.00      | ~ v1_funct_1(k7_tmap_1(sK3,X0))
% 51.28/7.00      | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
% 51.28/7.00      | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4) ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_745,c_50,c_49,c_48]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_750,plain,
% 51.28/7.00      ( v3_pre_topc(X0,sK3)
% 51.28/7.00      | v1_tsep_1(sK4,sK3)
% 51.28/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 51.28/7.00      | ~ m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))))
% 51.28/7.00      | ~ v1_funct_1(k7_tmap_1(sK3,X0))
% 51.28/7.00      | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
% 51.28/7.00      | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4) ),
% 51.28/7.00      inference(renaming,[status(thm)],[c_749]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_13,plain,
% 51.28/7.00      ( ~ v3_pre_topc(sK2(X0,X1),X0)
% 51.28/7.00      | v1_tsep_1(X1,X0)
% 51.28/7.00      | ~ m1_pre_topc(X1,X0)
% 51.28/7.00      | ~ l1_pre_topc(X0) ),
% 51.28/7.00      inference(cnf_transformation,[],[f84]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1959,plain,
% 51.28/7.00      ( ~ v3_pre_topc(sK2(X0,X1),X0)
% 51.28/7.00      | v1_tsep_1(X1,X0)
% 51.28/7.00      | ~ l1_pre_topc(X0)
% 51.28/7.00      | sK4 != X1
% 51.28/7.00      | sK3 != X0 ),
% 51.28/7.00      inference(resolution_lifted,[status(thm)],[c_13,c_298]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1960,plain,
% 51.28/7.00      ( ~ v3_pre_topc(sK2(sK3,sK4),sK3)
% 51.28/7.00      | v1_tsep_1(sK4,sK3)
% 51.28/7.00      | ~ l1_pre_topc(sK3) ),
% 51.28/7.00      inference(unflattening,[status(thm)],[c_1959]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1962,plain,
% 51.28/7.00      ( v1_tsep_1(sK4,sK3) | ~ v3_pre_topc(sK2(sK3,sK4),sK3) ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_1960,c_48]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1963,plain,
% 51.28/7.00      ( ~ v3_pre_topc(sK2(sK3,sK4),sK3) | v1_tsep_1(sK4,sK3) ),
% 51.28/7.00      inference(renaming,[status(thm)],[c_1962]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_2294,plain,
% 51.28/7.00      ( v1_tsep_1(sK4,sK3)
% 51.28/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 51.28/7.00      | ~ m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))))
% 51.28/7.00      | ~ v1_funct_1(k7_tmap_1(sK3,X0))
% 51.28/7.00      | sK2(sK3,sK4) != X0
% 51.28/7.00      | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
% 51.28/7.00      | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4)
% 51.28/7.00      | sK3 != sK3 ),
% 51.28/7.00      inference(resolution_lifted,[status(thm)],[c_750,c_1963]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_2295,plain,
% 51.28/7.00      ( v1_tsep_1(sK4,sK3)
% 51.28/7.00      | ~ m1_subset_1(sK2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 51.28/7.00      | ~ m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4))))))
% 51.28/7.00      | ~ v1_funct_1(k7_tmap_1(sK3,sK2(sK3,sK4)))
% 51.28/7.00      | k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4)
% 51.28/7.00      | k7_tmap_1(sK3,sK2(sK3,sK4)) != k9_tmap_1(sK3,sK4) ),
% 51.28/7.00      inference(unflattening,[status(thm)],[c_2294]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_15,plain,
% 51.28/7.00      ( v1_tsep_1(X0,X1)
% 51.28/7.00      | ~ m1_pre_topc(X0,X1)
% 51.28/7.00      | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 51.28/7.00      | ~ l1_pre_topc(X1) ),
% 51.28/7.00      inference(cnf_transformation,[],[f82]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1723,plain,
% 51.28/7.00      ( v1_tsep_1(X0,X1)
% 51.28/7.00      | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 51.28/7.00      | ~ l1_pre_topc(X1)
% 51.28/7.00      | sK4 != X0
% 51.28/7.00      | sK3 != X1 ),
% 51.28/7.00      inference(resolution_lifted,[status(thm)],[c_15,c_298]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1724,plain,
% 51.28/7.00      ( v1_tsep_1(sK4,sK3)
% 51.28/7.00      | m1_subset_1(sK2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 51.28/7.00      | ~ l1_pre_topc(sK3) ),
% 51.28/7.00      inference(unflattening,[status(thm)],[c_1723]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_2297,plain,
% 51.28/7.00      ( v1_tsep_1(sK4,sK3)
% 51.28/7.00      | ~ m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4))))))
% 51.28/7.00      | ~ v1_funct_1(k7_tmap_1(sK3,sK2(sK3,sK4)))
% 51.28/7.00      | k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4)
% 51.28/7.00      | k7_tmap_1(sK3,sK2(sK3,sK4)) != k9_tmap_1(sK3,sK4) ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_2295,c_48,c_1724]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_3887,plain,
% 51.28/7.00      ( v1_tsep_1(sK4,sK3)
% 51.28/7.00      | ~ m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4))))))
% 51.28/7.00      | ~ v1_funct_1(k7_tmap_1(sK3,sK2(sK3,sK4)))
% 51.28/7.00      | k7_tmap_1(sK3,sK2(sK3,sK4)) != k9_tmap_1(sK3,sK4)
% 51.28/7.00      | k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4) ),
% 51.28/7.00      inference(subtyping,[status(esa)],[c_2297]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_4974,plain,
% 51.28/7.00      ( k7_tmap_1(sK3,sK2(sK3,sK4)) != k9_tmap_1(sK3,sK4)
% 51.28/7.00      | k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4)
% 51.28/7.00      | v1_tsep_1(sK4,sK3) = iProver_top
% 51.28/7.00      | m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4)))))) != iProver_top
% 51.28/7.00      | v1_funct_1(k7_tmap_1(sK3,sK2(sK3,sK4))) != iProver_top ),
% 51.28/7.00      inference(predicate_to_equality,[status(thm)],[c_3887]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_4085,plain,
% 51.28/7.00      ( k7_tmap_1(sK3,sK2(sK3,sK4)) != k9_tmap_1(sK3,sK4)
% 51.28/7.00      | k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4)
% 51.28/7.00      | v1_tsep_1(sK4,sK3) = iProver_top
% 51.28/7.00      | m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4)))))) != iProver_top
% 51.28/7.00      | v1_funct_1(k7_tmap_1(sK3,sK2(sK3,sK4))) != iProver_top ),
% 51.28/7.00      inference(predicate_to_equality,[status(thm)],[c_3887]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1726,plain,
% 51.28/7.00      ( m1_subset_1(sK2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 51.28/7.00      | v1_tsep_1(sK4,sK3) ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_1724,c_48]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1727,plain,
% 51.28/7.00      ( v1_tsep_1(sK4,sK3)
% 51.28/7.00      | m1_subset_1(sK2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 51.28/7.00      inference(renaming,[status(thm)],[c_1726]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_3903,plain,
% 51.28/7.00      ( v1_tsep_1(sK4,sK3)
% 51.28/7.00      | m1_subset_1(sK2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 51.28/7.00      inference(subtyping,[status(esa)],[c_1727]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_4958,plain,
% 51.28/7.00      ( v1_tsep_1(sK4,sK3) = iProver_top
% 51.28/7.00      | m1_subset_1(sK2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 51.28/7.00      inference(predicate_to_equality,[status(thm)],[c_3903]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_6194,plain,
% 51.28/7.00      ( v1_tsep_1(sK4,sK3) = iProver_top
% 51.28/7.00      | v2_pre_topc(sK3) != iProver_top
% 51.28/7.00      | v1_funct_1(k7_tmap_1(sK3,sK2(sK3,sK4))) = iProver_top
% 51.28/7.00      | v2_struct_0(sK3) = iProver_top
% 51.28/7.00      | l1_pre_topc(sK3) != iProver_top ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_4958,c_4937]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_7178,plain,
% 51.28/7.00      ( m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4)))))) != iProver_top
% 51.28/7.00      | v1_tsep_1(sK4,sK3) = iProver_top
% 51.28/7.00      | k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4)
% 51.28/7.00      | k7_tmap_1(sK3,sK2(sK3,sK4)) != k9_tmap_1(sK3,sK4) ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_4974,c_51,c_52,c_53,c_4085,c_6194]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_7179,plain,
% 51.28/7.00      ( k7_tmap_1(sK3,sK2(sK3,sK4)) != k9_tmap_1(sK3,sK4)
% 51.28/7.00      | k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4)
% 51.28/7.00      | v1_tsep_1(sK4,sK3) = iProver_top
% 51.28/7.00      | m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4)))))) != iProver_top ),
% 51.28/7.00      inference(renaming,[status(thm)],[c_7178]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_161676,plain,
% 51.28/7.00      ( k7_tmap_1(sK3,sK2(sK3,sK4)) != k6_partfun1(u1_struct_0(sK3))
% 51.28/7.00      | k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4)
% 51.28/7.00      | v1_tsep_1(sK4,sK3) = iProver_top
% 51.28/7.00      | m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4)))))) != iProver_top ),
% 51.28/7.00      inference(demodulation,[status(thm)],[c_161657,c_7179]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_161701,plain,
% 51.28/7.00      ( k7_tmap_1(sK3,sK2(sK3,sK4)) != k6_partfun1(u1_struct_0(sK3))
% 51.28/7.00      | k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4)
% 51.28/7.00      | m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4)))))) != iProver_top ),
% 51.28/7.00      inference(backward_subsumption_resolution,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_161698,c_161676]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_117690,plain,
% 51.28/7.00      ( ~ m1_subset_1(sK2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 51.28/7.00      | m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4))))))
% 51.28/7.00      | ~ v2_pre_topc(sK3)
% 51.28/7.00      | v2_struct_0(sK3)
% 51.28/7.00      | ~ l1_pre_topc(sK3) ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_3926]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_117712,plain,
% 51.28/7.00      ( m1_subset_1(sK2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 51.28/7.00      | m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4)))))) = iProver_top
% 51.28/7.00      | v2_pre_topc(sK3) != iProver_top
% 51.28/7.00      | v2_struct_0(sK3) = iProver_top
% 51.28/7.00      | l1_pre_topc(sK3) != iProver_top ),
% 51.28/7.00      inference(predicate_to_equality,[status(thm)],[c_117690]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_6195,plain,
% 51.28/7.00      ( v1_tsep_1(sK4,sK3) = iProver_top
% 51.28/7.00      | v1_pre_topc(k6_tmap_1(sK3,sK2(sK3,sK4))) = iProver_top
% 51.28/7.00      | v2_pre_topc(sK3) != iProver_top
% 51.28/7.00      | v2_struct_0(sK3) = iProver_top
% 51.28/7.00      | l1_pre_topc(sK3) != iProver_top ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_4958,c_4934]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_8117,plain,
% 51.28/7.00      ( v1_pre_topc(k6_tmap_1(sK3,sK2(sK3,sK4))) = iProver_top
% 51.28/7.00      | v1_tsep_1(sK4,sK3) = iProver_top ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_6195,c_51,c_52,c_53]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_8118,plain,
% 51.28/7.00      ( v1_tsep_1(sK4,sK3) = iProver_top
% 51.28/7.00      | v1_pre_topc(k6_tmap_1(sK3,sK2(sK3,sK4))) = iProver_top ),
% 51.28/7.00      inference(renaming,[status(thm)],[c_8117]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_7,plain,
% 51.28/7.00      ( ~ m1_pre_topc(X0,X1)
% 51.28/7.00      | m1_subset_1(sK0(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 51.28/7.00      | ~ v1_pre_topc(X2)
% 51.28/7.00      | ~ v2_pre_topc(X1)
% 51.28/7.00      | ~ v2_pre_topc(X2)
% 51.28/7.00      | v2_struct_0(X1)
% 51.28/7.00      | ~ l1_pre_topc(X1)
% 51.28/7.00      | ~ l1_pre_topc(X2)
% 51.28/7.00      | k8_tmap_1(X1,X0) = X2 ),
% 51.28/7.00      inference(cnf_transformation,[],[f74]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1751,plain,
% 51.28/7.00      ( m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
% 51.28/7.00      | ~ v1_pre_topc(X2)
% 51.28/7.00      | ~ v2_pre_topc(X0)
% 51.28/7.00      | ~ v2_pre_topc(X2)
% 51.28/7.00      | v2_struct_0(X0)
% 51.28/7.00      | ~ l1_pre_topc(X0)
% 51.28/7.00      | ~ l1_pre_topc(X2)
% 51.28/7.00      | k8_tmap_1(X0,X1) = X2
% 51.28/7.00      | sK4 != X1
% 51.28/7.00      | sK3 != X0 ),
% 51.28/7.00      inference(resolution_lifted,[status(thm)],[c_7,c_298]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1752,plain,
% 51.28/7.00      ( m1_subset_1(sK0(sK3,sK4,X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 51.28/7.00      | ~ v1_pre_topc(X0)
% 51.28/7.00      | ~ v2_pre_topc(X0)
% 51.28/7.00      | ~ v2_pre_topc(sK3)
% 51.28/7.00      | v2_struct_0(sK3)
% 51.28/7.00      | ~ l1_pre_topc(X0)
% 51.28/7.00      | ~ l1_pre_topc(sK3)
% 51.28/7.00      | k8_tmap_1(sK3,sK4) = X0 ),
% 51.28/7.00      inference(unflattening,[status(thm)],[c_1751]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1756,plain,
% 51.28/7.00      ( ~ l1_pre_topc(X0)
% 51.28/7.00      | ~ v2_pre_topc(X0)
% 51.28/7.00      | ~ v1_pre_topc(X0)
% 51.28/7.00      | m1_subset_1(sK0(sK3,sK4,X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 51.28/7.00      | k8_tmap_1(sK3,sK4) = X0 ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_1752,c_50,c_49,c_48]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1757,plain,
% 51.28/7.00      ( m1_subset_1(sK0(sK3,sK4,X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 51.28/7.00      | ~ v1_pre_topc(X0)
% 51.28/7.00      | ~ v2_pre_topc(X0)
% 51.28/7.00      | ~ l1_pre_topc(X0)
% 51.28/7.00      | k8_tmap_1(sK3,sK4) = X0 ),
% 51.28/7.00      inference(renaming,[status(thm)],[c_1756]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_3901,plain,
% 51.28/7.00      ( m1_subset_1(sK0(sK3,sK4,X0_57),k1_zfmisc_1(u1_struct_0(sK3)))
% 51.28/7.00      | ~ v1_pre_topc(X0_57)
% 51.28/7.00      | ~ v2_pre_topc(X0_57)
% 51.28/7.00      | ~ l1_pre_topc(X0_57)
% 51.28/7.00      | k8_tmap_1(sK3,sK4) = X0_57 ),
% 51.28/7.00      inference(subtyping,[status(esa)],[c_1757]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_4960,plain,
% 51.28/7.00      ( k8_tmap_1(sK3,sK4) = X0_57
% 51.28/7.00      | m1_subset_1(sK0(sK3,sK4,X0_57),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 51.28/7.00      | v1_pre_topc(X0_57) != iProver_top
% 51.28/7.00      | v2_pre_topc(X0_57) != iProver_top
% 51.28/7.00      | l1_pre_topc(X0_57) != iProver_top ),
% 51.28/7.00      inference(predicate_to_equality,[status(thm)],[c_3901]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_6411,plain,
% 51.28/7.00      ( k7_tmap_1(sK3,sK0(sK3,sK4,X0_57)) = k6_partfun1(u1_struct_0(sK3))
% 51.28/7.00      | k8_tmap_1(sK3,sK4) = X0_57
% 51.28/7.00      | v1_pre_topc(X0_57) != iProver_top
% 51.28/7.00      | v2_pre_topc(X0_57) != iProver_top
% 51.28/7.00      | v2_pre_topc(sK3) != iProver_top
% 51.28/7.00      | v2_struct_0(sK3) = iProver_top
% 51.28/7.00      | l1_pre_topc(X0_57) != iProver_top
% 51.28/7.00      | l1_pre_topc(sK3) != iProver_top ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_4960,c_4931]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_9433,plain,
% 51.28/7.00      ( l1_pre_topc(X0_57) != iProver_top
% 51.28/7.00      | v2_pre_topc(X0_57) != iProver_top
% 51.28/7.00      | v1_pre_topc(X0_57) != iProver_top
% 51.28/7.00      | k8_tmap_1(sK3,sK4) = X0_57
% 51.28/7.00      | k7_tmap_1(sK3,sK0(sK3,sK4,X0_57)) = k6_partfun1(u1_struct_0(sK3)) ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_6411,c_51,c_52,c_53]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_9434,plain,
% 51.28/7.00      ( k7_tmap_1(sK3,sK0(sK3,sK4,X0_57)) = k6_partfun1(u1_struct_0(sK3))
% 51.28/7.00      | k8_tmap_1(sK3,sK4) = X0_57
% 51.28/7.00      | v1_pre_topc(X0_57) != iProver_top
% 51.28/7.00      | v2_pre_topc(X0_57) != iProver_top
% 51.28/7.00      | l1_pre_topc(X0_57) != iProver_top ),
% 51.28/7.00      inference(renaming,[status(thm)],[c_9433]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_9445,plain,
% 51.28/7.00      ( k7_tmap_1(sK3,sK0(sK3,sK4,k6_tmap_1(sK3,sK2(sK3,sK4)))) = k6_partfun1(u1_struct_0(sK3))
% 51.28/7.00      | k6_tmap_1(sK3,sK2(sK3,sK4)) = k8_tmap_1(sK3,sK4)
% 51.28/7.00      | v1_tsep_1(sK4,sK3) = iProver_top
% 51.28/7.00      | v2_pre_topc(k6_tmap_1(sK3,sK2(sK3,sK4))) != iProver_top
% 51.28/7.00      | l1_pre_topc(k6_tmap_1(sK3,sK2(sK3,sK4))) != iProver_top ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_8118,c_9434]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_6196,plain,
% 51.28/7.00      ( v1_tsep_1(sK4,sK3) = iProver_top
% 51.28/7.00      | v2_pre_topc(k6_tmap_1(sK3,sK2(sK3,sK4))) = iProver_top
% 51.28/7.00      | v2_pre_topc(sK3) != iProver_top
% 51.28/7.00      | v2_struct_0(sK3) = iProver_top
% 51.28/7.00      | l1_pre_topc(sK3) != iProver_top ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_4958,c_4933]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_6197,plain,
% 51.28/7.00      ( v1_tsep_1(sK4,sK3) = iProver_top
% 51.28/7.00      | v2_pre_topc(sK3) != iProver_top
% 51.28/7.00      | v2_struct_0(sK3) = iProver_top
% 51.28/7.00      | l1_pre_topc(k6_tmap_1(sK3,sK2(sK3,sK4))) = iProver_top
% 51.28/7.00      | l1_pre_topc(sK3) != iProver_top ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_4958,c_4932]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_5866,plain,
% 51.28/7.00      ( k6_tmap_1(sK3,sK2(sK3,sK4)) != X0_57
% 51.28/7.00      | k6_tmap_1(sK3,sK2(sK3,sK4)) = k8_tmap_1(sK3,sK4)
% 51.28/7.00      | k8_tmap_1(sK3,sK4) != X0_57 ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_3937]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_6492,plain,
% 51.28/7.00      ( k6_tmap_1(sK3,sK2(sK3,sK4)) != k6_tmap_1(sK3,sK2(sK3,sK4))
% 51.28/7.00      | k6_tmap_1(sK3,sK2(sK3,sK4)) = k8_tmap_1(sK3,sK4)
% 51.28/7.00      | k8_tmap_1(sK3,sK4) != k6_tmap_1(sK3,sK2(sK3,sK4)) ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_5866]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_6493,plain,
% 51.28/7.00      ( k6_tmap_1(sK3,sK2(sK3,sK4)) = k6_tmap_1(sK3,sK2(sK3,sK4)) ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_3933]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_7364,plain,
% 51.28/7.00      ( X0_57 != X1_57 | X1_57 = X0_57 ),
% 51.28/7.00      inference(resolution,[status(thm)],[c_3937,c_3933]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_10897,plain,
% 51.28/7.00      ( X0_58 != X1_58
% 51.28/7.00      | X0_57 != X1_57
% 51.28/7.00      | k6_tmap_1(X1_57,X1_58) = k6_tmap_1(X0_57,X0_58) ),
% 51.28/7.00      inference(resolution,[status(thm)],[c_7364,c_3955]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_50348,plain,
% 51.28/7.00      ( ~ v1_pre_topc(k6_tmap_1(X0_57,X0_58))
% 51.28/7.00      | ~ v2_pre_topc(k6_tmap_1(X0_57,X0_58))
% 51.28/7.00      | ~ l1_pre_topc(k6_tmap_1(X0_57,X0_58))
% 51.28/7.00      | X0_58 != sK0(sK3,sK4,k6_tmap_1(X0_57,X0_58))
% 51.28/7.00      | X0_57 != sK3
% 51.28/7.00      | k8_tmap_1(sK3,sK4) = k6_tmap_1(X0_57,X0_58) ),
% 51.28/7.00      inference(resolution,[status(thm)],[c_10897,c_3899]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_3938,plain,
% 51.28/7.00      ( X0_58 != X1_58 | X2_58 != X1_58 | X2_58 = X0_58 ),
% 51.28/7.00      theory(equality) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_14,plain,
% 51.28/7.00      ( v1_tsep_1(X0,X1)
% 51.28/7.00      | ~ m1_pre_topc(X0,X1)
% 51.28/7.00      | ~ l1_pre_topc(X1)
% 51.28/7.00      | sK2(X1,X0) = u1_struct_0(X0) ),
% 51.28/7.00      inference(cnf_transformation,[],[f83]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1737,plain,
% 51.28/7.00      ( v1_tsep_1(X0,X1)
% 51.28/7.00      | ~ l1_pre_topc(X1)
% 51.28/7.00      | sK2(X1,X0) = u1_struct_0(X0)
% 51.28/7.00      | sK4 != X0
% 51.28/7.00      | sK3 != X1 ),
% 51.28/7.00      inference(resolution_lifted,[status(thm)],[c_14,c_298]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1738,plain,
% 51.28/7.00      ( v1_tsep_1(sK4,sK3)
% 51.28/7.00      | ~ l1_pre_topc(sK3)
% 51.28/7.00      | sK2(sK3,sK4) = u1_struct_0(sK4) ),
% 51.28/7.00      inference(unflattening,[status(thm)],[c_1737]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1740,plain,
% 51.28/7.00      ( v1_tsep_1(sK4,sK3) | sK2(sK3,sK4) = u1_struct_0(sK4) ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_1738,c_48]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_3902,plain,
% 51.28/7.00      ( v1_tsep_1(sK4,sK3) | sK2(sK3,sK4) = u1_struct_0(sK4) ),
% 51.28/7.00      inference(subtyping,[status(esa)],[c_1740]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_7406,plain,
% 51.28/7.00      ( v1_tsep_1(sK4,sK3)
% 51.28/7.00      | X0_58 != u1_struct_0(sK4)
% 51.28/7.00      | sK2(sK3,sK4) = X0_58 ),
% 51.28/7.00      inference(resolution,[status(thm)],[c_3938,c_3902]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_7568,plain,
% 51.28/7.00      ( v1_tsep_1(sK4,sK3)
% 51.28/7.00      | X0_58 != X1_58
% 51.28/7.00      | X1_58 != u1_struct_0(sK4)
% 51.28/7.00      | sK2(sK3,sK4) = X0_58 ),
% 51.28/7.00      inference(resolution,[status(thm)],[c_7406,c_3938]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_3941,plain,
% 51.28/7.00      ( u1_struct_0(X0_57) = u1_struct_0(X1_57) | X0_57 != X1_57 ),
% 51.28/7.00      theory(equality) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_7948,plain,
% 51.28/7.00      ( v1_tsep_1(sK4,sK3)
% 51.28/7.00      | X0_58 != u1_struct_0(X0_57)
% 51.28/7.00      | sK2(sK3,sK4) = X0_58
% 51.28/7.00      | X0_57 != sK4 ),
% 51.28/7.00      inference(resolution,[status(thm)],[c_7568,c_3941]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_13039,plain,
% 51.28/7.00      ( v1_tsep_1(sK4,sK3)
% 51.28/7.00      | ~ v1_pre_topc(X0_57)
% 51.28/7.00      | ~ v2_pre_topc(X0_57)
% 51.28/7.00      | ~ l1_pre_topc(X0_57)
% 51.28/7.00      | sK2(sK3,sK4) = sK0(sK3,sK4,X0_57)
% 51.28/7.00      | k8_tmap_1(sK3,sK4) = X0_57
% 51.28/7.00      | sK4 != sK4 ),
% 51.28/7.00      inference(resolution,[status(thm)],[c_3900,c_7948]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_13044,plain,
% 51.28/7.00      ( v1_tsep_1(sK4,sK3)
% 51.28/7.00      | ~ v1_pre_topc(X0_57)
% 51.28/7.00      | ~ v2_pre_topc(X0_57)
% 51.28/7.00      | ~ l1_pre_topc(X0_57)
% 51.28/7.00      | sK2(sK3,sK4) = sK0(sK3,sK4,X0_57)
% 51.28/7.00      | k8_tmap_1(sK3,sK4) = X0_57 ),
% 51.28/7.00      inference(equality_resolution_simp,[status(thm)],[c_13039]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_51238,plain,
% 51.28/7.00      ( v1_tsep_1(sK4,sK3)
% 51.28/7.00      | ~ v1_pre_topc(k6_tmap_1(X0_57,sK2(sK3,sK4)))
% 51.28/7.00      | ~ v2_pre_topc(k6_tmap_1(X0_57,sK2(sK3,sK4)))
% 51.28/7.00      | ~ l1_pre_topc(k6_tmap_1(X0_57,sK2(sK3,sK4)))
% 51.28/7.00      | X0_57 != sK3
% 51.28/7.00      | k8_tmap_1(sK3,sK4) = k6_tmap_1(X0_57,sK2(sK3,sK4)) ),
% 51.28/7.00      inference(resolution,[status(thm)],[c_50348,c_13044]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_51239,plain,
% 51.28/7.00      ( X0_57 != sK3
% 51.28/7.00      | k8_tmap_1(sK3,sK4) = k6_tmap_1(X0_57,sK2(sK3,sK4))
% 51.28/7.00      | v1_tsep_1(sK4,sK3) = iProver_top
% 51.28/7.00      | v1_pre_topc(k6_tmap_1(X0_57,sK2(sK3,sK4))) != iProver_top
% 51.28/7.00      | v2_pre_topc(k6_tmap_1(X0_57,sK2(sK3,sK4))) != iProver_top
% 51.28/7.00      | l1_pre_topc(k6_tmap_1(X0_57,sK2(sK3,sK4))) != iProver_top ),
% 51.28/7.00      inference(predicate_to_equality,[status(thm)],[c_51238]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_51241,plain,
% 51.28/7.00      ( k8_tmap_1(sK3,sK4) = k6_tmap_1(sK3,sK2(sK3,sK4))
% 51.28/7.00      | sK3 != sK3
% 51.28/7.00      | v1_tsep_1(sK4,sK3) = iProver_top
% 51.28/7.00      | v1_pre_topc(k6_tmap_1(sK3,sK2(sK3,sK4))) != iProver_top
% 51.28/7.00      | v2_pre_topc(k6_tmap_1(sK3,sK2(sK3,sK4))) != iProver_top
% 51.28/7.00      | l1_pre_topc(k6_tmap_1(sK3,sK2(sK3,sK4))) != iProver_top ),
% 51.28/7.00      inference(instantiation,[status(thm)],[c_51239]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_106317,plain,
% 51.28/7.00      ( k6_tmap_1(sK3,sK2(sK3,sK4)) = k8_tmap_1(sK3,sK4)
% 51.28/7.00      | v1_tsep_1(sK4,sK3) = iProver_top ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_9445,c_51,c_52,c_53,c_3985,c_6195,c_6196,c_6197,
% 51.28/7.00                 c_6492,c_6493,c_51241]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_6409,plain,
% 51.28/7.00      ( k7_tmap_1(sK3,sK2(sK3,sK4)) = k6_partfun1(u1_struct_0(sK3))
% 51.28/7.00      | v1_tsep_1(sK4,sK3) = iProver_top
% 51.28/7.00      | v2_pre_topc(sK3) != iProver_top
% 51.28/7.00      | v2_struct_0(sK3) = iProver_top
% 51.28/7.00      | l1_pre_topc(sK3) != iProver_top ),
% 51.28/7.00      inference(superposition,[status(thm)],[c_4958,c_4931]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_8366,plain,
% 51.28/7.00      ( v1_tsep_1(sK4,sK3) = iProver_top
% 51.28/7.00      | k7_tmap_1(sK3,sK2(sK3,sK4)) = k6_partfun1(u1_struct_0(sK3)) ),
% 51.28/7.00      inference(global_propositional_subsumption,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_6409,c_51,c_52,c_53]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_8367,plain,
% 51.28/7.00      ( k7_tmap_1(sK3,sK2(sK3,sK4)) = k6_partfun1(u1_struct_0(sK3))
% 51.28/7.00      | v1_tsep_1(sK4,sK3) = iProver_top ),
% 51.28/7.00      inference(renaming,[status(thm)],[c_8366]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(c_1725,plain,
% 51.28/7.00      ( v1_tsep_1(sK4,sK3) = iProver_top
% 51.28/7.00      | m1_subset_1(sK2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 51.28/7.00      | l1_pre_topc(sK3) != iProver_top ),
% 51.28/7.00      inference(predicate_to_equality,[status(thm)],[c_1724]) ).
% 51.28/7.00  
% 51.28/7.00  cnf(contradiction,plain,
% 51.28/7.00      ( $false ),
% 51.28/7.00      inference(minisat,
% 51.28/7.00                [status(thm)],
% 51.28/7.00                [c_161701,c_161543,c_117712,c_106317,c_31037,c_8367,
% 51.28/7.00                 c_1725,c_1692,c_53,c_52,c_51]) ).
% 51.28/7.00  
% 51.28/7.00  
% 51.28/7.00  % SZS output end CNFRefutation for theBenchmark.p
% 51.28/7.00  
% 51.28/7.00  ------                               Statistics
% 51.28/7.00  
% 51.28/7.00  ------ Selected
% 51.28/7.00  
% 51.28/7.00  total_time:                             6.059
% 51.28/7.00  
%------------------------------------------------------------------------------
