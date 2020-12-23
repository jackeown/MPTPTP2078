%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:14 EST 2020

% Result     : Theorem 3.01s
% Output     : CNFRefutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :  283 (7322 expanded)
%              Number of clauses        :  182 (1509 expanded)
%              Number of leaves         :   21 (1686 expanded)
%              Depth                    :   34
%              Number of atoms          : 1453 (81237 expanded)
%              Number of equality atoms :  293 (2079 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

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

fof(f91,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k9_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f43])).

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
     => ( ( ~ m1_subset_1(k9_tmap_1(X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,sK5)))))
          | ~ v5_pre_topc(k9_tmap_1(X0,sK5),X0,k8_tmap_1(X0,sK5))
          | ~ v1_funct_2(k9_tmap_1(X0,sK5),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,sK5)))
          | ~ v1_funct_1(k9_tmap_1(X0,sK5))
          | ~ m1_pre_topc(sK5,X0)
          | ~ v1_tsep_1(sK5,X0) )
        & ( ( m1_subset_1(k9_tmap_1(X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,sK5)))))
            & v5_pre_topc(k9_tmap_1(X0,sK5),X0,k8_tmap_1(X0,sK5))
            & v1_funct_2(k9_tmap_1(X0,sK5),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,sK5)))
            & v1_funct_1(k9_tmap_1(X0,sK5)) )
          | ( m1_pre_topc(sK5,X0)
            & v1_tsep_1(sK5,X0) ) )
        & m1_pre_topc(sK5,X0) ) ) ),
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
          ( ( ~ m1_subset_1(k9_tmap_1(sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,X1)))))
            | ~ v5_pre_topc(k9_tmap_1(sK4,X1),sK4,k8_tmap_1(sK4,X1))
            | ~ v1_funct_2(k9_tmap_1(sK4,X1),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,X1)))
            | ~ v1_funct_1(k9_tmap_1(sK4,X1))
            | ~ m1_pre_topc(X1,sK4)
            | ~ v1_tsep_1(X1,sK4) )
          & ( ( m1_subset_1(k9_tmap_1(sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,X1)))))
              & v5_pre_topc(k9_tmap_1(sK4,X1),sK4,k8_tmap_1(sK4,X1))
              & v1_funct_2(k9_tmap_1(sK4,X1),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,X1)))
              & v1_funct_1(k9_tmap_1(sK4,X1)) )
            | ( m1_pre_topc(X1,sK4)
              & v1_tsep_1(X1,sK4) ) )
          & m1_pre_topc(X1,sK4) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,
    ( ( ~ m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
      | ~ v5_pre_topc(k9_tmap_1(sK4,sK5),sK4,k8_tmap_1(sK4,sK5))
      | ~ v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))
      | ~ v1_funct_1(k9_tmap_1(sK4,sK5))
      | ~ m1_pre_topc(sK5,sK4)
      | ~ v1_tsep_1(sK5,sK4) )
    & ( ( m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
        & v5_pre_topc(k9_tmap_1(sK4,sK5),sK4,k8_tmap_1(sK4,sK5))
        & v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))
        & v1_funct_1(k9_tmap_1(sK4,sK5)) )
      | ( m1_pre_topc(sK5,sK4)
        & v1_tsep_1(sK5,sK4) ) )
    & m1_pre_topc(sK5,sK4)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f62,f64,f63])).

fof(f113,plain,
    ( m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
    | m1_pre_topc(sK5,sK4) ),
    inference(cnf_transformation,[],[f65])).

fof(f105,plain,(
    m1_pre_topc(sK5,sK4) ),
    inference(cnf_transformation,[],[f65])).

fof(f102,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f65])).

fof(f103,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f65])).

fof(f104,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f65])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

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

fof(f100,plain,(
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

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

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

fof(f86,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f110,plain,
    ( v5_pre_topc(k9_tmap_1(sK4,sK5),sK4,k8_tmap_1(sK4,sK5))
    | v1_tsep_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f65])).

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
    inference(ennf_transformation,[],[f8])).

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
     => ( ~ v3_pre_topc(sK3(X0,X1),X0)
        & u1_struct_0(X1) = sK3(X0,X1)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tsep_1(X1,X0)
              | ( ~ v3_pre_topc(sK3(X0,X1),X0)
                & u1_struct_0(X1) = sK3(X0,X1)
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tsep_1(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f56,f57])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(sK3(X0,X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f101,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f93,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f98,plain,(
    ! [X0,X1] :
      ( v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f114,plain,
    ( ~ m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
    | ~ v5_pre_topc(k9_tmap_1(sK4,sK5),sK4,k8_tmap_1(sK4,sK5))
    | ~ v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))
    | ~ v1_funct_1(k9_tmap_1(sK4,sK5))
    | ~ m1_pre_topc(sK5,sK4)
    | ~ v1_tsep_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f65])).

fof(f81,plain,(
    ! [X0,X3,X1] :
      ( v3_pre_topc(X3,X0)
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f120,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f81])).

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
    inference(ennf_transformation,[],[f6])).

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
     => ( k6_tmap_1(X0,sK1(X0,X1,X2)) != X2
        & u1_struct_0(X1) = sK1(X0,X1,X2)
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ( k6_tmap_1(X0,sK1(X0,X1,X2)) != X2
                    & u1_struct_0(X1) = sK1(X0,X1,X2)
                    & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f48,f49])).

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
    inference(cnf_transformation,[],[f50])).

fof(f116,plain,(
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

fof(f117,plain,(
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
    inference(equality_resolution,[],[f116])).

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

fof(f33,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

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

fof(f88,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f89,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f90,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

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

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

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

fof(f94,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

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
     => ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f4])).

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
    inference(flattening,[],[f21])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f70,plain,(
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
    inference(cnf_transformation,[],[f46])).

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
    inference(ennf_transformation,[],[f7])).

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
     => ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2(X0,X1,X2))),X2,k7_tmap_1(X0,sK2(X0,X1,X2)))
        & u1_struct_0(X1) = sK2(X0,X1,X2)
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k9_tmap_1(X0,X1) = X2
                  | ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2(X0,X1,X2))),X2,k7_tmap_1(X0,sK2(X0,X1,X2)))
                    & u1_struct_0(X1) = sK2(X0,X1,X2)
                    & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f52,f53])).

fof(f77,plain,(
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

fof(f118,plain,(
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
    inference(equality_resolution,[],[f77])).

fof(f119,plain,(
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
    inference(equality_resolution,[],[f118])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f66,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | u1_struct_0(X1) = sK3(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v1_xboole_0(sK0(X0))
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_xboole_0(sK0(X0))
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f44])).

fof(f68,plain,(
    ! [X0] :
      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_27,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k9_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_37,negated_conjecture,
    ( m1_pre_topc(sK5,sK4)
    | m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))))) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_45,negated_conjecture,
    ( m1_pre_topc(sK5,sK4) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_292,negated_conjecture,
    ( m1_pre_topc(sK5,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_37,c_45])).

cnf(c_1230,plain,
    ( ~ v2_pre_topc(X0)
    | v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_292])).

cnf(c_1231,plain,
    ( ~ v2_pre_topc(sK4)
    | v1_funct_1(k9_tmap_1(sK4,sK5))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_1230])).

cnf(c_48,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_47,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_46,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1233,plain,
    ( v1_funct_1(k9_tmap_1(sK4,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1231,c_48,c_47,c_46])).

cnf(c_30,plain,
    ( ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
    | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | v3_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k7_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_20,plain,
    ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_319,plain,
    ( ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
    | v3_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k7_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_30,c_20])).

cnf(c_40,negated_conjecture,
    ( v5_pre_topc(k9_tmap_1(sK4,sK5),sK4,k8_tmap_1(sK4,sK5))
    | v1_tsep_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_629,plain,
    ( v3_pre_topc(X0,X1)
    | v1_tsep_1(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(k7_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(X1,X0) != k8_tmap_1(sK4,sK5)
    | k7_tmap_1(X1,X0) != k9_tmap_1(sK4,sK5)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_319,c_40])).

cnf(c_630,plain,
    ( v3_pre_topc(X0,sK4)
    | v1_tsep_1(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k7_tmap_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X0)))))
    | ~ v2_pre_topc(sK4)
    | ~ v1_funct_1(k7_tmap_1(sK4,X0))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | k6_tmap_1(sK4,X0) != k8_tmap_1(sK4,sK5)
    | k7_tmap_1(sK4,X0) != k9_tmap_1(sK4,sK5) ),
    inference(unflattening,[status(thm)],[c_629])).

cnf(c_634,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_tsep_1(sK5,sK4)
    | v3_pre_topc(X0,sK4)
    | ~ v1_funct_1(k7_tmap_1(sK4,X0))
    | k6_tmap_1(sK4,X0) != k8_tmap_1(sK4,sK5)
    | k7_tmap_1(sK4,X0) != k9_tmap_1(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_630,c_48,c_47,c_46])).

cnf(c_635,plain,
    ( v3_pre_topc(X0,sK4)
    | v1_tsep_1(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k7_tmap_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X0)))))
    | ~ v1_funct_1(k7_tmap_1(sK4,X0))
    | k6_tmap_1(sK4,X0) != k8_tmap_1(sK4,sK5)
    | k7_tmap_1(sK4,X0) != k9_tmap_1(sK4,sK5) ),
    inference(renaming,[status(thm)],[c_634])).

cnf(c_15,plain,
    ( ~ v3_pre_topc(sK3(X0,X1),X0)
    | v1_tsep_1(X1,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1154,plain,
    ( ~ v3_pre_topc(sK3(X0,X1),X0)
    | v1_tsep_1(X1,X0)
    | ~ l1_pre_topc(X0)
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_292])).

cnf(c_1155,plain,
    ( ~ v3_pre_topc(sK3(sK4,sK5),sK4)
    | v1_tsep_1(sK5,sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_1154])).

cnf(c_1157,plain,
    ( v1_tsep_1(sK5,sK4)
    | ~ v3_pre_topc(sK3(sK4,sK5),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1155,c_46])).

cnf(c_1158,plain,
    ( ~ v3_pre_topc(sK3(sK4,sK5),sK4)
    | v1_tsep_1(sK5,sK4) ),
    inference(renaming,[status(thm)],[c_1157])).

cnf(c_1536,plain,
    ( v1_tsep_1(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k7_tmap_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X0)))))
    | ~ v1_funct_1(k7_tmap_1(sK4,X0))
    | sK3(sK4,sK5) != X0
    | k6_tmap_1(sK4,X0) != k8_tmap_1(sK4,sK5)
    | k7_tmap_1(sK4,X0) != k9_tmap_1(sK4,sK5)
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_635,c_1158])).

cnf(c_1537,plain,
    ( v1_tsep_1(sK5,sK4)
    | ~ m1_subset_1(sK3(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k7_tmap_1(sK4,sK3(sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK3(sK4,sK5))))))
    | ~ v1_funct_1(k7_tmap_1(sK4,sK3(sK4,sK5)))
    | k6_tmap_1(sK4,sK3(sK4,sK5)) != k8_tmap_1(sK4,sK5)
    | k7_tmap_1(sK4,sK3(sK4,sK5)) != k9_tmap_1(sK4,sK5) ),
    inference(unflattening,[status(thm)],[c_1536])).

cnf(c_17,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | m1_subset_1(sK3(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1289,plain,
    ( v1_tsep_1(X0,X1)
    | m1_subset_1(sK3(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK5 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_292])).

cnf(c_1290,plain,
    ( v1_tsep_1(sK5,sK4)
    | m1_subset_1(sK3(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_1289])).

cnf(c_1539,plain,
    ( v1_tsep_1(sK5,sK4)
    | ~ m1_subset_1(k7_tmap_1(sK4,sK3(sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK3(sK4,sK5))))))
    | ~ v1_funct_1(k7_tmap_1(sK4,sK3(sK4,sK5)))
    | k6_tmap_1(sK4,sK3(sK4,sK5)) != k8_tmap_1(sK4,sK5)
    | k7_tmap_1(sK4,sK3(sK4,sK5)) != k9_tmap_1(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1537,c_46,c_1290])).

cnf(c_1962,plain,
    ( v1_tsep_1(sK5,sK4)
    | ~ m1_subset_1(k7_tmap_1(sK4,sK3(sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK3(sK4,sK5))))))
    | k6_tmap_1(sK4,sK3(sK4,sK5)) != k8_tmap_1(sK4,sK5)
    | k7_tmap_1(sK4,sK3(sK4,sK5)) != k9_tmap_1(sK4,sK5) ),
    inference(resolution_lifted,[status(thm)],[c_1233,c_1539])).

cnf(c_2541,plain,
    ( v1_tsep_1(sK5,sK4)
    | ~ m1_subset_1(k7_tmap_1(sK4,sK3(sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK3(sK4,sK5))))))
    | k7_tmap_1(sK4,sK3(sK4,sK5)) != k9_tmap_1(sK4,sK5)
    | k6_tmap_1(sK4,sK3(sK4,sK5)) != k8_tmap_1(sK4,sK5) ),
    inference(subtyping,[status(esa)],[c_1962])).

cnf(c_3050,plain,
    ( k7_tmap_1(sK4,sK3(sK4,sK5)) != k9_tmap_1(sK4,sK5)
    | k6_tmap_1(sK4,sK3(sK4,sK5)) != k8_tmap_1(sK4,sK5)
    | v1_tsep_1(sK5,sK4) = iProver_top
    | m1_subset_1(k7_tmap_1(sK4,sK3(sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK3(sK4,sK5)))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2541])).

cnf(c_51,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_35,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1217,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK5 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_292])).

cnf(c_1218,plain,
    ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_1217])).

cnf(c_1219,plain,
    ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1218])).

cnf(c_25,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(k9_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X0)))))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1243,plain,
    ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_292])).

cnf(c_1244,plain,
    ( m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_1243])).

cnf(c_1246,plain,
    ( m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1244,c_48,c_47,c_46])).

cnf(c_26,plain,
    ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1143,plain,
    ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_292])).

cnf(c_1144,plain,
    ( v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_1143])).

cnf(c_1146,plain,
    ( v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1144,c_48,c_47,c_46])).

cnf(c_32,plain,
    ( v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
    | ~ v3_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_36,negated_conjecture,
    ( ~ v5_pre_topc(k9_tmap_1(sK4,sK5),sK4,k8_tmap_1(sK4,sK5))
    | ~ v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))
    | ~ v1_tsep_1(sK5,sK4)
    | ~ m1_pre_topc(sK5,sK4)
    | ~ m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
    | ~ v1_funct_1(k9_tmap_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_297,plain,
    ( ~ v1_tsep_1(sK5,sK4)
    | ~ v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))
    | ~ v5_pre_topc(k9_tmap_1(sK4,sK5),sK4,k8_tmap_1(sK4,sK5))
    | ~ m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
    | ~ v1_funct_1(k9_tmap_1(sK4,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_36,c_45])).

cnf(c_298,negated_conjecture,
    ( ~ v5_pre_topc(k9_tmap_1(sK4,sK5),sK4,k8_tmap_1(sK4,sK5))
    | ~ v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))
    | ~ v1_tsep_1(sK5,sK4)
    | ~ m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
    | ~ v1_funct_1(k9_tmap_1(sK4,sK5)) ),
    inference(renaming,[status(thm)],[c_297])).

cnf(c_593,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))
    | ~ v3_pre_topc(X0,X1)
    | ~ v1_tsep_1(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(k9_tmap_1(sK4,sK5))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(X1,X0) != k8_tmap_1(sK4,sK5)
    | k7_tmap_1(X1,X0) != k9_tmap_1(sK4,sK5)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_298])).

cnf(c_594,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))
    | ~ v3_pre_topc(X0,sK4)
    | ~ v1_tsep_1(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
    | ~ v2_pre_topc(sK4)
    | ~ v1_funct_1(k9_tmap_1(sK4,sK5))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | k6_tmap_1(sK4,X0) != k8_tmap_1(sK4,sK5)
    | k7_tmap_1(sK4,X0) != k9_tmap_1(sK4,sK5) ),
    inference(unflattening,[status(thm)],[c_593])).

cnf(c_598,plain,
    ( ~ m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_tsep_1(sK5,sK4)
    | ~ v3_pre_topc(X0,sK4)
    | ~ v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))
    | ~ v1_funct_1(k9_tmap_1(sK4,sK5))
    | k6_tmap_1(sK4,X0) != k8_tmap_1(sK4,sK5)
    | k7_tmap_1(sK4,X0) != k9_tmap_1(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_594,c_48,c_47,c_46])).

cnf(c_599,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))
    | ~ v3_pre_topc(X0,sK4)
    | ~ v1_tsep_1(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
    | ~ v1_funct_1(k9_tmap_1(sK4,sK5))
    | k6_tmap_1(sK4,X0) != k8_tmap_1(sK4,sK5)
    | k7_tmap_1(sK4,X0) != k9_tmap_1(sK4,sK5) ),
    inference(renaming,[status(thm)],[c_598])).

cnf(c_1454,plain,
    ( ~ v3_pre_topc(X0,sK4)
    | ~ v1_tsep_1(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
    | ~ v1_funct_1(k9_tmap_1(sK4,sK5))
    | k6_tmap_1(sK4,X0) != k8_tmap_1(sK4,sK5)
    | k7_tmap_1(sK4,X0) != k9_tmap_1(sK4,sK5) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1146,c_599])).

cnf(c_1475,plain,
    ( ~ v3_pre_topc(X0,sK4)
    | ~ v1_tsep_1(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
    | k6_tmap_1(sK4,X0) != k8_tmap_1(sK4,sK5)
    | k7_tmap_1(sK4,X0) != k9_tmap_1(sK4,sK5) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1233,c_1454])).

cnf(c_1481,plain,
    ( ~ v3_pre_topc(X0,sK4)
    | ~ v1_tsep_1(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | k6_tmap_1(sK4,X0) != k8_tmap_1(sK4,sK5)
    | k7_tmap_1(sK4,X0) != k9_tmap_1(sK4,sK5) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1246,c_1475])).

cnf(c_18,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_337,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_35])).

cnf(c_338,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_337])).

cnf(c_1203,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK5 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_338,c_292])).

cnf(c_1204,plain,
    ( v3_pre_topc(u1_struct_0(sK5),sK4)
    | ~ v1_tsep_1(sK5,sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_1203])).

cnf(c_1206,plain,
    ( ~ v1_tsep_1(sK5,sK4)
    | v3_pre_topc(u1_struct_0(sK5),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1204,c_46])).

cnf(c_1207,plain,
    ( v3_pre_topc(u1_struct_0(sK5),sK4)
    | ~ v1_tsep_1(sK5,sK4) ),
    inference(renaming,[status(thm)],[c_1206])).

cnf(c_1559,plain,
    ( ~ v1_tsep_1(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | k6_tmap_1(sK4,X0) != k8_tmap_1(sK4,sK5)
    | k7_tmap_1(sK4,X0) != k9_tmap_1(sK4,sK5)
    | u1_struct_0(sK5) != X0
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_1481,c_1207])).

cnf(c_1560,plain,
    ( ~ v1_tsep_1(sK5,sK4)
    | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | k6_tmap_1(sK4,u1_struct_0(sK5)) != k8_tmap_1(sK4,sK5)
    | k7_tmap_1(sK4,u1_struct_0(sK5)) != k9_tmap_1(sK4,sK5) ),
    inference(unflattening,[status(thm)],[c_1559])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(k8_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(k8_tmap_1(X1,X0))
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_24,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_23,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k8_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_22,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_357,plain,
    ( ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_35,c_24,c_23,c_22])).

cnf(c_358,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(renaming,[status(thm)],[c_357])).

cnf(c_1195,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k6_tmap_1(X0,u1_struct_0(X1)) = k8_tmap_1(X0,X1)
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_358,c_292])).

cnf(c_1196,plain,
    ( ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | k6_tmap_1(sK4,u1_struct_0(sK5)) = k8_tmap_1(sK4,sK5) ),
    inference(unflattening,[status(thm)],[c_1195])).

cnf(c_1562,plain,
    ( ~ v1_tsep_1(sK5,sK4)
    | k7_tmap_1(sK4,u1_struct_0(sK5)) != k9_tmap_1(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1560,c_48,c_47,c_46,c_1196,c_1218])).

cnf(c_2555,plain,
    ( ~ v1_tsep_1(sK5,sK4)
    | k7_tmap_1(sK4,u1_struct_0(sK5)) != k9_tmap_1(sK4,sK5) ),
    inference(subtyping,[status(esa)],[c_1562])).

cnf(c_2626,plain,
    ( k7_tmap_1(sK4,u1_struct_0(sK5)) != k9_tmap_1(sK4,sK5)
    | v1_tsep_1(sK5,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2555])).

cnf(c_2654,plain,
    ( k7_tmap_1(sK4,sK3(sK4,sK5)) != k9_tmap_1(sK4,sK5)
    | k6_tmap_1(sK4,sK3(sK4,sK5)) != k8_tmap_1(sK4,sK5)
    | v1_tsep_1(sK5,sK4) = iProver_top
    | m1_subset_1(k7_tmap_1(sK4,sK3(sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK3(sK4,sK5)))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2541])).

cnf(c_1198,plain,
    ( k6_tmap_1(sK4,u1_struct_0(sK5)) = k8_tmap_1(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1196,c_48,c_47,c_46])).

cnf(c_2563,plain,
    ( k6_tmap_1(sK4,u1_struct_0(sK5)) = k8_tmap_1(sK4,sK5) ),
    inference(subtyping,[status(esa)],[c_1198])).

cnf(c_1637,plain,
    ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_48])).

cnf(c_1638,plain,
    ( v1_funct_2(k7_tmap_1(sK4,X0),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_1637])).

cnf(c_1642,plain,
    ( v1_funct_2(k7_tmap_1(sK4,X0),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1638,c_47,c_46])).

cnf(c_2553,plain,
    ( v1_funct_2(k7_tmap_1(sK4,X0_59),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X0_59)))
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(subtyping,[status(esa)],[c_1642])).

cnf(c_3038,plain,
    ( v1_funct_2(k7_tmap_1(sK4,X0_59),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X0_59))) = iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2553])).

cnf(c_3757,plain,
    ( v1_funct_2(k7_tmap_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))) = iProver_top
    | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2563,c_3038])).

cnf(c_1220,plain,
    ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1218,c_46])).

cnf(c_2562,plain,
    ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(subtyping,[status(esa)],[c_1220])).

cnf(c_3029,plain,
    ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2562])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1655,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_48])).

cnf(c_1656,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4)
    | u1_struct_0(k6_tmap_1(sK4,X0)) = u1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1655])).

cnf(c_1660,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | u1_struct_0(k6_tmap_1(sK4,X0)) = u1_struct_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1656,c_47,c_46])).

cnf(c_2552,plain,
    ( ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK4)))
    | u1_struct_0(k6_tmap_1(sK4,X0_59)) = u1_struct_0(sK4) ),
    inference(subtyping,[status(esa)],[c_1660])).

cnf(c_3039,plain,
    ( u1_struct_0(k6_tmap_1(sK4,X0_59)) = u1_struct_0(sK4)
    | m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2552])).

cnf(c_3551,plain,
    ( u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5))) = u1_struct_0(sK4) ),
    inference(superposition,[status(thm)],[c_3029,c_3039])).

cnf(c_3558,plain,
    ( u1_struct_0(k8_tmap_1(sK4,sK5)) = u1_struct_0(sK4) ),
    inference(light_normalisation,[status(thm)],[c_3551,c_2563])).

cnf(c_3758,plain,
    ( v1_funct_2(k7_tmap_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK4),u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3757,c_3558])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1709,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_48])).

cnf(c_1710,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(k7_tmap_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X0)))))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_1709])).

cnf(c_1714,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(k7_tmap_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X0))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1710,c_47,c_46])).

cnf(c_2549,plain,
    ( ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(k7_tmap_1(sK4,X0_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X0_59))))) ),
    inference(subtyping,[status(esa)],[c_1714])).

cnf(c_3042,plain,
    ( m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK4,X0_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X0_59))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2549])).

cnf(c_3818,plain,
    ( m1_subset_1(k7_tmap_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))))) = iProver_top
    | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2563,c_3042])).

cnf(c_3819,plain,
    ( m1_subset_1(k7_tmap_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) = iProver_top
    | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3818,c_3558])).

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
    inference(cnf_transformation,[],[f70])).

cnf(c_14,plain,
    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
    | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_347,plain,
    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_26])).

cnf(c_1123,plain,
    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
    | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_347,c_292])).

cnf(c_1124,plain,
    ( r1_funct_2(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5))),k9_tmap_1(sK4,sK5),k7_tmap_1(sK4,u1_struct_0(sK5)))
    | ~ m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
    | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v2_pre_topc(sK4)
    | ~ v1_funct_1(k9_tmap_1(sK4,sK5))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_1123])).

cnf(c_1126,plain,
    ( ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
    | r1_funct_2(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5))),k9_tmap_1(sK4,sK5),k7_tmap_1(sK4,u1_struct_0(sK5)))
    | ~ v1_funct_1(k9_tmap_1(sK4,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1124,c_48,c_47,c_46])).

cnf(c_1127,plain,
    ( r1_funct_2(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5))),k9_tmap_1(sK4,sK5),k7_tmap_1(sK4,u1_struct_0(sK5)))
    | ~ m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
    | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_funct_1(k9_tmap_1(sK4,sK5)) ),
    inference(renaming,[status(thm)],[c_1126])).

cnf(c_1227,plain,
    ( r1_funct_2(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5))),k9_tmap_1(sK4,sK5),k7_tmap_1(sK4,u1_struct_0(sK5)))
    | ~ m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
    | ~ v1_funct_1(k9_tmap_1(sK4,sK5)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1220,c_1127])).

cnf(c_1240,plain,
    ( r1_funct_2(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5))),k9_tmap_1(sK4,sK5),k7_tmap_1(sK4,u1_struct_0(sK5)))
    | ~ m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1233,c_1227])).

cnf(c_1253,plain,
    ( r1_funct_2(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5))),k9_tmap_1(sK4,sK5),k7_tmap_1(sK4,u1_struct_0(sK5))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1246,c_1240])).

cnf(c_1836,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X5)
    | X3 = X0
    | k9_tmap_1(sK4,sK5) != X0
    | k7_tmap_1(sK4,u1_struct_0(sK5)) != X3
    | u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5))) != X5
    | u1_struct_0(k8_tmap_1(sK4,sK5)) != X2
    | u1_struct_0(sK4) != X4
    | u1_struct_0(sK4) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_1253])).

cnf(c_1837,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))
    | ~ v1_funct_2(k7_tmap_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5))))
    | ~ m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
    | ~ m1_subset_1(k7_tmap_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5))))))
    | ~ v1_funct_1(k9_tmap_1(sK4,sK5))
    | ~ v1_funct_1(k7_tmap_1(sK4,u1_struct_0(sK5)))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK4,sK5)))
    | k7_tmap_1(sK4,u1_struct_0(sK5)) = k9_tmap_1(sK4,sK5) ),
    inference(unflattening,[status(thm)],[c_1836])).

cnf(c_1839,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5))))))
    | ~ v1_funct_2(k7_tmap_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5))))
    | ~ v1_funct_1(k7_tmap_1(sK4,u1_struct_0(sK5)))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK4,sK5)))
    | k7_tmap_1(sK4,u1_struct_0(sK5)) = k9_tmap_1(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1837,c_48,c_47,c_46,c_1144,c_1231,c_1244])).

cnf(c_1840,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5))))
    | ~ m1_subset_1(k7_tmap_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5))))))
    | ~ v1_funct_1(k7_tmap_1(sK4,u1_struct_0(sK5)))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK4,sK5)))
    | k7_tmap_1(sK4,u1_struct_0(sK5)) = k9_tmap_1(sK4,sK5) ),
    inference(renaming,[status(thm)],[c_1839])).

cnf(c_2542,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5))))
    | ~ m1_subset_1(k7_tmap_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5))))))
    | ~ v1_funct_1(k7_tmap_1(sK4,u1_struct_0(sK5)))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK4,sK5)))
    | k7_tmap_1(sK4,u1_struct_0(sK5)) = k9_tmap_1(sK4,sK5) ),
    inference(subtyping,[status(esa)],[c_1840])).

cnf(c_3049,plain,
    ( k7_tmap_1(sK4,u1_struct_0(sK5)) = k9_tmap_1(sK4,sK5)
    | v1_funct_2(k7_tmap_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5)))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5)))))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK4,u1_struct_0(sK5))) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5)))) = iProver_top
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2542])).

cnf(c_3135,plain,
    ( k7_tmap_1(sK4,u1_struct_0(sK5)) = k9_tmap_1(sK4,sK5)
    | v1_funct_2(k7_tmap_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK4,u1_struct_0(sK5))) != iProver_top
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK4,sK5))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3049,c_2563])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k7_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1691,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k7_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_48])).

cnf(c_1692,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v2_pre_topc(sK4)
    | v1_funct_1(k7_tmap_1(sK4,X0))
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_1691])).

cnf(c_1696,plain,
    ( v1_funct_1(k7_tmap_1(sK4,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1692,c_47,c_46])).

cnf(c_1697,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_funct_1(k7_tmap_1(sK4,X0)) ),
    inference(renaming,[status(thm)],[c_1696])).

cnf(c_2550,plain,
    ( ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_funct_1(k7_tmap_1(sK4,X0_59)) ),
    inference(subtyping,[status(esa)],[c_1697])).

cnf(c_3226,plain,
    ( ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_funct_1(k7_tmap_1(sK4,u1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_2550])).

cnf(c_3227,plain,
    ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK4,u1_struct_0(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3226])).

cnf(c_4071,plain,
    ( m1_subset_1(k7_tmap_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))))) != iProver_top
    | v1_funct_2(k7_tmap_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))) != iProver_top
    | k7_tmap_1(sK4,u1_struct_0(sK5)) = k9_tmap_1(sK4,sK5)
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK4,sK5))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3135,c_51,c_1219,c_3227])).

cnf(c_4072,plain,
    ( k7_tmap_1(sK4,u1_struct_0(sK5)) = k9_tmap_1(sK4,sK5)
    | v1_funct_2(k7_tmap_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))))) != iProver_top
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK4,sK5))) = iProver_top ),
    inference(renaming,[status(thm)],[c_4071])).

cnf(c_4075,plain,
    ( k7_tmap_1(sK4,u1_struct_0(sK5)) = k9_tmap_1(sK4,sK5)
    | v1_funct_2(k7_tmap_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK4),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k7_tmap_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4072,c_3558])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_573,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_0,c_1])).

cnf(c_1626,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_573,c_48])).

cnf(c_1627,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4))
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_1626])).

cnf(c_165,plain,
    ( v2_struct_0(sK4)
    | ~ v1_xboole_0(u1_struct_0(sK4))
    | ~ l1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_168,plain,
    ( ~ l1_pre_topc(sK4)
    | l1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1629,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1627,c_48,c_46,c_165,c_168])).

cnf(c_2554,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_1629])).

cnf(c_3037,plain,
    ( v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2554])).

cnf(c_4080,plain,
    ( k7_tmap_1(sK4,u1_struct_0(sK5)) = k9_tmap_1(sK4,sK5)
    | v1_funct_2(k7_tmap_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK4),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k7_tmap_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4075,c_3037])).

cnf(c_4789,plain,
    ( k6_tmap_1(sK4,sK3(sK4,sK5)) != k8_tmap_1(sK4,sK5)
    | k7_tmap_1(sK4,sK3(sK4,sK5)) != k9_tmap_1(sK4,sK5)
    | m1_subset_1(k7_tmap_1(sK4,sK3(sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK3(sK4,sK5)))))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3050,c_51,c_1219,c_2626,c_2654,c_3758,c_3819,c_4080])).

cnf(c_4790,plain,
    ( k7_tmap_1(sK4,sK3(sK4,sK5)) != k9_tmap_1(sK4,sK5)
    | k6_tmap_1(sK4,sK3(sK4,sK5)) != k8_tmap_1(sK4,sK5)
    | m1_subset_1(k7_tmap_1(sK4,sK3(sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK3(sK4,sK5)))))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4789])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1727,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_48])).

cnf(c_1728,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4)
    | k7_tmap_1(sK4,X0) = k6_partfun1(u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_1727])).

cnf(c_1732,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | k7_tmap_1(sK4,X0) = k6_partfun1(u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1728,c_47,c_46])).

cnf(c_2548,plain,
    ( ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK4)))
    | k7_tmap_1(sK4,X0_59) = k6_partfun1(u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_1732])).

cnf(c_3043,plain,
    ( k7_tmap_1(sK4,X0_59) = k6_partfun1(u1_struct_0(sK4))
    | m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2548])).

cnf(c_3661,plain,
    ( k7_tmap_1(sK4,u1_struct_0(sK5)) = k6_partfun1(u1_struct_0(sK4)) ),
    inference(superposition,[status(thm)],[c_3029,c_3043])).

cnf(c_16,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK3(X1,X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1303,plain,
    ( v1_tsep_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK3(X1,X0) = u1_struct_0(X0)
    | sK5 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_292])).

cnf(c_1304,plain,
    ( v1_tsep_1(sK5,sK4)
    | ~ l1_pre_topc(sK4)
    | sK3(sK4,sK5) = u1_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_1303])).

cnf(c_1306,plain,
    ( v1_tsep_1(sK5,sK4)
    | sK3(sK4,sK5) = u1_struct_0(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1304,c_46])).

cnf(c_2558,plain,
    ( v1_tsep_1(sK5,sK4)
    | sK3(sK4,sK5) = u1_struct_0(sK5) ),
    inference(subtyping,[status(esa)],[c_1306])).

cnf(c_3033,plain,
    ( sK3(sK4,sK5) = u1_struct_0(sK5)
    | v1_tsep_1(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2558])).

cnf(c_3036,plain,
    ( k7_tmap_1(sK4,u1_struct_0(sK5)) != k9_tmap_1(sK4,sK5)
    | v1_tsep_1(sK5,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2555])).

cnf(c_4373,plain,
    ( v1_tsep_1(sK5,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3036,c_51,c_1219,c_2626,c_3758,c_3819,c_4080])).

cnf(c_4378,plain,
    ( sK3(sK4,sK5) = u1_struct_0(sK5) ),
    inference(superposition,[status(thm)],[c_3033,c_4373])).

cnf(c_4793,plain,
    ( k9_tmap_1(sK4,sK5) != k6_partfun1(u1_struct_0(sK4))
    | k8_tmap_1(sK4,sK5) != k8_tmap_1(sK4,sK5)
    | m1_subset_1(k6_partfun1(u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4790,c_2563,c_3558,c_3661,c_4378])).

cnf(c_4794,plain,
    ( k9_tmap_1(sK4,sK5) != k6_partfun1(u1_struct_0(sK4))
    | m1_subset_1(k6_partfun1(u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4793])).

cnf(c_4153,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5)))))) = iProver_top
    | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3661,c_3042])).

cnf(c_4162,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) = iProver_top
    | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4153,c_2563,c_3558])).

cnf(c_3,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_158,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_160,plain,
    ( m1_subset_1(sK0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_158])).

cnf(c_1765,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_46])).

cnf(c_1766,plain,
    ( m1_subset_1(sK0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(unflattening,[status(thm)],[c_1765])).

cnf(c_2547,plain,
    ( m1_subset_1(sK0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(subtyping,[status(esa)],[c_1766])).

cnf(c_3044,plain,
    ( m1_subset_1(sK0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2547])).

cnf(c_3660,plain,
    ( k7_tmap_1(sK4,sK0(sK4)) = k6_partfun1(u1_struct_0(sK4)) ),
    inference(superposition,[status(thm)],[c_3044,c_3043])).

cnf(c_3971,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK0(sK4)))))) = iProver_top
    | m1_subset_1(sK0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3660,c_3042])).

cnf(c_3550,plain,
    ( u1_struct_0(k6_tmap_1(sK4,sK0(sK4))) = u1_struct_0(sK4) ),
    inference(superposition,[status(thm)],[c_3044,c_3039])).

cnf(c_3980,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) = iProver_top
    | m1_subset_1(sK0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3971,c_3550])).

cnf(c_4253,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4162,c_51,c_160,c_3980])).

cnf(c_4797,plain,
    ( k9_tmap_1(sK4,sK5) != k6_partfun1(u1_struct_0(sK4)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4794,c_4253])).

cnf(c_4082,plain,
    ( k7_tmap_1(sK4,u1_struct_0(sK5)) = k9_tmap_1(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4080,c_51,c_1219,c_3758,c_3819])).

cnf(c_4152,plain,
    ( k9_tmap_1(sK4,sK5) = k6_partfun1(u1_struct_0(sK4)) ),
    inference(demodulation,[status(thm)],[c_3661,c_4082])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4797,c_4152])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:47:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.01/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.01/0.99  
% 3.01/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.01/0.99  
% 3.01/0.99  ------  iProver source info
% 3.01/0.99  
% 3.01/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.01/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.01/0.99  git: non_committed_changes: false
% 3.01/0.99  git: last_make_outside_of_git: false
% 3.01/0.99  
% 3.01/0.99  ------ 
% 3.01/0.99  
% 3.01/0.99  ------ Input Options
% 3.01/0.99  
% 3.01/0.99  --out_options                           all
% 3.01/0.99  --tptp_safe_out                         true
% 3.01/0.99  --problem_path                          ""
% 3.01/0.99  --include_path                          ""
% 3.01/0.99  --clausifier                            res/vclausify_rel
% 3.01/0.99  --clausifier_options                    --mode clausify
% 3.01/0.99  --stdin                                 false
% 3.01/0.99  --stats_out                             all
% 3.01/0.99  
% 3.01/0.99  ------ General Options
% 3.01/0.99  
% 3.01/0.99  --fof                                   false
% 3.01/0.99  --time_out_real                         305.
% 3.01/0.99  --time_out_virtual                      -1.
% 3.01/0.99  --symbol_type_check                     false
% 3.01/0.99  --clausify_out                          false
% 3.01/0.99  --sig_cnt_out                           false
% 3.01/0.99  --trig_cnt_out                          false
% 3.01/0.99  --trig_cnt_out_tolerance                1.
% 3.01/0.99  --trig_cnt_out_sk_spl                   false
% 3.01/0.99  --abstr_cl_out                          false
% 3.01/0.99  
% 3.01/0.99  ------ Global Options
% 3.01/0.99  
% 3.01/0.99  --schedule                              default
% 3.01/0.99  --add_important_lit                     false
% 3.01/0.99  --prop_solver_per_cl                    1000
% 3.01/0.99  --min_unsat_core                        false
% 3.01/0.99  --soft_assumptions                      false
% 3.01/0.99  --soft_lemma_size                       3
% 3.01/0.99  --prop_impl_unit_size                   0
% 3.01/0.99  --prop_impl_unit                        []
% 3.01/0.99  --share_sel_clauses                     true
% 3.01/0.99  --reset_solvers                         false
% 3.01/0.99  --bc_imp_inh                            [conj_cone]
% 3.01/0.99  --conj_cone_tolerance                   3.
% 3.01/0.99  --extra_neg_conj                        none
% 3.01/0.99  --large_theory_mode                     true
% 3.01/0.99  --prolific_symb_bound                   200
% 3.01/0.99  --lt_threshold                          2000
% 3.01/0.99  --clause_weak_htbl                      true
% 3.01/0.99  --gc_record_bc_elim                     false
% 3.01/0.99  
% 3.01/0.99  ------ Preprocessing Options
% 3.01/0.99  
% 3.01/0.99  --preprocessing_flag                    true
% 3.01/0.99  --time_out_prep_mult                    0.1
% 3.01/0.99  --splitting_mode                        input
% 3.01/0.99  --splitting_grd                         true
% 3.01/0.99  --splitting_cvd                         false
% 3.01/0.99  --splitting_cvd_svl                     false
% 3.01/0.99  --splitting_nvd                         32
% 3.01/0.99  --sub_typing                            true
% 3.01/0.99  --prep_gs_sim                           true
% 3.01/0.99  --prep_unflatten                        true
% 3.01/0.99  --prep_res_sim                          true
% 3.01/0.99  --prep_upred                            true
% 3.01/0.99  --prep_sem_filter                       exhaustive
% 3.01/0.99  --prep_sem_filter_out                   false
% 3.01/0.99  --pred_elim                             true
% 3.01/0.99  --res_sim_input                         true
% 3.01/0.99  --eq_ax_congr_red                       true
% 3.01/0.99  --pure_diseq_elim                       true
% 3.01/0.99  --brand_transform                       false
% 3.01/0.99  --non_eq_to_eq                          false
% 3.01/0.99  --prep_def_merge                        true
% 3.01/0.99  --prep_def_merge_prop_impl              false
% 3.01/0.99  --prep_def_merge_mbd                    true
% 3.01/0.99  --prep_def_merge_tr_red                 false
% 3.01/0.99  --prep_def_merge_tr_cl                  false
% 3.01/0.99  --smt_preprocessing                     true
% 3.01/0.99  --smt_ac_axioms                         fast
% 3.01/0.99  --preprocessed_out                      false
% 3.01/0.99  --preprocessed_stats                    false
% 3.01/0.99  
% 3.01/0.99  ------ Abstraction refinement Options
% 3.01/0.99  
% 3.01/0.99  --abstr_ref                             []
% 3.01/0.99  --abstr_ref_prep                        false
% 3.01/0.99  --abstr_ref_until_sat                   false
% 3.01/0.99  --abstr_ref_sig_restrict                funpre
% 3.01/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.01/0.99  --abstr_ref_under                       []
% 3.01/0.99  
% 3.01/0.99  ------ SAT Options
% 3.01/0.99  
% 3.01/0.99  --sat_mode                              false
% 3.01/0.99  --sat_fm_restart_options                ""
% 3.01/0.99  --sat_gr_def                            false
% 3.01/0.99  --sat_epr_types                         true
% 3.01/0.99  --sat_non_cyclic_types                  false
% 3.01/0.99  --sat_finite_models                     false
% 3.01/0.99  --sat_fm_lemmas                         false
% 3.01/0.99  --sat_fm_prep                           false
% 3.01/0.99  --sat_fm_uc_incr                        true
% 3.01/0.99  --sat_out_model                         small
% 3.01/0.99  --sat_out_clauses                       false
% 3.01/0.99  
% 3.01/0.99  ------ QBF Options
% 3.01/0.99  
% 3.01/0.99  --qbf_mode                              false
% 3.01/0.99  --qbf_elim_univ                         false
% 3.01/0.99  --qbf_dom_inst                          none
% 3.01/0.99  --qbf_dom_pre_inst                      false
% 3.01/0.99  --qbf_sk_in                             false
% 3.01/0.99  --qbf_pred_elim                         true
% 3.01/0.99  --qbf_split                             512
% 3.01/0.99  
% 3.01/0.99  ------ BMC1 Options
% 3.01/0.99  
% 3.01/0.99  --bmc1_incremental                      false
% 3.01/0.99  --bmc1_axioms                           reachable_all
% 3.01/0.99  --bmc1_min_bound                        0
% 3.01/0.99  --bmc1_max_bound                        -1
% 3.01/0.99  --bmc1_max_bound_default                -1
% 3.01/0.99  --bmc1_symbol_reachability              true
% 3.01/0.99  --bmc1_property_lemmas                  false
% 3.01/0.99  --bmc1_k_induction                      false
% 3.01/0.99  --bmc1_non_equiv_states                 false
% 3.01/0.99  --bmc1_deadlock                         false
% 3.01/0.99  --bmc1_ucm                              false
% 3.01/0.99  --bmc1_add_unsat_core                   none
% 3.01/0.99  --bmc1_unsat_core_children              false
% 3.01/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.01/0.99  --bmc1_out_stat                         full
% 3.01/0.99  --bmc1_ground_init                      false
% 3.01/0.99  --bmc1_pre_inst_next_state              false
% 3.01/0.99  --bmc1_pre_inst_state                   false
% 3.01/0.99  --bmc1_pre_inst_reach_state             false
% 3.01/0.99  --bmc1_out_unsat_core                   false
% 3.01/0.99  --bmc1_aig_witness_out                  false
% 3.01/0.99  --bmc1_verbose                          false
% 3.01/0.99  --bmc1_dump_clauses_tptp                false
% 3.01/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.01/0.99  --bmc1_dump_file                        -
% 3.01/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.01/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.01/0.99  --bmc1_ucm_extend_mode                  1
% 3.01/0.99  --bmc1_ucm_init_mode                    2
% 3.01/0.99  --bmc1_ucm_cone_mode                    none
% 3.01/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.01/0.99  --bmc1_ucm_relax_model                  4
% 3.01/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.01/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.01/0.99  --bmc1_ucm_layered_model                none
% 3.01/0.99  --bmc1_ucm_max_lemma_size               10
% 3.01/0.99  
% 3.01/0.99  ------ AIG Options
% 3.01/0.99  
% 3.01/0.99  --aig_mode                              false
% 3.01/0.99  
% 3.01/0.99  ------ Instantiation Options
% 3.01/0.99  
% 3.01/0.99  --instantiation_flag                    true
% 3.01/0.99  --inst_sos_flag                         false
% 3.01/0.99  --inst_sos_phase                        true
% 3.01/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.01/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.01/0.99  --inst_lit_sel_side                     num_symb
% 3.01/0.99  --inst_solver_per_active                1400
% 3.01/0.99  --inst_solver_calls_frac                1.
% 3.01/0.99  --inst_passive_queue_type               priority_queues
% 3.01/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.01/0.99  --inst_passive_queues_freq              [25;2]
% 3.01/0.99  --inst_dismatching                      true
% 3.01/0.99  --inst_eager_unprocessed_to_passive     true
% 3.01/0.99  --inst_prop_sim_given                   true
% 3.01/0.99  --inst_prop_sim_new                     false
% 3.01/0.99  --inst_subs_new                         false
% 3.01/0.99  --inst_eq_res_simp                      false
% 3.01/0.99  --inst_subs_given                       false
% 3.01/0.99  --inst_orphan_elimination               true
% 3.01/0.99  --inst_learning_loop_flag               true
% 3.01/0.99  --inst_learning_start                   3000
% 3.01/0.99  --inst_learning_factor                  2
% 3.01/0.99  --inst_start_prop_sim_after_learn       3
% 3.01/0.99  --inst_sel_renew                        solver
% 3.01/0.99  --inst_lit_activity_flag                true
% 3.01/0.99  --inst_restr_to_given                   false
% 3.01/0.99  --inst_activity_threshold               500
% 3.01/0.99  --inst_out_proof                        true
% 3.01/0.99  
% 3.01/0.99  ------ Resolution Options
% 3.01/0.99  
% 3.01/0.99  --resolution_flag                       true
% 3.01/0.99  --res_lit_sel                           adaptive
% 3.01/0.99  --res_lit_sel_side                      none
% 3.01/0.99  --res_ordering                          kbo
% 3.01/0.99  --res_to_prop_solver                    active
% 3.01/0.99  --res_prop_simpl_new                    false
% 3.01/0.99  --res_prop_simpl_given                  true
% 3.01/0.99  --res_passive_queue_type                priority_queues
% 3.01/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.01/0.99  --res_passive_queues_freq               [15;5]
% 3.01/0.99  --res_forward_subs                      full
% 3.01/0.99  --res_backward_subs                     full
% 3.01/0.99  --res_forward_subs_resolution           true
% 3.01/0.99  --res_backward_subs_resolution          true
% 3.01/0.99  --res_orphan_elimination                true
% 3.01/0.99  --res_time_limit                        2.
% 3.01/0.99  --res_out_proof                         true
% 3.01/0.99  
% 3.01/0.99  ------ Superposition Options
% 3.01/0.99  
% 3.01/0.99  --superposition_flag                    true
% 3.01/0.99  --sup_passive_queue_type                priority_queues
% 3.01/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.01/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.01/0.99  --demod_completeness_check              fast
% 3.01/0.99  --demod_use_ground                      true
% 3.01/0.99  --sup_to_prop_solver                    passive
% 3.01/0.99  --sup_prop_simpl_new                    true
% 3.01/0.99  --sup_prop_simpl_given                  true
% 3.01/0.99  --sup_fun_splitting                     false
% 3.01/0.99  --sup_smt_interval                      50000
% 3.01/0.99  
% 3.01/0.99  ------ Superposition Simplification Setup
% 3.01/0.99  
% 3.01/0.99  --sup_indices_passive                   []
% 3.01/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.01/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/0.99  --sup_full_bw                           [BwDemod]
% 3.01/0.99  --sup_immed_triv                        [TrivRules]
% 3.01/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.01/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/0.99  --sup_immed_bw_main                     []
% 3.01/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.01/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/0.99  
% 3.01/0.99  ------ Combination Options
% 3.01/0.99  
% 3.01/0.99  --comb_res_mult                         3
% 3.01/0.99  --comb_sup_mult                         2
% 3.01/0.99  --comb_inst_mult                        10
% 3.01/0.99  
% 3.01/0.99  ------ Debug Options
% 3.01/0.99  
% 3.01/0.99  --dbg_backtrace                         false
% 3.01/0.99  --dbg_dump_prop_clauses                 false
% 3.01/0.99  --dbg_dump_prop_clauses_file            -
% 3.01/0.99  --dbg_out_stat                          false
% 3.01/0.99  ------ Parsing...
% 3.01/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.01/0.99  
% 3.01/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 3.01/0.99  
% 3.01/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.01/0.99  
% 3.01/0.99  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.01/0.99  ------ Proving...
% 3.01/0.99  ------ Problem Properties 
% 3.01/0.99  
% 3.01/0.99  
% 3.01/0.99  clauses                                 24
% 3.01/0.99  conjectures                             0
% 3.01/0.99  EPR                                     0
% 3.01/0.99  Horn                                    18
% 3.01/0.99  unary                                   10
% 3.01/0.99  binary                                  9
% 3.01/0.99  lits                                    57
% 3.01/0.99  lits eq                                 14
% 3.01/0.99  fd_pure                                 0
% 3.01/0.99  fd_pseudo                               0
% 3.01/0.99  fd_cond                                 3
% 3.01/0.99  fd_pseudo_cond                          0
% 3.01/0.99  AC symbols                              0
% 3.01/0.99  
% 3.01/0.99  ------ Schedule dynamic 5 is on 
% 3.01/0.99  
% 3.01/0.99  ------ no conjectures: strip conj schedule 
% 3.01/0.99  
% 3.01/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 3.01/0.99  
% 3.01/0.99  
% 3.01/0.99  ------ 
% 3.01/0.99  Current options:
% 3.01/0.99  ------ 
% 3.01/0.99  
% 3.01/0.99  ------ Input Options
% 3.01/0.99  
% 3.01/0.99  --out_options                           all
% 3.01/0.99  --tptp_safe_out                         true
% 3.01/0.99  --problem_path                          ""
% 3.01/0.99  --include_path                          ""
% 3.01/0.99  --clausifier                            res/vclausify_rel
% 3.01/0.99  --clausifier_options                    --mode clausify
% 3.01/0.99  --stdin                                 false
% 3.01/0.99  --stats_out                             all
% 3.01/0.99  
% 3.01/0.99  ------ General Options
% 3.01/0.99  
% 3.01/0.99  --fof                                   false
% 3.01/0.99  --time_out_real                         305.
% 3.01/0.99  --time_out_virtual                      -1.
% 3.01/0.99  --symbol_type_check                     false
% 3.01/0.99  --clausify_out                          false
% 3.01/0.99  --sig_cnt_out                           false
% 3.01/0.99  --trig_cnt_out                          false
% 3.01/0.99  --trig_cnt_out_tolerance                1.
% 3.01/0.99  --trig_cnt_out_sk_spl                   false
% 3.01/0.99  --abstr_cl_out                          false
% 3.01/0.99  
% 3.01/0.99  ------ Global Options
% 3.01/0.99  
% 3.01/0.99  --schedule                              default
% 3.01/0.99  --add_important_lit                     false
% 3.01/0.99  --prop_solver_per_cl                    1000
% 3.01/0.99  --min_unsat_core                        false
% 3.01/0.99  --soft_assumptions                      false
% 3.01/0.99  --soft_lemma_size                       3
% 3.01/0.99  --prop_impl_unit_size                   0
% 3.01/0.99  --prop_impl_unit                        []
% 3.01/0.99  --share_sel_clauses                     true
% 3.01/0.99  --reset_solvers                         false
% 3.01/0.99  --bc_imp_inh                            [conj_cone]
% 3.01/0.99  --conj_cone_tolerance                   3.
% 3.01/0.99  --extra_neg_conj                        none
% 3.01/0.99  --large_theory_mode                     true
% 3.01/0.99  --prolific_symb_bound                   200
% 3.01/0.99  --lt_threshold                          2000
% 3.01/0.99  --clause_weak_htbl                      true
% 3.01/0.99  --gc_record_bc_elim                     false
% 3.01/0.99  
% 3.01/0.99  ------ Preprocessing Options
% 3.01/0.99  
% 3.01/0.99  --preprocessing_flag                    true
% 3.01/0.99  --time_out_prep_mult                    0.1
% 3.01/0.99  --splitting_mode                        input
% 3.01/0.99  --splitting_grd                         true
% 3.01/0.99  --splitting_cvd                         false
% 3.01/0.99  --splitting_cvd_svl                     false
% 3.01/0.99  --splitting_nvd                         32
% 3.01/0.99  --sub_typing                            true
% 3.01/0.99  --prep_gs_sim                           true
% 3.01/0.99  --prep_unflatten                        true
% 3.01/0.99  --prep_res_sim                          true
% 3.01/0.99  --prep_upred                            true
% 3.01/0.99  --prep_sem_filter                       exhaustive
% 3.01/0.99  --prep_sem_filter_out                   false
% 3.01/0.99  --pred_elim                             true
% 3.01/0.99  --res_sim_input                         true
% 3.01/0.99  --eq_ax_congr_red                       true
% 3.01/0.99  --pure_diseq_elim                       true
% 3.01/0.99  --brand_transform                       false
% 3.01/0.99  --non_eq_to_eq                          false
% 3.01/0.99  --prep_def_merge                        true
% 3.01/0.99  --prep_def_merge_prop_impl              false
% 3.01/0.99  --prep_def_merge_mbd                    true
% 3.01/0.99  --prep_def_merge_tr_red                 false
% 3.01/0.99  --prep_def_merge_tr_cl                  false
% 3.01/0.99  --smt_preprocessing                     true
% 3.01/0.99  --smt_ac_axioms                         fast
% 3.01/0.99  --preprocessed_out                      false
% 3.01/0.99  --preprocessed_stats                    false
% 3.01/0.99  
% 3.01/0.99  ------ Abstraction refinement Options
% 3.01/0.99  
% 3.01/0.99  --abstr_ref                             []
% 3.01/0.99  --abstr_ref_prep                        false
% 3.01/0.99  --abstr_ref_until_sat                   false
% 3.01/0.99  --abstr_ref_sig_restrict                funpre
% 3.01/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.01/0.99  --abstr_ref_under                       []
% 3.01/0.99  
% 3.01/0.99  ------ SAT Options
% 3.01/0.99  
% 3.01/0.99  --sat_mode                              false
% 3.01/0.99  --sat_fm_restart_options                ""
% 3.01/0.99  --sat_gr_def                            false
% 3.01/0.99  --sat_epr_types                         true
% 3.01/0.99  --sat_non_cyclic_types                  false
% 3.01/0.99  --sat_finite_models                     false
% 3.01/0.99  --sat_fm_lemmas                         false
% 3.01/0.99  --sat_fm_prep                           false
% 3.01/0.99  --sat_fm_uc_incr                        true
% 3.01/0.99  --sat_out_model                         small
% 3.01/0.99  --sat_out_clauses                       false
% 3.01/0.99  
% 3.01/0.99  ------ QBF Options
% 3.01/0.99  
% 3.01/0.99  --qbf_mode                              false
% 3.01/0.99  --qbf_elim_univ                         false
% 3.01/0.99  --qbf_dom_inst                          none
% 3.01/0.99  --qbf_dom_pre_inst                      false
% 3.01/0.99  --qbf_sk_in                             false
% 3.01/0.99  --qbf_pred_elim                         true
% 3.01/0.99  --qbf_split                             512
% 3.01/0.99  
% 3.01/0.99  ------ BMC1 Options
% 3.01/0.99  
% 3.01/0.99  --bmc1_incremental                      false
% 3.01/0.99  --bmc1_axioms                           reachable_all
% 3.01/0.99  --bmc1_min_bound                        0
% 3.01/0.99  --bmc1_max_bound                        -1
% 3.01/0.99  --bmc1_max_bound_default                -1
% 3.01/0.99  --bmc1_symbol_reachability              true
% 3.01/0.99  --bmc1_property_lemmas                  false
% 3.01/0.99  --bmc1_k_induction                      false
% 3.01/0.99  --bmc1_non_equiv_states                 false
% 3.01/0.99  --bmc1_deadlock                         false
% 3.01/0.99  --bmc1_ucm                              false
% 3.01/0.99  --bmc1_add_unsat_core                   none
% 3.01/0.99  --bmc1_unsat_core_children              false
% 3.01/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.01/0.99  --bmc1_out_stat                         full
% 3.01/0.99  --bmc1_ground_init                      false
% 3.01/0.99  --bmc1_pre_inst_next_state              false
% 3.01/0.99  --bmc1_pre_inst_state                   false
% 3.01/0.99  --bmc1_pre_inst_reach_state             false
% 3.01/0.99  --bmc1_out_unsat_core                   false
% 3.01/0.99  --bmc1_aig_witness_out                  false
% 3.01/0.99  --bmc1_verbose                          false
% 3.01/0.99  --bmc1_dump_clauses_tptp                false
% 3.01/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.01/0.99  --bmc1_dump_file                        -
% 3.01/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.01/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.01/1.00  --bmc1_ucm_extend_mode                  1
% 3.01/1.00  --bmc1_ucm_init_mode                    2
% 3.01/1.00  --bmc1_ucm_cone_mode                    none
% 3.01/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.01/1.00  --bmc1_ucm_relax_model                  4
% 3.01/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.01/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.01/1.00  --bmc1_ucm_layered_model                none
% 3.01/1.00  --bmc1_ucm_max_lemma_size               10
% 3.01/1.00  
% 3.01/1.00  ------ AIG Options
% 3.01/1.00  
% 3.01/1.00  --aig_mode                              false
% 3.01/1.00  
% 3.01/1.00  ------ Instantiation Options
% 3.01/1.00  
% 3.01/1.00  --instantiation_flag                    true
% 3.01/1.00  --inst_sos_flag                         false
% 3.01/1.00  --inst_sos_phase                        true
% 3.01/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.01/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.01/1.00  --inst_lit_sel_side                     none
% 3.01/1.00  --inst_solver_per_active                1400
% 3.01/1.00  --inst_solver_calls_frac                1.
% 3.01/1.00  --inst_passive_queue_type               priority_queues
% 3.01/1.00  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 3.01/1.00  --inst_passive_queues_freq              [25;2]
% 3.01/1.00  --inst_dismatching                      true
% 3.01/1.00  --inst_eager_unprocessed_to_passive     true
% 3.01/1.00  --inst_prop_sim_given                   true
% 3.01/1.00  --inst_prop_sim_new                     false
% 3.01/1.00  --inst_subs_new                         false
% 3.01/1.00  --inst_eq_res_simp                      false
% 3.01/1.00  --inst_subs_given                       false
% 3.01/1.00  --inst_orphan_elimination               true
% 3.01/1.00  --inst_learning_loop_flag               true
% 3.01/1.00  --inst_learning_start                   3000
% 3.01/1.00  --inst_learning_factor                  2
% 3.01/1.00  --inst_start_prop_sim_after_learn       3
% 3.01/1.00  --inst_sel_renew                        solver
% 3.01/1.00  --inst_lit_activity_flag                true
% 3.01/1.00  --inst_restr_to_given                   false
% 3.01/1.00  --inst_activity_threshold               500
% 3.01/1.00  --inst_out_proof                        true
% 3.01/1.00  
% 3.01/1.00  ------ Resolution Options
% 3.01/1.00  
% 3.01/1.00  --resolution_flag                       false
% 3.01/1.00  --res_lit_sel                           adaptive
% 3.01/1.00  --res_lit_sel_side                      none
% 3.01/1.00  --res_ordering                          kbo
% 3.01/1.00  --res_to_prop_solver                    active
% 3.01/1.00  --res_prop_simpl_new                    false
% 3.01/1.00  --res_prop_simpl_given                  true
% 3.01/1.00  --res_passive_queue_type                priority_queues
% 3.01/1.00  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 3.01/1.00  --res_passive_queues_freq               [15;5]
% 3.01/1.00  --res_forward_subs                      full
% 3.01/1.00  --res_backward_subs                     full
% 3.01/1.00  --res_forward_subs_resolution           true
% 3.01/1.00  --res_backward_subs_resolution          true
% 3.01/1.00  --res_orphan_elimination                true
% 3.01/1.00  --res_time_limit                        2.
% 3.01/1.00  --res_out_proof                         true
% 3.01/1.00  
% 3.01/1.00  ------ Superposition Options
% 3.01/1.00  
% 3.01/1.00  --superposition_flag                    true
% 3.01/1.00  --sup_passive_queue_type                priority_queues
% 3.01/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.01/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.01/1.00  --demod_completeness_check              fast
% 3.01/1.00  --demod_use_ground                      true
% 3.01/1.00  --sup_to_prop_solver                    passive
% 3.01/1.00  --sup_prop_simpl_new                    true
% 3.01/1.00  --sup_prop_simpl_given                  true
% 3.01/1.00  --sup_fun_splitting                     false
% 3.01/1.00  --sup_smt_interval                      50000
% 3.01/1.00  
% 3.01/1.00  ------ Superposition Simplification Setup
% 3.01/1.00  
% 3.01/1.00  --sup_indices_passive                   []
% 3.01/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.01/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/1.00  --sup_full_bw                           [BwDemod]
% 3.01/1.00  --sup_immed_triv                        [TrivRules]
% 3.01/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.01/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/1.00  --sup_immed_bw_main                     []
% 3.01/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.01/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/1.00  
% 3.01/1.00  ------ Combination Options
% 3.01/1.00  
% 3.01/1.00  --comb_res_mult                         3
% 3.01/1.00  --comb_sup_mult                         2
% 3.01/1.00  --comb_inst_mult                        10
% 3.01/1.00  
% 3.01/1.00  ------ Debug Options
% 3.01/1.00  
% 3.01/1.00  --dbg_backtrace                         false
% 3.01/1.00  --dbg_dump_prop_clauses                 false
% 3.01/1.00  --dbg_dump_prop_clauses_file            -
% 3.01/1.00  --dbg_out_stat                          false
% 3.01/1.00  
% 3.01/1.00  
% 3.01/1.00  
% 3.01/1.00  
% 3.01/1.00  ------ Proving...
% 3.01/1.00  
% 3.01/1.00  
% 3.01/1.00  % SZS status Theorem for theBenchmark.p
% 3.01/1.00  
% 3.01/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.01/1.00  
% 3.01/1.00  fof(f11,axiom,(
% 3.01/1.00    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))))),
% 3.01/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f35,plain,(
% 3.01/1.00    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.01/1.00    inference(ennf_transformation,[],[f11])).
% 3.01/1.00  
% 3.01/1.00  fof(f36,plain,(
% 3.01/1.00    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.01/1.00    inference(flattening,[],[f35])).
% 3.01/1.00  
% 3.01/1.00  fof(f91,plain,(
% 3.01/1.00    ( ! [X0,X1] : (v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f36])).
% 3.01/1.00  
% 3.01/1.00  fof(f15,conjecture,(
% 3.01/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))))))),
% 3.01/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f16,negated_conjecture,(
% 3.01/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))))))),
% 3.01/1.00    inference(negated_conjecture,[],[f15])).
% 3.01/1.00  
% 3.01/1.00  fof(f42,plain,(
% 3.01/1.00    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1)))) & m1_pre_topc(X1,X0)) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.01/1.00    inference(ennf_transformation,[],[f16])).
% 3.01/1.00  
% 3.01/1.00  fof(f43,plain,(
% 3.01/1.00    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.01/1.00    inference(flattening,[],[f42])).
% 3.01/1.00  
% 3.01/1.00  fof(f61,plain,(
% 3.01/1.00    ? [X0] : (? [X1] : ((((~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) & ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.01/1.00    inference(nnf_transformation,[],[f43])).
% 3.01/1.00  
% 3.01/1.00  fof(f62,plain,(
% 3.01/1.00    ? [X0] : (? [X1] : ((~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.01/1.00    inference(flattening,[],[f61])).
% 3.01/1.00  
% 3.01/1.00  fof(f64,plain,(
% 3.01/1.00    ( ! [X0] : (? [X1] : ((~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0)) => ((~m1_subset_1(k9_tmap_1(X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,sK5))))) | ~v5_pre_topc(k9_tmap_1(X0,sK5),X0,k8_tmap_1(X0,sK5)) | ~v1_funct_2(k9_tmap_1(X0,sK5),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,sK5))) | ~v1_funct_1(k9_tmap_1(X0,sK5)) | ~m1_pre_topc(sK5,X0) | ~v1_tsep_1(sK5,X0)) & ((m1_subset_1(k9_tmap_1(X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,sK5))))) & v5_pre_topc(k9_tmap_1(X0,sK5),X0,k8_tmap_1(X0,sK5)) & v1_funct_2(k9_tmap_1(X0,sK5),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,sK5))) & v1_funct_1(k9_tmap_1(X0,sK5))) | (m1_pre_topc(sK5,X0) & v1_tsep_1(sK5,X0))) & m1_pre_topc(sK5,X0))) )),
% 3.01/1.00    introduced(choice_axiom,[])).
% 3.01/1.00  
% 3.01/1.00  fof(f63,plain,(
% 3.01/1.00    ? [X0] : (? [X1] : ((~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~m1_subset_1(k9_tmap_1(sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,X1))))) | ~v5_pre_topc(k9_tmap_1(sK4,X1),sK4,k8_tmap_1(sK4,X1)) | ~v1_funct_2(k9_tmap_1(sK4,X1),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,X1))) | ~v1_funct_1(k9_tmap_1(sK4,X1)) | ~m1_pre_topc(X1,sK4) | ~v1_tsep_1(X1,sK4)) & ((m1_subset_1(k9_tmap_1(sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,X1))))) & v5_pre_topc(k9_tmap_1(sK4,X1),sK4,k8_tmap_1(sK4,X1)) & v1_funct_2(k9_tmap_1(sK4,X1),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,X1))) & v1_funct_1(k9_tmap_1(sK4,X1))) | (m1_pre_topc(X1,sK4) & v1_tsep_1(X1,sK4))) & m1_pre_topc(X1,sK4)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 3.01/1.00    introduced(choice_axiom,[])).
% 3.01/1.00  
% 3.01/1.00  fof(f65,plain,(
% 3.01/1.00    ((~m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))))) | ~v5_pre_topc(k9_tmap_1(sK4,sK5),sK4,k8_tmap_1(sK4,sK5)) | ~v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))) | ~v1_funct_1(k9_tmap_1(sK4,sK5)) | ~m1_pre_topc(sK5,sK4) | ~v1_tsep_1(sK5,sK4)) & ((m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))))) & v5_pre_topc(k9_tmap_1(sK4,sK5),sK4,k8_tmap_1(sK4,sK5)) & v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))) & v1_funct_1(k9_tmap_1(sK4,sK5))) | (m1_pre_topc(sK5,sK4) & v1_tsep_1(sK5,sK4))) & m1_pre_topc(sK5,sK4)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)),
% 3.01/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f62,f64,f63])).
% 3.01/1.00  
% 3.01/1.00  fof(f113,plain,(
% 3.01/1.00    m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))))) | m1_pre_topc(sK5,sK4)),
% 3.01/1.00    inference(cnf_transformation,[],[f65])).
% 3.01/1.00  
% 3.01/1.00  fof(f105,plain,(
% 3.01/1.00    m1_pre_topc(sK5,sK4)),
% 3.01/1.00    inference(cnf_transformation,[],[f65])).
% 3.01/1.00  
% 3.01/1.00  fof(f102,plain,(
% 3.01/1.00    ~v2_struct_0(sK4)),
% 3.01/1.00    inference(cnf_transformation,[],[f65])).
% 3.01/1.00  
% 3.01/1.00  fof(f103,plain,(
% 3.01/1.00    v2_pre_topc(sK4)),
% 3.01/1.00    inference(cnf_transformation,[],[f65])).
% 3.01/1.00  
% 3.01/1.00  fof(f104,plain,(
% 3.01/1.00    l1_pre_topc(sK4)),
% 3.01/1.00    inference(cnf_transformation,[],[f65])).
% 3.01/1.00  
% 3.01/1.00  fof(f13,axiom,(
% 3.01/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))))),
% 3.01/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f39,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.01/1.00    inference(ennf_transformation,[],[f13])).
% 3.01/1.00  
% 3.01/1.00  fof(f40,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.01/1.00    inference(flattening,[],[f39])).
% 3.01/1.00  
% 3.01/1.00  fof(f59,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | (~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1)))) & ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.01/1.00    inference(nnf_transformation,[],[f40])).
% 3.01/1.00  
% 3.01/1.00  fof(f60,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1))) & ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.01/1.00    inference(flattening,[],[f59])).
% 3.01/1.00  
% 3.01/1.00  fof(f100,plain,(
% 3.01/1.00    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f60])).
% 3.01/1.00  
% 3.01/1.00  fof(f9,axiom,(
% 3.01/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 3.01/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f31,plain,(
% 3.01/1.00    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.01/1.00    inference(ennf_transformation,[],[f9])).
% 3.01/1.00  
% 3.01/1.00  fof(f32,plain,(
% 3.01/1.00    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.01/1.00    inference(flattening,[],[f31])).
% 3.01/1.00  
% 3.01/1.00  fof(f86,plain,(
% 3.01/1.00    ( ! [X0,X1] : (v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f32])).
% 3.01/1.00  
% 3.01/1.00  fof(f110,plain,(
% 3.01/1.00    v5_pre_topc(k9_tmap_1(sK4,sK5),sK4,k8_tmap_1(sK4,sK5)) | v1_tsep_1(sK5,sK4)),
% 3.01/1.00    inference(cnf_transformation,[],[f65])).
% 3.01/1.00  
% 3.01/1.00  fof(f8,axiom,(
% 3.01/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tsep_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v3_pre_topc(X2,X0))))))),
% 3.01/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f29,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.01/1.00    inference(ennf_transformation,[],[f8])).
% 3.01/1.00  
% 3.01/1.00  fof(f30,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.01/1.00    inference(flattening,[],[f29])).
% 3.01/1.00  
% 3.01/1.00  fof(f55,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.01/1.00    inference(nnf_transformation,[],[f30])).
% 3.01/1.00  
% 3.01/1.00  fof(f56,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.01/1.00    inference(rectify,[],[f55])).
% 3.01/1.00  
% 3.01/1.00  fof(f57,plain,(
% 3.01/1.00    ! [X1,X0] : (? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK3(X0,X1),X0) & u1_struct_0(X1) = sK3(X0,X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.01/1.00    introduced(choice_axiom,[])).
% 3.01/1.00  
% 3.01/1.00  fof(f58,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | (~v3_pre_topc(sK3(X0,X1),X0) & u1_struct_0(X1) = sK3(X0,X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.01/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f56,f57])).
% 3.01/1.00  
% 3.01/1.00  fof(f84,plain,(
% 3.01/1.00    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(sK3(X0,X1),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f58])).
% 3.01/1.00  
% 3.01/1.00  fof(f82,plain,(
% 3.01/1.00    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f58])).
% 3.01/1.00  
% 3.01/1.00  fof(f14,axiom,(
% 3.01/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.01/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f41,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.01/1.00    inference(ennf_transformation,[],[f14])).
% 3.01/1.00  
% 3.01/1.00  fof(f101,plain,(
% 3.01/1.00    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f41])).
% 3.01/1.00  
% 3.01/1.00  fof(f93,plain,(
% 3.01/1.00    ( ! [X0,X1] : (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f36])).
% 3.01/1.00  
% 3.01/1.00  fof(f92,plain,(
% 3.01/1.00    ( ! [X0,X1] : (v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f36])).
% 3.01/1.00  
% 3.01/1.00  fof(f98,plain,(
% 3.01/1.00    ( ! [X0,X1] : (v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f60])).
% 3.01/1.00  
% 3.01/1.00  fof(f114,plain,(
% 3.01/1.00    ~m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))))) | ~v5_pre_topc(k9_tmap_1(sK4,sK5),sK4,k8_tmap_1(sK4,sK5)) | ~v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))) | ~v1_funct_1(k9_tmap_1(sK4,sK5)) | ~m1_pre_topc(sK5,sK4) | ~v1_tsep_1(sK5,sK4)),
% 3.01/1.00    inference(cnf_transformation,[],[f65])).
% 3.01/1.00  
% 3.01/1.00  fof(f81,plain,(
% 3.01/1.00    ( ! [X0,X3,X1] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f58])).
% 3.01/1.00  
% 3.01/1.00  fof(f120,plain,(
% 3.01/1.00    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.01/1.00    inference(equality_resolution,[],[f81])).
% 3.01/1.00  
% 3.01/1.00  fof(f6,axiom,(
% 3.01/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & v1_pre_topc(X2)) => (k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => k6_tmap_1(X0,X3) = X2))))))),
% 3.01/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f25,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : ((k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.01/1.00    inference(ennf_transformation,[],[f6])).
% 3.01/1.00  
% 3.01/1.00  fof(f26,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.01/1.00    inference(flattening,[],[f25])).
% 3.01/1.00  
% 3.01/1.00  fof(f47,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.01/1.00    inference(nnf_transformation,[],[f26])).
% 3.01/1.00  
% 3.01/1.00  fof(f48,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.01/1.00    inference(rectify,[],[f47])).
% 3.01/1.00  
% 3.01/1.00  fof(f49,plain,(
% 3.01/1.00    ! [X2,X1,X0] : (? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (k6_tmap_1(X0,sK1(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK1(X0,X1,X2) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.01/1.00    introduced(choice_axiom,[])).
% 3.01/1.00  
% 3.01/1.00  fof(f50,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | (k6_tmap_1(X0,sK1(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK1(X0,X1,X2) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.01/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f48,f49])).
% 3.01/1.00  
% 3.01/1.00  fof(f73,plain,(
% 3.01/1.00    ( ! [X4,X2,X0,X1] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f50])).
% 3.01/1.00  
% 3.01/1.00  fof(f116,plain,(
% 3.01/1.00    ( ! [X2,X0,X1] : (k6_tmap_1(X0,u1_struct_0(X1)) = X2 | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.01/1.00    inference(equality_resolution,[],[f73])).
% 3.01/1.00  
% 3.01/1.00  fof(f117,plain,(
% 3.01/1.00    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.01/1.00    inference(equality_resolution,[],[f116])).
% 3.01/1.00  
% 3.01/1.00  fof(f10,axiom,(
% 3.01/1.00    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 3.01/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f33,plain,(
% 3.01/1.00    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.01/1.00    inference(ennf_transformation,[],[f10])).
% 3.01/1.00  
% 3.01/1.00  fof(f34,plain,(
% 3.01/1.00    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.01/1.00    inference(flattening,[],[f33])).
% 3.01/1.00  
% 3.01/1.00  fof(f88,plain,(
% 3.01/1.00    ( ! [X0,X1] : (v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f34])).
% 3.01/1.00  
% 3.01/1.00  fof(f89,plain,(
% 3.01/1.00    ( ! [X0,X1] : (v2_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f34])).
% 3.01/1.00  
% 3.01/1.00  fof(f90,plain,(
% 3.01/1.00    ( ! [X0,X1] : (l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f34])).
% 3.01/1.00  
% 3.01/1.00  fof(f12,axiom,(
% 3.01/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 3.01/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f37,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.01/1.00    inference(ennf_transformation,[],[f12])).
% 3.01/1.00  
% 3.01/1.00  fof(f38,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.01/1.00    inference(flattening,[],[f37])).
% 3.01/1.00  
% 3.01/1.00  fof(f94,plain,(
% 3.01/1.00    ( ! [X0,X1] : (u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f38])).
% 3.01/1.00  
% 3.01/1.00  fof(f87,plain,(
% 3.01/1.00    ( ! [X0,X1] : (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f32])).
% 3.01/1.00  
% 3.01/1.00  fof(f4,axiom,(
% 3.01/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 3.01/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f21,plain,(
% 3.01/1.00    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 3.01/1.00    inference(ennf_transformation,[],[f4])).
% 3.01/1.00  
% 3.01/1.00  fof(f22,plain,(
% 3.01/1.00    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 3.01/1.00    inference(flattening,[],[f21])).
% 3.01/1.00  
% 3.01/1.00  fof(f46,plain,(
% 3.01/1.00    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 3.01/1.00    inference(nnf_transformation,[],[f22])).
% 3.01/1.00  
% 3.01/1.00  fof(f70,plain,(
% 3.01/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f46])).
% 3.01/1.00  
% 3.01/1.00  fof(f7,axiom,(
% 3.01/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(X2)) => (k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))))))))),
% 3.01/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f27,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : ((r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.01/1.00    inference(ennf_transformation,[],[f7])).
% 3.01/1.00  
% 3.01/1.00  fof(f28,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.01/1.00    inference(flattening,[],[f27])).
% 3.01/1.00  
% 3.01/1.00  fof(f51,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | ? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.01/1.00    inference(nnf_transformation,[],[f28])).
% 3.01/1.00  
% 3.01/1.00  fof(f52,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | ? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.01/1.00    inference(rectify,[],[f51])).
% 3.01/1.00  
% 3.01/1.00  fof(f53,plain,(
% 3.01/1.00    ! [X2,X1,X0] : (? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2(X0,X1,X2))),X2,k7_tmap_1(X0,sK2(X0,X1,X2))) & u1_struct_0(X1) = sK2(X0,X1,X2) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.01/1.00    introduced(choice_axiom,[])).
% 3.01/1.00  
% 3.01/1.00  fof(f54,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2(X0,X1,X2))),X2,k7_tmap_1(X0,sK2(X0,X1,X2))) & u1_struct_0(X1) = sK2(X0,X1,X2) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.01/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f52,f53])).
% 3.01/1.00  
% 3.01/1.00  fof(f77,plain,(
% 3.01/1.00    ( ! [X4,X2,X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k9_tmap_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f54])).
% 3.01/1.00  
% 3.01/1.00  fof(f118,plain,(
% 3.01/1.00    ( ! [X2,X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),X2,k7_tmap_1(X0,u1_struct_0(X1))) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k9_tmap_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.01/1.00    inference(equality_resolution,[],[f77])).
% 3.01/1.00  
% 3.01/1.00  fof(f119,plain,(
% 3.01/1.00    ( ! [X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1))) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.01/1.00    inference(equality_resolution,[],[f118])).
% 3.01/1.00  
% 3.01/1.00  fof(f85,plain,(
% 3.01/1.00    ( ! [X0,X1] : (v1_funct_1(k7_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f32])).
% 3.01/1.00  
% 3.01/1.00  fof(f1,axiom,(
% 3.01/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.01/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f17,plain,(
% 3.01/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.01/1.00    inference(ennf_transformation,[],[f1])).
% 3.01/1.00  
% 3.01/1.00  fof(f66,plain,(
% 3.01/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f17])).
% 3.01/1.00  
% 3.01/1.00  fof(f2,axiom,(
% 3.01/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.01/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f18,plain,(
% 3.01/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.01/1.00    inference(ennf_transformation,[],[f2])).
% 3.01/1.00  
% 3.01/1.00  fof(f19,plain,(
% 3.01/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.01/1.00    inference(flattening,[],[f18])).
% 3.01/1.00  
% 3.01/1.00  fof(f67,plain,(
% 3.01/1.00    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f19])).
% 3.01/1.00  
% 3.01/1.00  fof(f5,axiom,(
% 3.01/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))))),
% 3.01/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f23,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.01/1.00    inference(ennf_transformation,[],[f5])).
% 3.01/1.00  
% 3.01/1.00  fof(f24,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.01/1.00    inference(flattening,[],[f23])).
% 3.01/1.00  
% 3.01/1.00  fof(f72,plain,(
% 3.01/1.00    ( ! [X0,X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f24])).
% 3.01/1.00  
% 3.01/1.00  fof(f83,plain,(
% 3.01/1.00    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | u1_struct_0(X1) = sK3(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f58])).
% 3.01/1.00  
% 3.01/1.00  fof(f3,axiom,(
% 3.01/1.00    ! [X0] : (l1_pre_topc(X0) => ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.01/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f20,plain,(
% 3.01/1.00    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.01/1.00    inference(ennf_transformation,[],[f3])).
% 3.01/1.00  
% 3.01/1.00  fof(f44,plain,(
% 3.01/1.00    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (v1_xboole_0(sK0(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.01/1.00    introduced(choice_axiom,[])).
% 3.01/1.00  
% 3.01/1.00  fof(f45,plain,(
% 3.01/1.00    ! [X0] : ((v1_xboole_0(sK0(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.01/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f44])).
% 3.01/1.00  
% 3.01/1.00  fof(f68,plain,(
% 3.01/1.00    ( ! [X0] : (m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f45])).
% 3.01/1.00  
% 3.01/1.00  cnf(c_27,plain,
% 3.01/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.01/1.00      | ~ v2_pre_topc(X1)
% 3.01/1.00      | v1_funct_1(k9_tmap_1(X1,X0))
% 3.01/1.00      | v2_struct_0(X1)
% 3.01/1.00      | ~ l1_pre_topc(X1) ),
% 3.01/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_37,negated_conjecture,
% 3.01/1.00      ( m1_pre_topc(sK5,sK4)
% 3.01/1.00      | m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))))) ),
% 3.01/1.00      inference(cnf_transformation,[],[f113]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_45,negated_conjecture,
% 3.01/1.00      ( m1_pre_topc(sK5,sK4) ),
% 3.01/1.00      inference(cnf_transformation,[],[f105]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_292,negated_conjecture,
% 3.01/1.00      ( m1_pre_topc(sK5,sK4) ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_37,c_45]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1230,plain,
% 3.01/1.00      ( ~ v2_pre_topc(X0)
% 3.01/1.00      | v1_funct_1(k9_tmap_1(X0,X1))
% 3.01/1.00      | v2_struct_0(X0)
% 3.01/1.00      | ~ l1_pre_topc(X0)
% 3.01/1.00      | sK5 != X1
% 3.01/1.00      | sK4 != X0 ),
% 3.01/1.00      inference(resolution_lifted,[status(thm)],[c_27,c_292]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1231,plain,
% 3.01/1.00      ( ~ v2_pre_topc(sK4)
% 3.01/1.00      | v1_funct_1(k9_tmap_1(sK4,sK5))
% 3.01/1.00      | v2_struct_0(sK4)
% 3.01/1.00      | ~ l1_pre_topc(sK4) ),
% 3.01/1.00      inference(unflattening,[status(thm)],[c_1230]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_48,negated_conjecture,
% 3.01/1.00      ( ~ v2_struct_0(sK4) ),
% 3.01/1.00      inference(cnf_transformation,[],[f102]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_47,negated_conjecture,
% 3.01/1.00      ( v2_pre_topc(sK4) ),
% 3.01/1.00      inference(cnf_transformation,[],[f103]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_46,negated_conjecture,
% 3.01/1.00      ( l1_pre_topc(sK4) ),
% 3.01/1.00      inference(cnf_transformation,[],[f104]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1233,plain,
% 3.01/1.00      ( v1_funct_1(k9_tmap_1(sK4,sK5)) ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_1231,c_48,c_47,c_46]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_30,plain,
% 3.01/1.00      ( ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
% 3.01/1.00      | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
% 3.01/1.00      | v3_pre_topc(X1,X0)
% 3.01/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.01/1.00      | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
% 3.01/1.00      | ~ v2_pre_topc(X0)
% 3.01/1.00      | ~ v1_funct_1(k7_tmap_1(X0,X1))
% 3.01/1.00      | v2_struct_0(X0)
% 3.01/1.00      | ~ l1_pre_topc(X0) ),
% 3.01/1.00      inference(cnf_transformation,[],[f100]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_20,plain,
% 3.01/1.00      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
% 3.01/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.01/1.00      | ~ v2_pre_topc(X0)
% 3.01/1.00      | v2_struct_0(X0)
% 3.01/1.00      | ~ l1_pre_topc(X0) ),
% 3.01/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_319,plain,
% 3.01/1.00      ( ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
% 3.01/1.00      | v3_pre_topc(X1,X0)
% 3.01/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.01/1.00      | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
% 3.01/1.00      | ~ v2_pre_topc(X0)
% 3.01/1.00      | ~ v1_funct_1(k7_tmap_1(X0,X1))
% 3.01/1.00      | v2_struct_0(X0)
% 3.01/1.00      | ~ l1_pre_topc(X0) ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_30,c_20]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_40,negated_conjecture,
% 3.01/1.00      ( v5_pre_topc(k9_tmap_1(sK4,sK5),sK4,k8_tmap_1(sK4,sK5))
% 3.01/1.00      | v1_tsep_1(sK5,sK4) ),
% 3.01/1.00      inference(cnf_transformation,[],[f110]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_629,plain,
% 3.01/1.00      ( v3_pre_topc(X0,X1)
% 3.01/1.00      | v1_tsep_1(sK5,sK4)
% 3.01/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/1.00      | ~ m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
% 3.01/1.00      | ~ v2_pre_topc(X1)
% 3.01/1.00      | ~ v1_funct_1(k7_tmap_1(X1,X0))
% 3.01/1.00      | v2_struct_0(X1)
% 3.01/1.00      | ~ l1_pre_topc(X1)
% 3.01/1.00      | k6_tmap_1(X1,X0) != k8_tmap_1(sK4,sK5)
% 3.01/1.00      | k7_tmap_1(X1,X0) != k9_tmap_1(sK4,sK5)
% 3.01/1.00      | sK4 != X1 ),
% 3.01/1.00      inference(resolution_lifted,[status(thm)],[c_319,c_40]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_630,plain,
% 3.01/1.00      ( v3_pre_topc(X0,sK4)
% 3.01/1.00      | v1_tsep_1(sK5,sK4)
% 3.01/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.01/1.00      | ~ m1_subset_1(k7_tmap_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X0)))))
% 3.01/1.00      | ~ v2_pre_topc(sK4)
% 3.01/1.00      | ~ v1_funct_1(k7_tmap_1(sK4,X0))
% 3.01/1.00      | v2_struct_0(sK4)
% 3.01/1.00      | ~ l1_pre_topc(sK4)
% 3.01/1.00      | k6_tmap_1(sK4,X0) != k8_tmap_1(sK4,sK5)
% 3.01/1.00      | k7_tmap_1(sK4,X0) != k9_tmap_1(sK4,sK5) ),
% 3.01/1.00      inference(unflattening,[status(thm)],[c_629]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_634,plain,
% 3.01/1.00      ( ~ m1_subset_1(k7_tmap_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X0)))))
% 3.01/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.01/1.00      | v1_tsep_1(sK5,sK4)
% 3.01/1.00      | v3_pre_topc(X0,sK4)
% 3.01/1.00      | ~ v1_funct_1(k7_tmap_1(sK4,X0))
% 3.01/1.00      | k6_tmap_1(sK4,X0) != k8_tmap_1(sK4,sK5)
% 3.01/1.00      | k7_tmap_1(sK4,X0) != k9_tmap_1(sK4,sK5) ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_630,c_48,c_47,c_46]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_635,plain,
% 3.01/1.00      ( v3_pre_topc(X0,sK4)
% 3.01/1.00      | v1_tsep_1(sK5,sK4)
% 3.01/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.01/1.00      | ~ m1_subset_1(k7_tmap_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X0)))))
% 3.01/1.00      | ~ v1_funct_1(k7_tmap_1(sK4,X0))
% 3.01/1.00      | k6_tmap_1(sK4,X0) != k8_tmap_1(sK4,sK5)
% 3.01/1.00      | k7_tmap_1(sK4,X0) != k9_tmap_1(sK4,sK5) ),
% 3.01/1.00      inference(renaming,[status(thm)],[c_634]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_15,plain,
% 3.01/1.00      ( ~ v3_pre_topc(sK3(X0,X1),X0)
% 3.01/1.00      | v1_tsep_1(X1,X0)
% 3.01/1.00      | ~ m1_pre_topc(X1,X0)
% 3.01/1.00      | ~ l1_pre_topc(X0) ),
% 3.01/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1154,plain,
% 3.01/1.00      ( ~ v3_pre_topc(sK3(X0,X1),X0)
% 3.01/1.00      | v1_tsep_1(X1,X0)
% 3.01/1.00      | ~ l1_pre_topc(X0)
% 3.01/1.00      | sK5 != X1
% 3.01/1.00      | sK4 != X0 ),
% 3.01/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_292]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1155,plain,
% 3.01/1.00      ( ~ v3_pre_topc(sK3(sK4,sK5),sK4)
% 3.01/1.00      | v1_tsep_1(sK5,sK4)
% 3.01/1.00      | ~ l1_pre_topc(sK4) ),
% 3.01/1.00      inference(unflattening,[status(thm)],[c_1154]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1157,plain,
% 3.01/1.00      ( v1_tsep_1(sK5,sK4) | ~ v3_pre_topc(sK3(sK4,sK5),sK4) ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_1155,c_46]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1158,plain,
% 3.01/1.00      ( ~ v3_pre_topc(sK3(sK4,sK5),sK4) | v1_tsep_1(sK5,sK4) ),
% 3.01/1.00      inference(renaming,[status(thm)],[c_1157]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1536,plain,
% 3.01/1.00      ( v1_tsep_1(sK5,sK4)
% 3.01/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.01/1.00      | ~ m1_subset_1(k7_tmap_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X0)))))
% 3.01/1.00      | ~ v1_funct_1(k7_tmap_1(sK4,X0))
% 3.01/1.00      | sK3(sK4,sK5) != X0
% 3.01/1.00      | k6_tmap_1(sK4,X0) != k8_tmap_1(sK4,sK5)
% 3.01/1.00      | k7_tmap_1(sK4,X0) != k9_tmap_1(sK4,sK5)
% 3.01/1.00      | sK4 != sK4 ),
% 3.01/1.00      inference(resolution_lifted,[status(thm)],[c_635,c_1158]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1537,plain,
% 3.01/1.00      ( v1_tsep_1(sK5,sK4)
% 3.01/1.00      | ~ m1_subset_1(sK3(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.01/1.00      | ~ m1_subset_1(k7_tmap_1(sK4,sK3(sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK3(sK4,sK5))))))
% 3.01/1.00      | ~ v1_funct_1(k7_tmap_1(sK4,sK3(sK4,sK5)))
% 3.01/1.00      | k6_tmap_1(sK4,sK3(sK4,sK5)) != k8_tmap_1(sK4,sK5)
% 3.01/1.00      | k7_tmap_1(sK4,sK3(sK4,sK5)) != k9_tmap_1(sK4,sK5) ),
% 3.01/1.00      inference(unflattening,[status(thm)],[c_1536]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_17,plain,
% 3.01/1.00      ( v1_tsep_1(X0,X1)
% 3.01/1.00      | ~ m1_pre_topc(X0,X1)
% 3.01/1.00      | m1_subset_1(sK3(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/1.00      | ~ l1_pre_topc(X1) ),
% 3.01/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1289,plain,
% 3.01/1.00      ( v1_tsep_1(X0,X1)
% 3.01/1.00      | m1_subset_1(sK3(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/1.00      | ~ l1_pre_topc(X1)
% 3.01/1.00      | sK5 != X0
% 3.01/1.00      | sK4 != X1 ),
% 3.01/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_292]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1290,plain,
% 3.01/1.00      ( v1_tsep_1(sK5,sK4)
% 3.01/1.00      | m1_subset_1(sK3(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.01/1.00      | ~ l1_pre_topc(sK4) ),
% 3.01/1.00      inference(unflattening,[status(thm)],[c_1289]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1539,plain,
% 3.01/1.00      ( v1_tsep_1(sK5,sK4)
% 3.01/1.00      | ~ m1_subset_1(k7_tmap_1(sK4,sK3(sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK3(sK4,sK5))))))
% 3.01/1.00      | ~ v1_funct_1(k7_tmap_1(sK4,sK3(sK4,sK5)))
% 3.01/1.00      | k6_tmap_1(sK4,sK3(sK4,sK5)) != k8_tmap_1(sK4,sK5)
% 3.01/1.00      | k7_tmap_1(sK4,sK3(sK4,sK5)) != k9_tmap_1(sK4,sK5) ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_1537,c_46,c_1290]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1962,plain,
% 3.01/1.00      ( v1_tsep_1(sK5,sK4)
% 3.01/1.00      | ~ m1_subset_1(k7_tmap_1(sK4,sK3(sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK3(sK4,sK5))))))
% 3.01/1.00      | k6_tmap_1(sK4,sK3(sK4,sK5)) != k8_tmap_1(sK4,sK5)
% 3.01/1.00      | k7_tmap_1(sK4,sK3(sK4,sK5)) != k9_tmap_1(sK4,sK5) ),
% 3.01/1.00      inference(resolution_lifted,[status(thm)],[c_1233,c_1539]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2541,plain,
% 3.01/1.00      ( v1_tsep_1(sK5,sK4)
% 3.01/1.00      | ~ m1_subset_1(k7_tmap_1(sK4,sK3(sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK3(sK4,sK5))))))
% 3.01/1.00      | k7_tmap_1(sK4,sK3(sK4,sK5)) != k9_tmap_1(sK4,sK5)
% 3.01/1.00      | k6_tmap_1(sK4,sK3(sK4,sK5)) != k8_tmap_1(sK4,sK5) ),
% 3.01/1.00      inference(subtyping,[status(esa)],[c_1962]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3050,plain,
% 3.01/1.00      ( k7_tmap_1(sK4,sK3(sK4,sK5)) != k9_tmap_1(sK4,sK5)
% 3.01/1.00      | k6_tmap_1(sK4,sK3(sK4,sK5)) != k8_tmap_1(sK4,sK5)
% 3.01/1.00      | v1_tsep_1(sK5,sK4) = iProver_top
% 3.01/1.00      | m1_subset_1(k7_tmap_1(sK4,sK3(sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK3(sK4,sK5)))))) != iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_2541]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_51,plain,
% 3.01/1.00      ( l1_pre_topc(sK4) = iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_35,plain,
% 3.01/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.01/1.00      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/1.00      | ~ l1_pre_topc(X1) ),
% 3.01/1.00      inference(cnf_transformation,[],[f101]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1217,plain,
% 3.01/1.00      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/1.00      | ~ l1_pre_topc(X1)
% 3.01/1.00      | sK5 != X0
% 3.01/1.00      | sK4 != X1 ),
% 3.01/1.00      inference(resolution_lifted,[status(thm)],[c_35,c_292]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1218,plain,
% 3.01/1.00      ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.01/1.00      | ~ l1_pre_topc(sK4) ),
% 3.01/1.00      inference(unflattening,[status(thm)],[c_1217]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1219,plain,
% 3.01/1.00      ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 3.01/1.00      | l1_pre_topc(sK4) != iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_1218]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_25,plain,
% 3.01/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.01/1.00      | m1_subset_1(k9_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X0)))))
% 3.01/1.00      | ~ v2_pre_topc(X1)
% 3.01/1.00      | v2_struct_0(X1)
% 3.01/1.00      | ~ l1_pre_topc(X1) ),
% 3.01/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1243,plain,
% 3.01/1.00      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 3.01/1.00      | ~ v2_pre_topc(X0)
% 3.01/1.00      | v2_struct_0(X0)
% 3.01/1.00      | ~ l1_pre_topc(X0)
% 3.01/1.00      | sK5 != X1
% 3.01/1.00      | sK4 != X0 ),
% 3.01/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_292]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1244,plain,
% 3.01/1.00      ( m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
% 3.01/1.00      | ~ v2_pre_topc(sK4)
% 3.01/1.00      | v2_struct_0(sK4)
% 3.01/1.00      | ~ l1_pre_topc(sK4) ),
% 3.01/1.00      inference(unflattening,[status(thm)],[c_1243]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1246,plain,
% 3.01/1.00      ( m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))))) ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_1244,c_48,c_47,c_46]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_26,plain,
% 3.01/1.00      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 3.01/1.00      | ~ m1_pre_topc(X1,X0)
% 3.01/1.00      | ~ v2_pre_topc(X0)
% 3.01/1.00      | v2_struct_0(X0)
% 3.01/1.00      | ~ l1_pre_topc(X0) ),
% 3.01/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1143,plain,
% 3.01/1.00      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 3.01/1.00      | ~ v2_pre_topc(X0)
% 3.01/1.00      | v2_struct_0(X0)
% 3.01/1.00      | ~ l1_pre_topc(X0)
% 3.01/1.00      | sK5 != X1
% 3.01/1.00      | sK4 != X0 ),
% 3.01/1.00      inference(resolution_lifted,[status(thm)],[c_26,c_292]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1144,plain,
% 3.01/1.00      ( v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))
% 3.01/1.00      | ~ v2_pre_topc(sK4)
% 3.01/1.00      | v2_struct_0(sK4)
% 3.01/1.00      | ~ l1_pre_topc(sK4) ),
% 3.01/1.00      inference(unflattening,[status(thm)],[c_1143]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1146,plain,
% 3.01/1.00      ( v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))) ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_1144,c_48,c_47,c_46]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_32,plain,
% 3.01/1.00      ( v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
% 3.01/1.00      | ~ v3_pre_topc(X1,X0)
% 3.01/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.01/1.00      | ~ v2_pre_topc(X0)
% 3.01/1.00      | v2_struct_0(X0)
% 3.01/1.00      | ~ l1_pre_topc(X0) ),
% 3.01/1.00      inference(cnf_transformation,[],[f98]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_36,negated_conjecture,
% 3.01/1.00      ( ~ v5_pre_topc(k9_tmap_1(sK4,sK5),sK4,k8_tmap_1(sK4,sK5))
% 3.01/1.00      | ~ v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))
% 3.01/1.00      | ~ v1_tsep_1(sK5,sK4)
% 3.01/1.00      | ~ m1_pre_topc(sK5,sK4)
% 3.01/1.00      | ~ m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
% 3.01/1.00      | ~ v1_funct_1(k9_tmap_1(sK4,sK5)) ),
% 3.01/1.00      inference(cnf_transformation,[],[f114]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_297,plain,
% 3.01/1.00      ( ~ v1_tsep_1(sK5,sK4)
% 3.01/1.00      | ~ v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))
% 3.01/1.00      | ~ v5_pre_topc(k9_tmap_1(sK4,sK5),sK4,k8_tmap_1(sK4,sK5))
% 3.01/1.00      | ~ m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
% 3.01/1.00      | ~ v1_funct_1(k9_tmap_1(sK4,sK5)) ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_36,c_45]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_298,negated_conjecture,
% 3.01/1.00      ( ~ v5_pre_topc(k9_tmap_1(sK4,sK5),sK4,k8_tmap_1(sK4,sK5))
% 3.01/1.00      | ~ v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))
% 3.01/1.00      | ~ v1_tsep_1(sK5,sK4)
% 3.01/1.00      | ~ m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
% 3.01/1.00      | ~ v1_funct_1(k9_tmap_1(sK4,sK5)) ),
% 3.01/1.00      inference(renaming,[status(thm)],[c_297]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_593,plain,
% 3.01/1.00      ( ~ v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))
% 3.01/1.00      | ~ v3_pre_topc(X0,X1)
% 3.01/1.00      | ~ v1_tsep_1(sK5,sK4)
% 3.01/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/1.00      | ~ m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
% 3.01/1.00      | ~ v2_pre_topc(X1)
% 3.01/1.00      | ~ v1_funct_1(k9_tmap_1(sK4,sK5))
% 3.01/1.00      | v2_struct_0(X1)
% 3.01/1.00      | ~ l1_pre_topc(X1)
% 3.01/1.00      | k6_tmap_1(X1,X0) != k8_tmap_1(sK4,sK5)
% 3.01/1.00      | k7_tmap_1(X1,X0) != k9_tmap_1(sK4,sK5)
% 3.01/1.00      | sK4 != X1 ),
% 3.01/1.00      inference(resolution_lifted,[status(thm)],[c_32,c_298]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_594,plain,
% 3.01/1.00      ( ~ v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))
% 3.01/1.00      | ~ v3_pre_topc(X0,sK4)
% 3.01/1.00      | ~ v1_tsep_1(sK5,sK4)
% 3.01/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.01/1.00      | ~ m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
% 3.01/1.00      | ~ v2_pre_topc(sK4)
% 3.01/1.00      | ~ v1_funct_1(k9_tmap_1(sK4,sK5))
% 3.01/1.00      | v2_struct_0(sK4)
% 3.01/1.00      | ~ l1_pre_topc(sK4)
% 3.01/1.00      | k6_tmap_1(sK4,X0) != k8_tmap_1(sK4,sK5)
% 3.01/1.00      | k7_tmap_1(sK4,X0) != k9_tmap_1(sK4,sK5) ),
% 3.01/1.00      inference(unflattening,[status(thm)],[c_593]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_598,plain,
% 3.01/1.00      ( ~ m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
% 3.01/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.01/1.00      | ~ v1_tsep_1(sK5,sK4)
% 3.01/1.00      | ~ v3_pre_topc(X0,sK4)
% 3.01/1.00      | ~ v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))
% 3.01/1.00      | ~ v1_funct_1(k9_tmap_1(sK4,sK5))
% 3.01/1.00      | k6_tmap_1(sK4,X0) != k8_tmap_1(sK4,sK5)
% 3.01/1.00      | k7_tmap_1(sK4,X0) != k9_tmap_1(sK4,sK5) ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_594,c_48,c_47,c_46]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_599,plain,
% 3.01/1.00      ( ~ v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))
% 3.01/1.00      | ~ v3_pre_topc(X0,sK4)
% 3.01/1.00      | ~ v1_tsep_1(sK5,sK4)
% 3.01/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.01/1.00      | ~ m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
% 3.01/1.00      | ~ v1_funct_1(k9_tmap_1(sK4,sK5))
% 3.01/1.00      | k6_tmap_1(sK4,X0) != k8_tmap_1(sK4,sK5)
% 3.01/1.00      | k7_tmap_1(sK4,X0) != k9_tmap_1(sK4,sK5) ),
% 3.01/1.00      inference(renaming,[status(thm)],[c_598]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1454,plain,
% 3.01/1.00      ( ~ v3_pre_topc(X0,sK4)
% 3.01/1.00      | ~ v1_tsep_1(sK5,sK4)
% 3.01/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.01/1.00      | ~ m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
% 3.01/1.00      | ~ v1_funct_1(k9_tmap_1(sK4,sK5))
% 3.01/1.00      | k6_tmap_1(sK4,X0) != k8_tmap_1(sK4,sK5)
% 3.01/1.00      | k7_tmap_1(sK4,X0) != k9_tmap_1(sK4,sK5) ),
% 3.01/1.00      inference(backward_subsumption_resolution,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_1146,c_599]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1475,plain,
% 3.01/1.00      ( ~ v3_pre_topc(X0,sK4)
% 3.01/1.00      | ~ v1_tsep_1(sK5,sK4)
% 3.01/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.01/1.00      | ~ m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
% 3.01/1.00      | k6_tmap_1(sK4,X0) != k8_tmap_1(sK4,sK5)
% 3.01/1.00      | k7_tmap_1(sK4,X0) != k9_tmap_1(sK4,sK5) ),
% 3.01/1.00      inference(backward_subsumption_resolution,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_1233,c_1454]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1481,plain,
% 3.01/1.00      ( ~ v3_pre_topc(X0,sK4)
% 3.01/1.00      | ~ v1_tsep_1(sK5,sK4)
% 3.01/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.01/1.00      | k6_tmap_1(sK4,X0) != k8_tmap_1(sK4,sK5)
% 3.01/1.00      | k7_tmap_1(sK4,X0) != k9_tmap_1(sK4,sK5) ),
% 3.01/1.00      inference(backward_subsumption_resolution,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_1246,c_1475]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_18,plain,
% 3.01/1.00      ( v3_pre_topc(u1_struct_0(X0),X1)
% 3.01/1.00      | ~ v1_tsep_1(X0,X1)
% 3.01/1.00      | ~ m1_pre_topc(X0,X1)
% 3.01/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/1.00      | ~ l1_pre_topc(X1) ),
% 3.01/1.00      inference(cnf_transformation,[],[f120]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_337,plain,
% 3.01/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.01/1.00      | ~ v1_tsep_1(X0,X1)
% 3.01/1.00      | v3_pre_topc(u1_struct_0(X0),X1)
% 3.01/1.00      | ~ l1_pre_topc(X1) ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_18,c_35]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_338,plain,
% 3.01/1.00      ( v3_pre_topc(u1_struct_0(X0),X1)
% 3.01/1.00      | ~ v1_tsep_1(X0,X1)
% 3.01/1.00      | ~ m1_pre_topc(X0,X1)
% 3.01/1.00      | ~ l1_pre_topc(X1) ),
% 3.01/1.00      inference(renaming,[status(thm)],[c_337]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1203,plain,
% 3.01/1.00      ( v3_pre_topc(u1_struct_0(X0),X1)
% 3.01/1.00      | ~ v1_tsep_1(X0,X1)
% 3.01/1.00      | ~ l1_pre_topc(X1)
% 3.01/1.00      | sK5 != X0
% 3.01/1.00      | sK4 != X1 ),
% 3.01/1.00      inference(resolution_lifted,[status(thm)],[c_338,c_292]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1204,plain,
% 3.01/1.00      ( v3_pre_topc(u1_struct_0(sK5),sK4)
% 3.01/1.00      | ~ v1_tsep_1(sK5,sK4)
% 3.01/1.00      | ~ l1_pre_topc(sK4) ),
% 3.01/1.00      inference(unflattening,[status(thm)],[c_1203]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1206,plain,
% 3.01/1.00      ( ~ v1_tsep_1(sK5,sK4) | v3_pre_topc(u1_struct_0(sK5),sK4) ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_1204,c_46]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1207,plain,
% 3.01/1.00      ( v3_pre_topc(u1_struct_0(sK5),sK4) | ~ v1_tsep_1(sK5,sK4) ),
% 3.01/1.00      inference(renaming,[status(thm)],[c_1206]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1559,plain,
% 3.01/1.00      ( ~ v1_tsep_1(sK5,sK4)
% 3.01/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.01/1.00      | k6_tmap_1(sK4,X0) != k8_tmap_1(sK4,sK5)
% 3.01/1.00      | k7_tmap_1(sK4,X0) != k9_tmap_1(sK4,sK5)
% 3.01/1.00      | u1_struct_0(sK5) != X0
% 3.01/1.00      | sK4 != sK4 ),
% 3.01/1.00      inference(resolution_lifted,[status(thm)],[c_1481,c_1207]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1560,plain,
% 3.01/1.00      ( ~ v1_tsep_1(sK5,sK4)
% 3.01/1.00      | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.01/1.00      | k6_tmap_1(sK4,u1_struct_0(sK5)) != k8_tmap_1(sK4,sK5)
% 3.01/1.00      | k7_tmap_1(sK4,u1_struct_0(sK5)) != k9_tmap_1(sK4,sK5) ),
% 3.01/1.00      inference(unflattening,[status(thm)],[c_1559]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_10,plain,
% 3.01/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.01/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/1.00      | ~ v1_pre_topc(k8_tmap_1(X1,X0))
% 3.01/1.00      | ~ v2_pre_topc(X1)
% 3.01/1.00      | ~ v2_pre_topc(k8_tmap_1(X1,X0))
% 3.01/1.00      | v2_struct_0(X1)
% 3.01/1.00      | ~ l1_pre_topc(X1)
% 3.01/1.00      | ~ l1_pre_topc(k8_tmap_1(X1,X0))
% 3.01/1.00      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 3.01/1.00      inference(cnf_transformation,[],[f117]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_24,plain,
% 3.01/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.01/1.00      | v1_pre_topc(k8_tmap_1(X1,X0))
% 3.01/1.00      | ~ v2_pre_topc(X1)
% 3.01/1.00      | v2_struct_0(X1)
% 3.01/1.00      | ~ l1_pre_topc(X1) ),
% 3.01/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_23,plain,
% 3.01/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.01/1.00      | ~ v2_pre_topc(X1)
% 3.01/1.00      | v2_pre_topc(k8_tmap_1(X1,X0))
% 3.01/1.00      | v2_struct_0(X1)
% 3.01/1.00      | ~ l1_pre_topc(X1) ),
% 3.01/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_22,plain,
% 3.01/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.01/1.00      | ~ v2_pre_topc(X1)
% 3.01/1.00      | v2_struct_0(X1)
% 3.01/1.00      | ~ l1_pre_topc(X1)
% 3.01/1.00      | l1_pre_topc(k8_tmap_1(X1,X0)) ),
% 3.01/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_357,plain,
% 3.01/1.00      ( ~ l1_pre_topc(X1)
% 3.01/1.00      | v2_struct_0(X1)
% 3.01/1.00      | ~ m1_pre_topc(X0,X1)
% 3.01/1.00      | ~ v2_pre_topc(X1)
% 3.01/1.00      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_10,c_35,c_24,c_23,c_22]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_358,plain,
% 3.01/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.01/1.00      | ~ v2_pre_topc(X1)
% 3.01/1.00      | v2_struct_0(X1)
% 3.01/1.00      | ~ l1_pre_topc(X1)
% 3.01/1.00      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 3.01/1.00      inference(renaming,[status(thm)],[c_357]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1195,plain,
% 3.01/1.00      ( ~ v2_pre_topc(X0)
% 3.01/1.00      | v2_struct_0(X0)
% 3.01/1.00      | ~ l1_pre_topc(X0)
% 3.01/1.00      | k6_tmap_1(X0,u1_struct_0(X1)) = k8_tmap_1(X0,X1)
% 3.01/1.00      | sK5 != X1
% 3.01/1.00      | sK4 != X0 ),
% 3.01/1.00      inference(resolution_lifted,[status(thm)],[c_358,c_292]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1196,plain,
% 3.01/1.00      ( ~ v2_pre_topc(sK4)
% 3.01/1.00      | v2_struct_0(sK4)
% 3.01/1.00      | ~ l1_pre_topc(sK4)
% 3.01/1.00      | k6_tmap_1(sK4,u1_struct_0(sK5)) = k8_tmap_1(sK4,sK5) ),
% 3.01/1.00      inference(unflattening,[status(thm)],[c_1195]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1562,plain,
% 3.01/1.00      ( ~ v1_tsep_1(sK5,sK4)
% 3.01/1.00      | k7_tmap_1(sK4,u1_struct_0(sK5)) != k9_tmap_1(sK4,sK5) ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_1560,c_48,c_47,c_46,c_1196,c_1218]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2555,plain,
% 3.01/1.00      ( ~ v1_tsep_1(sK5,sK4)
% 3.01/1.00      | k7_tmap_1(sK4,u1_struct_0(sK5)) != k9_tmap_1(sK4,sK5) ),
% 3.01/1.00      inference(subtyping,[status(esa)],[c_1562]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2626,plain,
% 3.01/1.00      ( k7_tmap_1(sK4,u1_struct_0(sK5)) != k9_tmap_1(sK4,sK5)
% 3.01/1.00      | v1_tsep_1(sK5,sK4) != iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_2555]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2654,plain,
% 3.01/1.00      ( k7_tmap_1(sK4,sK3(sK4,sK5)) != k9_tmap_1(sK4,sK5)
% 3.01/1.00      | k6_tmap_1(sK4,sK3(sK4,sK5)) != k8_tmap_1(sK4,sK5)
% 3.01/1.00      | v1_tsep_1(sK5,sK4) = iProver_top
% 3.01/1.00      | m1_subset_1(k7_tmap_1(sK4,sK3(sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK3(sK4,sK5)))))) != iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_2541]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1198,plain,
% 3.01/1.00      ( k6_tmap_1(sK4,u1_struct_0(sK5)) = k8_tmap_1(sK4,sK5) ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_1196,c_48,c_47,c_46]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2563,plain,
% 3.01/1.00      ( k6_tmap_1(sK4,u1_struct_0(sK5)) = k8_tmap_1(sK4,sK5) ),
% 3.01/1.00      inference(subtyping,[status(esa)],[c_1198]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1637,plain,
% 3.01/1.00      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
% 3.01/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.01/1.00      | ~ v2_pre_topc(X0)
% 3.01/1.00      | ~ l1_pre_topc(X0)
% 3.01/1.00      | sK4 != X0 ),
% 3.01/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_48]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1638,plain,
% 3.01/1.00      ( v1_funct_2(k7_tmap_1(sK4,X0),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X0)))
% 3.01/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.01/1.00      | ~ v2_pre_topc(sK4)
% 3.01/1.00      | ~ l1_pre_topc(sK4) ),
% 3.01/1.00      inference(unflattening,[status(thm)],[c_1637]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1642,plain,
% 3.01/1.00      ( v1_funct_2(k7_tmap_1(sK4,X0),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X0)))
% 3.01/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_1638,c_47,c_46]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2553,plain,
% 3.01/1.00      ( v1_funct_2(k7_tmap_1(sK4,X0_59),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X0_59)))
% 3.01/1.00      | ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 3.01/1.00      inference(subtyping,[status(esa)],[c_1642]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3038,plain,
% 3.01/1.00      ( v1_funct_2(k7_tmap_1(sK4,X0_59),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X0_59))) = iProver_top
% 3.01/1.00      | m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_2553]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3757,plain,
% 3.01/1.00      ( v1_funct_2(k7_tmap_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))) = iProver_top
% 3.01/1.00      | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_2563,c_3038]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1220,plain,
% 3.01/1.00      ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_1218,c_46]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2562,plain,
% 3.01/1.00      ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 3.01/1.00      inference(subtyping,[status(esa)],[c_1220]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3029,plain,
% 3.01/1.00      ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_2562]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_29,plain,
% 3.01/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/1.00      | ~ v2_pre_topc(X1)
% 3.01/1.00      | v2_struct_0(X1)
% 3.01/1.00      | ~ l1_pre_topc(X1)
% 3.01/1.00      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
% 3.01/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1655,plain,
% 3.01/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/1.00      | ~ v2_pre_topc(X1)
% 3.01/1.00      | ~ l1_pre_topc(X1)
% 3.01/1.00      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1)
% 3.01/1.00      | sK4 != X1 ),
% 3.01/1.00      inference(resolution_lifted,[status(thm)],[c_29,c_48]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1656,plain,
% 3.01/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.01/1.00      | ~ v2_pre_topc(sK4)
% 3.01/1.00      | ~ l1_pre_topc(sK4)
% 3.01/1.00      | u1_struct_0(k6_tmap_1(sK4,X0)) = u1_struct_0(sK4) ),
% 3.01/1.00      inference(unflattening,[status(thm)],[c_1655]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1660,plain,
% 3.01/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.01/1.00      | u1_struct_0(k6_tmap_1(sK4,X0)) = u1_struct_0(sK4) ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_1656,c_47,c_46]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2552,plain,
% 3.01/1.00      ( ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.01/1.00      | u1_struct_0(k6_tmap_1(sK4,X0_59)) = u1_struct_0(sK4) ),
% 3.01/1.00      inference(subtyping,[status(esa)],[c_1660]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3039,plain,
% 3.01/1.00      ( u1_struct_0(k6_tmap_1(sK4,X0_59)) = u1_struct_0(sK4)
% 3.01/1.00      | m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_2552]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3551,plain,
% 3.01/1.00      ( u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5))) = u1_struct_0(sK4) ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_3029,c_3039]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3558,plain,
% 3.01/1.00      ( u1_struct_0(k8_tmap_1(sK4,sK5)) = u1_struct_0(sK4) ),
% 3.01/1.00      inference(light_normalisation,[status(thm)],[c_3551,c_2563]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3758,plain,
% 3.01/1.00      ( v1_funct_2(k7_tmap_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK4),u1_struct_0(sK4)) = iProver_top
% 3.01/1.00      | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 3.01/1.00      inference(light_normalisation,[status(thm)],[c_3757,c_3558]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_19,plain,
% 3.01/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/1.00      | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
% 3.01/1.00      | ~ v2_pre_topc(X1)
% 3.01/1.00      | v2_struct_0(X1)
% 3.01/1.00      | ~ l1_pre_topc(X1) ),
% 3.01/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1709,plain,
% 3.01/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/1.00      | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
% 3.01/1.00      | ~ v2_pre_topc(X1)
% 3.01/1.00      | ~ l1_pre_topc(X1)
% 3.01/1.00      | sK4 != X1 ),
% 3.01/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_48]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1710,plain,
% 3.01/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.01/1.00      | m1_subset_1(k7_tmap_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X0)))))
% 3.01/1.00      | ~ v2_pre_topc(sK4)
% 3.01/1.00      | ~ l1_pre_topc(sK4) ),
% 3.01/1.00      inference(unflattening,[status(thm)],[c_1709]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1714,plain,
% 3.01/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.01/1.00      | m1_subset_1(k7_tmap_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X0))))) ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_1710,c_47,c_46]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2549,plain,
% 3.01/1.00      ( ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.01/1.00      | m1_subset_1(k7_tmap_1(sK4,X0_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X0_59))))) ),
% 3.01/1.00      inference(subtyping,[status(esa)],[c_1714]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3042,plain,
% 3.01/1.00      ( m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.01/1.00      | m1_subset_1(k7_tmap_1(sK4,X0_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,X0_59))))) = iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_2549]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3818,plain,
% 3.01/1.00      ( m1_subset_1(k7_tmap_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))))) = iProver_top
% 3.01/1.00      | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_2563,c_3042]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3819,plain,
% 3.01/1.00      ( m1_subset_1(k7_tmap_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) = iProver_top
% 3.01/1.00      | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 3.01/1.00      inference(light_normalisation,[status(thm)],[c_3818,c_3558]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_5,plain,
% 3.01/1.00      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
% 3.01/1.00      | ~ v1_funct_2(X5,X2,X3)
% 3.01/1.00      | ~ v1_funct_2(X4,X0,X1)
% 3.01/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.01/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.01/1.00      | ~ v1_funct_1(X5)
% 3.01/1.00      | ~ v1_funct_1(X4)
% 3.01/1.00      | v1_xboole_0(X1)
% 3.01/1.00      | v1_xboole_0(X3)
% 3.01/1.00      | X4 = X5 ),
% 3.01/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_14,plain,
% 3.01/1.00      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
% 3.01/1.00      | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 3.01/1.00      | ~ m1_pre_topc(X1,X0)
% 3.01/1.00      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 3.01/1.00      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
% 3.01/1.00      | ~ v2_pre_topc(X0)
% 3.01/1.00      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 3.01/1.00      | v2_struct_0(X0)
% 3.01/1.00      | ~ l1_pre_topc(X0) ),
% 3.01/1.00      inference(cnf_transformation,[],[f119]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_347,plain,
% 3.01/1.00      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
% 3.01/1.00      | ~ m1_pre_topc(X1,X0)
% 3.01/1.00      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 3.01/1.00      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
% 3.01/1.00      | ~ v2_pre_topc(X0)
% 3.01/1.00      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 3.01/1.00      | v2_struct_0(X0)
% 3.01/1.00      | ~ l1_pre_topc(X0) ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_14,c_26]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1123,plain,
% 3.01/1.00      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
% 3.01/1.00      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 3.01/1.00      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
% 3.01/1.00      | ~ v2_pre_topc(X0)
% 3.01/1.00      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 3.01/1.00      | v2_struct_0(X0)
% 3.01/1.00      | ~ l1_pre_topc(X0)
% 3.01/1.00      | sK5 != X1
% 3.01/1.00      | sK4 != X0 ),
% 3.01/1.00      inference(resolution_lifted,[status(thm)],[c_347,c_292]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1124,plain,
% 3.01/1.00      ( r1_funct_2(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5))),k9_tmap_1(sK4,sK5),k7_tmap_1(sK4,u1_struct_0(sK5)))
% 3.01/1.00      | ~ m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
% 3.01/1.00      | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.01/1.00      | ~ v2_pre_topc(sK4)
% 3.01/1.00      | ~ v1_funct_1(k9_tmap_1(sK4,sK5))
% 3.01/1.00      | v2_struct_0(sK4)
% 3.01/1.00      | ~ l1_pre_topc(sK4) ),
% 3.01/1.00      inference(unflattening,[status(thm)],[c_1123]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1126,plain,
% 3.01/1.00      ( ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.01/1.00      | ~ m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
% 3.01/1.00      | r1_funct_2(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5))),k9_tmap_1(sK4,sK5),k7_tmap_1(sK4,u1_struct_0(sK5)))
% 3.01/1.00      | ~ v1_funct_1(k9_tmap_1(sK4,sK5)) ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_1124,c_48,c_47,c_46]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1127,plain,
% 3.01/1.00      ( r1_funct_2(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5))),k9_tmap_1(sK4,sK5),k7_tmap_1(sK4,u1_struct_0(sK5)))
% 3.01/1.00      | ~ m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
% 3.01/1.00      | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.01/1.00      | ~ v1_funct_1(k9_tmap_1(sK4,sK5)) ),
% 3.01/1.00      inference(renaming,[status(thm)],[c_1126]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1227,plain,
% 3.01/1.00      ( r1_funct_2(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5))),k9_tmap_1(sK4,sK5),k7_tmap_1(sK4,u1_struct_0(sK5)))
% 3.01/1.00      | ~ m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
% 3.01/1.00      | ~ v1_funct_1(k9_tmap_1(sK4,sK5)) ),
% 3.01/1.00      inference(backward_subsumption_resolution,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_1220,c_1127]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1240,plain,
% 3.01/1.00      ( r1_funct_2(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5))),k9_tmap_1(sK4,sK5),k7_tmap_1(sK4,u1_struct_0(sK5)))
% 3.01/1.00      | ~ m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))))) ),
% 3.01/1.00      inference(backward_subsumption_resolution,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_1233,c_1227]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1253,plain,
% 3.01/1.00      ( r1_funct_2(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5))),k9_tmap_1(sK4,sK5),k7_tmap_1(sK4,u1_struct_0(sK5))) ),
% 3.01/1.00      inference(backward_subsumption_resolution,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_1246,c_1240]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1836,plain,
% 3.01/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.01/1.00      | ~ v1_funct_2(X3,X4,X5)
% 3.01/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.01/1.00      | ~ v1_funct_1(X0)
% 3.01/1.00      | ~ v1_funct_1(X3)
% 3.01/1.00      | v1_xboole_0(X2)
% 3.01/1.00      | v1_xboole_0(X5)
% 3.01/1.00      | X3 = X0
% 3.01/1.00      | k9_tmap_1(sK4,sK5) != X0
% 3.01/1.00      | k7_tmap_1(sK4,u1_struct_0(sK5)) != X3
% 3.01/1.00      | u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5))) != X5
% 3.01/1.00      | u1_struct_0(k8_tmap_1(sK4,sK5)) != X2
% 3.01/1.00      | u1_struct_0(sK4) != X4
% 3.01/1.00      | u1_struct_0(sK4) != X1 ),
% 3.01/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_1253]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1837,plain,
% 3.01/1.00      ( ~ v1_funct_2(k9_tmap_1(sK4,sK5),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))
% 3.01/1.00      | ~ v1_funct_2(k7_tmap_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5))))
% 3.01/1.00      | ~ m1_subset_1(k9_tmap_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5)))))
% 3.01/1.00      | ~ m1_subset_1(k7_tmap_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5))))))
% 3.01/1.00      | ~ v1_funct_1(k9_tmap_1(sK4,sK5))
% 3.01/1.00      | ~ v1_funct_1(k7_tmap_1(sK4,u1_struct_0(sK5)))
% 3.01/1.00      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5))))
% 3.01/1.00      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK4,sK5)))
% 3.01/1.00      | k7_tmap_1(sK4,u1_struct_0(sK5)) = k9_tmap_1(sK4,sK5) ),
% 3.01/1.00      inference(unflattening,[status(thm)],[c_1836]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1839,plain,
% 3.01/1.00      ( ~ m1_subset_1(k7_tmap_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5))))))
% 3.01/1.00      | ~ v1_funct_2(k7_tmap_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5))))
% 3.01/1.00      | ~ v1_funct_1(k7_tmap_1(sK4,u1_struct_0(sK5)))
% 3.01/1.00      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5))))
% 3.01/1.00      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK4,sK5)))
% 3.01/1.00      | k7_tmap_1(sK4,u1_struct_0(sK5)) = k9_tmap_1(sK4,sK5) ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_1837,c_48,c_47,c_46,c_1144,c_1231,c_1244]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1840,plain,
% 3.01/1.00      ( ~ v1_funct_2(k7_tmap_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5))))
% 3.01/1.00      | ~ m1_subset_1(k7_tmap_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5))))))
% 3.01/1.00      | ~ v1_funct_1(k7_tmap_1(sK4,u1_struct_0(sK5)))
% 3.01/1.00      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5))))
% 3.01/1.00      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK4,sK5)))
% 3.01/1.00      | k7_tmap_1(sK4,u1_struct_0(sK5)) = k9_tmap_1(sK4,sK5) ),
% 3.01/1.00      inference(renaming,[status(thm)],[c_1839]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2542,plain,
% 3.01/1.00      ( ~ v1_funct_2(k7_tmap_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5))))
% 3.01/1.00      | ~ m1_subset_1(k7_tmap_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5))))))
% 3.01/1.00      | ~ v1_funct_1(k7_tmap_1(sK4,u1_struct_0(sK5)))
% 3.01/1.00      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5))))
% 3.01/1.00      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK4,sK5)))
% 3.01/1.00      | k7_tmap_1(sK4,u1_struct_0(sK5)) = k9_tmap_1(sK4,sK5) ),
% 3.01/1.00      inference(subtyping,[status(esa)],[c_1840]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3049,plain,
% 3.01/1.00      ( k7_tmap_1(sK4,u1_struct_0(sK5)) = k9_tmap_1(sK4,sK5)
% 3.01/1.00      | v1_funct_2(k7_tmap_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5)))) != iProver_top
% 3.01/1.00      | m1_subset_1(k7_tmap_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5)))))) != iProver_top
% 3.01/1.00      | v1_funct_1(k7_tmap_1(sK4,u1_struct_0(sK5))) != iProver_top
% 3.01/1.00      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5)))) = iProver_top
% 3.01/1.00      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK4,sK5))) = iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_2542]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3135,plain,
% 3.01/1.00      ( k7_tmap_1(sK4,u1_struct_0(sK5)) = k9_tmap_1(sK4,sK5)
% 3.01/1.00      | v1_funct_2(k7_tmap_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))) != iProver_top
% 3.01/1.00      | m1_subset_1(k7_tmap_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))))) != iProver_top
% 3.01/1.00      | v1_funct_1(k7_tmap_1(sK4,u1_struct_0(sK5))) != iProver_top
% 3.01/1.00      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK4,sK5))) = iProver_top ),
% 3.01/1.00      inference(light_normalisation,[status(thm)],[c_3049,c_2563]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_21,plain,
% 3.01/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/1.00      | ~ v2_pre_topc(X1)
% 3.01/1.00      | v1_funct_1(k7_tmap_1(X1,X0))
% 3.01/1.00      | v2_struct_0(X1)
% 3.01/1.00      | ~ l1_pre_topc(X1) ),
% 3.01/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1691,plain,
% 3.01/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/1.00      | ~ v2_pre_topc(X1)
% 3.01/1.00      | v1_funct_1(k7_tmap_1(X1,X0))
% 3.01/1.00      | ~ l1_pre_topc(X1)
% 3.01/1.00      | sK4 != X1 ),
% 3.01/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_48]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1692,plain,
% 3.01/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.01/1.00      | ~ v2_pre_topc(sK4)
% 3.01/1.00      | v1_funct_1(k7_tmap_1(sK4,X0))
% 3.01/1.00      | ~ l1_pre_topc(sK4) ),
% 3.01/1.00      inference(unflattening,[status(thm)],[c_1691]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1696,plain,
% 3.01/1.00      ( v1_funct_1(k7_tmap_1(sK4,X0))
% 3.01/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_1692,c_47,c_46]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1697,plain,
% 3.01/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.01/1.00      | v1_funct_1(k7_tmap_1(sK4,X0)) ),
% 3.01/1.00      inference(renaming,[status(thm)],[c_1696]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2550,plain,
% 3.01/1.00      ( ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.01/1.00      | v1_funct_1(k7_tmap_1(sK4,X0_59)) ),
% 3.01/1.00      inference(subtyping,[status(esa)],[c_1697]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3226,plain,
% 3.01/1.00      ( ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.01/1.00      | v1_funct_1(k7_tmap_1(sK4,u1_struct_0(sK5))) ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_2550]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3227,plain,
% 3.01/1.00      ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.01/1.00      | v1_funct_1(k7_tmap_1(sK4,u1_struct_0(sK5))) = iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_3226]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_4071,plain,
% 3.01/1.00      ( m1_subset_1(k7_tmap_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))))) != iProver_top
% 3.01/1.00      | v1_funct_2(k7_tmap_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))) != iProver_top
% 3.01/1.00      | k7_tmap_1(sK4,u1_struct_0(sK5)) = k9_tmap_1(sK4,sK5)
% 3.01/1.00      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK4,sK5))) = iProver_top ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_3135,c_51,c_1219,c_3227]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_4072,plain,
% 3.01/1.00      ( k7_tmap_1(sK4,u1_struct_0(sK5)) = k9_tmap_1(sK4,sK5)
% 3.01/1.00      | v1_funct_2(k7_tmap_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))) != iProver_top
% 3.01/1.00      | m1_subset_1(k7_tmap_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k8_tmap_1(sK4,sK5))))) != iProver_top
% 3.01/1.00      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK4,sK5))) = iProver_top ),
% 3.01/1.00      inference(renaming,[status(thm)],[c_4071]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_4075,plain,
% 3.01/1.00      ( k7_tmap_1(sK4,u1_struct_0(sK5)) = k9_tmap_1(sK4,sK5)
% 3.01/1.00      | v1_funct_2(k7_tmap_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK4),u1_struct_0(sK4)) != iProver_top
% 3.01/1.00      | m1_subset_1(k7_tmap_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) != iProver_top
% 3.01/1.00      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 3.01/1.00      inference(light_normalisation,[status(thm)],[c_4072,c_3558]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_0,plain,
% 3.01/1.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.01/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1,plain,
% 3.01/1.00      ( v2_struct_0(X0)
% 3.01/1.00      | ~ v1_xboole_0(u1_struct_0(X0))
% 3.01/1.00      | ~ l1_struct_0(X0) ),
% 3.01/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_573,plain,
% 3.01/1.00      ( v2_struct_0(X0)
% 3.01/1.00      | ~ v1_xboole_0(u1_struct_0(X0))
% 3.01/1.00      | ~ l1_pre_topc(X0) ),
% 3.01/1.00      inference(resolution,[status(thm)],[c_0,c_1]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1626,plain,
% 3.01/1.00      ( ~ v1_xboole_0(u1_struct_0(X0)) | ~ l1_pre_topc(X0) | sK4 != X0 ),
% 3.01/1.00      inference(resolution_lifted,[status(thm)],[c_573,c_48]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1627,plain,
% 3.01/1.00      ( ~ v1_xboole_0(u1_struct_0(sK4)) | ~ l1_pre_topc(sK4) ),
% 3.01/1.00      inference(unflattening,[status(thm)],[c_1626]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_165,plain,
% 3.01/1.00      ( v2_struct_0(sK4)
% 3.01/1.00      | ~ v1_xboole_0(u1_struct_0(sK4))
% 3.01/1.00      | ~ l1_struct_0(sK4) ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_168,plain,
% 3.01/1.00      ( ~ l1_pre_topc(sK4) | l1_struct_0(sK4) ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1629,plain,
% 3.01/1.00      ( ~ v1_xboole_0(u1_struct_0(sK4)) ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_1627,c_48,c_46,c_165,c_168]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2554,plain,
% 3.01/1.00      ( ~ v1_xboole_0(u1_struct_0(sK4)) ),
% 3.01/1.00      inference(subtyping,[status(esa)],[c_1629]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3037,plain,
% 3.01/1.00      ( v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_2554]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_4080,plain,
% 3.01/1.00      ( k7_tmap_1(sK4,u1_struct_0(sK5)) = k9_tmap_1(sK4,sK5)
% 3.01/1.00      | v1_funct_2(k7_tmap_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK4),u1_struct_0(sK4)) != iProver_top
% 3.01/1.00      | m1_subset_1(k7_tmap_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) != iProver_top ),
% 3.01/1.00      inference(forward_subsumption_resolution,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_4075,c_3037]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_4789,plain,
% 3.01/1.00      ( k6_tmap_1(sK4,sK3(sK4,sK5)) != k8_tmap_1(sK4,sK5)
% 3.01/1.00      | k7_tmap_1(sK4,sK3(sK4,sK5)) != k9_tmap_1(sK4,sK5)
% 3.01/1.00      | m1_subset_1(k7_tmap_1(sK4,sK3(sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK3(sK4,sK5)))))) != iProver_top ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_3050,c_51,c_1219,c_2626,c_2654,c_3758,c_3819,c_4080]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_4790,plain,
% 3.01/1.00      ( k7_tmap_1(sK4,sK3(sK4,sK5)) != k9_tmap_1(sK4,sK5)
% 3.01/1.00      | k6_tmap_1(sK4,sK3(sK4,sK5)) != k8_tmap_1(sK4,sK5)
% 3.01/1.00      | m1_subset_1(k7_tmap_1(sK4,sK3(sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK3(sK4,sK5)))))) != iProver_top ),
% 3.01/1.00      inference(renaming,[status(thm)],[c_4789]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_6,plain,
% 3.01/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/1.00      | ~ v2_pre_topc(X1)
% 3.01/1.00      | v2_struct_0(X1)
% 3.01/1.00      | ~ l1_pre_topc(X1)
% 3.01/1.00      | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1)) ),
% 3.01/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1727,plain,
% 3.01/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/1.00      | ~ v2_pre_topc(X1)
% 3.01/1.00      | ~ l1_pre_topc(X1)
% 3.01/1.00      | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1))
% 3.01/1.00      | sK4 != X1 ),
% 3.01/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_48]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1728,plain,
% 3.01/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.01/1.00      | ~ v2_pre_topc(sK4)
% 3.01/1.00      | ~ l1_pre_topc(sK4)
% 3.01/1.00      | k7_tmap_1(sK4,X0) = k6_partfun1(u1_struct_0(sK4)) ),
% 3.01/1.00      inference(unflattening,[status(thm)],[c_1727]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1732,plain,
% 3.01/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.01/1.00      | k7_tmap_1(sK4,X0) = k6_partfun1(u1_struct_0(sK4)) ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_1728,c_47,c_46]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2548,plain,
% 3.01/1.00      ( ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.01/1.00      | k7_tmap_1(sK4,X0_59) = k6_partfun1(u1_struct_0(sK4)) ),
% 3.01/1.00      inference(subtyping,[status(esa)],[c_1732]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3043,plain,
% 3.01/1.00      ( k7_tmap_1(sK4,X0_59) = k6_partfun1(u1_struct_0(sK4))
% 3.01/1.00      | m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_2548]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3661,plain,
% 3.01/1.00      ( k7_tmap_1(sK4,u1_struct_0(sK5)) = k6_partfun1(u1_struct_0(sK4)) ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_3029,c_3043]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_16,plain,
% 3.01/1.00      ( v1_tsep_1(X0,X1)
% 3.01/1.00      | ~ m1_pre_topc(X0,X1)
% 3.01/1.00      | ~ l1_pre_topc(X1)
% 3.01/1.00      | sK3(X1,X0) = u1_struct_0(X0) ),
% 3.01/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1303,plain,
% 3.01/1.00      ( v1_tsep_1(X0,X1)
% 3.01/1.00      | ~ l1_pre_topc(X1)
% 3.01/1.00      | sK3(X1,X0) = u1_struct_0(X0)
% 3.01/1.00      | sK5 != X0
% 3.01/1.00      | sK4 != X1 ),
% 3.01/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_292]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1304,plain,
% 3.01/1.00      ( v1_tsep_1(sK5,sK4)
% 3.01/1.00      | ~ l1_pre_topc(sK4)
% 3.01/1.00      | sK3(sK4,sK5) = u1_struct_0(sK5) ),
% 3.01/1.00      inference(unflattening,[status(thm)],[c_1303]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1306,plain,
% 3.01/1.00      ( v1_tsep_1(sK5,sK4) | sK3(sK4,sK5) = u1_struct_0(sK5) ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_1304,c_46]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2558,plain,
% 3.01/1.00      ( v1_tsep_1(sK5,sK4) | sK3(sK4,sK5) = u1_struct_0(sK5) ),
% 3.01/1.00      inference(subtyping,[status(esa)],[c_1306]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3033,plain,
% 3.01/1.00      ( sK3(sK4,sK5) = u1_struct_0(sK5)
% 3.01/1.00      | v1_tsep_1(sK5,sK4) = iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_2558]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3036,plain,
% 3.01/1.00      ( k7_tmap_1(sK4,u1_struct_0(sK5)) != k9_tmap_1(sK4,sK5)
% 3.01/1.00      | v1_tsep_1(sK5,sK4) != iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_2555]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_4373,plain,
% 3.01/1.00      ( v1_tsep_1(sK5,sK4) != iProver_top ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_3036,c_51,c_1219,c_2626,c_3758,c_3819,c_4080]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_4378,plain,
% 3.01/1.00      ( sK3(sK4,sK5) = u1_struct_0(sK5) ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_3033,c_4373]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_4793,plain,
% 3.01/1.00      ( k9_tmap_1(sK4,sK5) != k6_partfun1(u1_struct_0(sK4))
% 3.01/1.00      | k8_tmap_1(sK4,sK5) != k8_tmap_1(sK4,sK5)
% 3.01/1.00      | m1_subset_1(k6_partfun1(u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) != iProver_top ),
% 3.01/1.00      inference(light_normalisation,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_4790,c_2563,c_3558,c_3661,c_4378]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_4794,plain,
% 3.01/1.00      ( k9_tmap_1(sK4,sK5) != k6_partfun1(u1_struct_0(sK4))
% 3.01/1.00      | m1_subset_1(k6_partfun1(u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) != iProver_top ),
% 3.01/1.00      inference(equality_resolution_simp,[status(thm)],[c_4793]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_4153,plain,
% 3.01/1.00      ( m1_subset_1(k6_partfun1(u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,u1_struct_0(sK5)))))) = iProver_top
% 3.01/1.00      | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_3661,c_3042]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_4162,plain,
% 3.01/1.00      ( m1_subset_1(k6_partfun1(u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) = iProver_top
% 3.01/1.00      | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 3.01/1.00      inference(light_normalisation,[status(thm)],[c_4153,c_2563,c_3558]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3,plain,
% 3.01/1.00      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.01/1.00      | ~ l1_pre_topc(X0) ),
% 3.01/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_158,plain,
% 3.01/1.00      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 3.01/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_160,plain,
% 3.01/1.00      ( m1_subset_1(sK0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 3.01/1.00      | l1_pre_topc(sK4) != iProver_top ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_158]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1765,plain,
% 3.01/1.00      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) | sK4 != X0 ),
% 3.01/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_46]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1766,plain,
% 3.01/1.00      ( m1_subset_1(sK0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 3.01/1.00      inference(unflattening,[status(thm)],[c_1765]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2547,plain,
% 3.01/1.00      ( m1_subset_1(sK0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 3.01/1.00      inference(subtyping,[status(esa)],[c_1766]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3044,plain,
% 3.01/1.00      ( m1_subset_1(sK0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_2547]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3660,plain,
% 3.01/1.00      ( k7_tmap_1(sK4,sK0(sK4)) = k6_partfun1(u1_struct_0(sK4)) ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_3044,c_3043]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3971,plain,
% 3.01/1.00      ( m1_subset_1(k6_partfun1(u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(k6_tmap_1(sK4,sK0(sK4)))))) = iProver_top
% 3.01/1.00      | m1_subset_1(sK0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_3660,c_3042]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3550,plain,
% 3.01/1.00      ( u1_struct_0(k6_tmap_1(sK4,sK0(sK4))) = u1_struct_0(sK4) ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_3044,c_3039]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3980,plain,
% 3.01/1.00      ( m1_subset_1(k6_partfun1(u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) = iProver_top
% 3.01/1.00      | m1_subset_1(sK0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 3.01/1.00      inference(light_normalisation,[status(thm)],[c_3971,c_3550]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_4253,plain,
% 3.01/1.00      ( m1_subset_1(k6_partfun1(u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) = iProver_top ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_4162,c_51,c_160,c_3980]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_4797,plain,
% 3.01/1.00      ( k9_tmap_1(sK4,sK5) != k6_partfun1(u1_struct_0(sK4)) ),
% 3.01/1.00      inference(forward_subsumption_resolution,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_4794,c_4253]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_4082,plain,
% 3.01/1.00      ( k7_tmap_1(sK4,u1_struct_0(sK5)) = k9_tmap_1(sK4,sK5) ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_4080,c_51,c_1219,c_3758,c_3819]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_4152,plain,
% 3.01/1.00      ( k9_tmap_1(sK4,sK5) = k6_partfun1(u1_struct_0(sK4)) ),
% 3.01/1.00      inference(demodulation,[status(thm)],[c_3661,c_4082]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(contradiction,plain,
% 3.01/1.00      ( $false ),
% 3.01/1.00      inference(minisat,[status(thm)],[c_4797,c_4152]) ).
% 3.01/1.00  
% 3.01/1.00  
% 3.01/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.01/1.00  
% 3.01/1.00  ------                               Statistics
% 3.01/1.00  
% 3.01/1.00  ------ General
% 3.01/1.00  
% 3.01/1.00  abstr_ref_over_cycles:                  0
% 3.01/1.00  abstr_ref_under_cycles:                 0
% 3.01/1.00  gc_basic_clause_elim:                   0
% 3.01/1.00  forced_gc_time:                         0
% 3.01/1.00  parsing_time:                           0.014
% 3.01/1.00  unif_index_cands_time:                  0.
% 3.01/1.00  unif_index_add_time:                    0.
% 3.01/1.00  orderings_time:                         0.
% 3.01/1.00  out_proof_time:                         0.031
% 3.01/1.00  total_time:                             0.258
% 3.01/1.00  num_of_symbols:                         68
% 3.01/1.00  num_of_terms:                           4362
% 3.01/1.00  
% 3.01/1.00  ------ Preprocessing
% 3.01/1.00  
% 3.01/1.00  num_of_splits:                          0
% 3.01/1.00  num_of_split_atoms:                     0
% 3.01/1.00  num_of_reused_defs:                     0
% 3.01/1.00  num_eq_ax_congr_red:                    19
% 3.01/1.00  num_of_sem_filtered_clauses:            6
% 3.01/1.00  num_of_subtypes:                        4
% 3.01/1.00  monotx_restored_types:                  0
% 3.01/1.00  sat_num_of_epr_types:                   0
% 3.01/1.00  sat_num_of_non_cyclic_types:            0
% 3.01/1.00  sat_guarded_non_collapsed_types:        1
% 3.01/1.00  num_pure_diseq_elim:                    0
% 3.01/1.00  simp_replaced_by:                       0
% 3.01/1.00  res_preprocessed:                       160
% 3.01/1.00  prep_upred:                             0
% 3.01/1.00  prep_unflattend:                        118
% 3.01/1.00  smt_new_axioms:                         0
% 3.01/1.00  pred_elim_cands:                        5
% 3.01/1.00  pred_elim:                              9
% 3.01/1.00  pred_elim_cl:                           18
% 3.01/1.00  pred_elim_cycles:                       18
% 3.01/1.00  merged_defs:                            0
% 3.01/1.00  merged_defs_ncl:                        0
% 3.01/1.00  bin_hyper_res:                          0
% 3.01/1.00  prep_cycles:                            4
% 3.01/1.00  pred_elim_time:                         0.078
% 3.01/1.00  splitting_time:                         0.
% 3.01/1.00  sem_filter_time:                        0.
% 3.01/1.00  monotx_time:                            0.
% 3.01/1.00  subtype_inf_time:                       0.
% 3.01/1.00  
% 3.01/1.00  ------ Problem properties
% 3.01/1.00  
% 3.01/1.00  clauses:                                24
% 3.01/1.00  conjectures:                            0
% 3.01/1.00  epr:                                    0
% 3.01/1.00  horn:                                   18
% 3.01/1.00  ground:                                 15
% 3.01/1.00  unary:                                  10
% 3.01/1.00  binary:                                 9
% 3.01/1.00  lits:                                   57
% 3.01/1.00  lits_eq:                                14
% 3.01/1.00  fd_pure:                                0
% 3.01/1.00  fd_pseudo:                              0
% 3.01/1.00  fd_cond:                                3
% 3.01/1.00  fd_pseudo_cond:                         0
% 3.01/1.00  ac_symbols:                             0
% 3.01/1.00  
% 3.01/1.00  ------ Propositional Solver
% 3.01/1.00  
% 3.01/1.00  prop_solver_calls:                      27
% 3.01/1.00  prop_fast_solver_calls:                 1730
% 3.01/1.00  smt_solver_calls:                       0
% 3.01/1.00  smt_fast_solver_calls:                  0
% 3.01/1.00  prop_num_of_clauses:                    1289
% 3.01/1.00  prop_preprocess_simplified:             5080
% 3.01/1.00  prop_fo_subsumed:                       105
% 3.01/1.00  prop_solver_time:                       0.
% 3.01/1.00  smt_solver_time:                        0.
% 3.01/1.00  smt_fast_solver_time:                   0.
% 3.01/1.00  prop_fast_solver_time:                  0.
% 3.01/1.00  prop_unsat_core_time:                   0.
% 3.01/1.00  
% 3.01/1.00  ------ QBF
% 3.01/1.00  
% 3.01/1.00  qbf_q_res:                              0
% 3.01/1.00  qbf_num_tautologies:                    0
% 3.01/1.00  qbf_prep_cycles:                        0
% 3.01/1.00  
% 3.01/1.00  ------ BMC1
% 3.01/1.00  
% 3.01/1.00  bmc1_current_bound:                     -1
% 3.01/1.00  bmc1_last_solved_bound:                 -1
% 3.01/1.00  bmc1_unsat_core_size:                   -1
% 3.01/1.00  bmc1_unsat_core_parents_size:           -1
% 3.01/1.00  bmc1_merge_next_fun:                    0
% 3.01/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.01/1.00  
% 3.01/1.00  ------ Instantiation
% 3.01/1.00  
% 3.01/1.00  inst_num_of_clauses:                    329
% 3.01/1.00  inst_num_in_passive:                    88
% 3.01/1.00  inst_num_in_active:                     205
% 3.01/1.00  inst_num_in_unprocessed:                36
% 3.01/1.00  inst_num_of_loops:                      210
% 3.01/1.00  inst_num_of_learning_restarts:          0
% 3.01/1.00  inst_num_moves_active_passive:          1
% 3.01/1.00  inst_lit_activity:                      0
% 3.01/1.00  inst_lit_activity_moves:                0
% 3.01/1.00  inst_num_tautologies:                   0
% 3.01/1.00  inst_num_prop_implied:                  0
% 3.01/1.00  inst_num_existing_simplified:           0
% 3.01/1.00  inst_num_eq_res_simplified:             0
% 3.01/1.00  inst_num_child_elim:                    0
% 3.01/1.00  inst_num_of_dismatching_blockings:      50
% 3.01/1.00  inst_num_of_non_proper_insts:           274
% 3.01/1.00  inst_num_of_duplicates:                 0
% 3.01/1.00  inst_inst_num_from_inst_to_res:         0
% 3.01/1.00  inst_dismatching_checking_time:         0.
% 3.01/1.00  
% 3.01/1.00  ------ Resolution
% 3.01/1.00  
% 3.01/1.00  res_num_of_clauses:                     0
% 3.01/1.00  res_num_in_passive:                     0
% 3.01/1.00  res_num_in_active:                      0
% 3.01/1.00  res_num_of_loops:                       164
% 3.01/1.00  res_forward_subset_subsumed:            50
% 3.01/1.00  res_backward_subset_subsumed:           7
% 3.01/1.00  res_forward_subsumed:                   1
% 3.01/1.00  res_backward_subsumed:                  3
% 3.01/1.00  res_forward_subsumption_resolution:     14
% 3.01/1.00  res_backward_subsumption_resolution:    6
% 3.01/1.00  res_clause_to_clause_subsumption:       239
% 3.01/1.00  res_orphan_elimination:                 0
% 3.01/1.00  res_tautology_del:                      89
% 3.01/1.00  res_num_eq_res_simplified:              0
% 3.01/1.00  res_num_sel_changes:                    0
% 3.01/1.00  res_moves_from_active_to_pass:          0
% 3.01/1.00  
% 3.01/1.00  ------ Superposition
% 3.01/1.00  
% 3.01/1.00  sup_time_total:                         0.
% 3.01/1.00  sup_time_generating:                    0.
% 3.01/1.00  sup_time_sim_full:                      0.
% 3.01/1.00  sup_time_sim_immed:                     0.
% 3.01/1.00  
% 3.01/1.00  sup_num_of_clauses:                     40
% 3.01/1.00  sup_num_in_active:                      33
% 3.01/1.00  sup_num_in_passive:                     7
% 3.01/1.00  sup_num_of_loops:                       41
% 3.01/1.00  sup_fw_superposition:                   15
% 3.01/1.00  sup_bw_superposition:                   20
% 3.01/1.00  sup_immediate_simplified:               18
% 3.01/1.00  sup_given_eliminated:                   0
% 3.01/1.00  comparisons_done:                       0
% 3.01/1.00  comparisons_avoided:                    0
% 3.01/1.00  
% 3.01/1.00  ------ Simplifications
% 3.01/1.00  
% 3.01/1.00  
% 3.01/1.00  sim_fw_subset_subsumed:                 5
% 3.01/1.00  sim_bw_subset_subsumed:                 3
% 3.01/1.00  sim_fw_subsumed:                        2
% 3.01/1.00  sim_bw_subsumed:                        0
% 3.01/1.00  sim_fw_subsumption_res:                 2
% 3.01/1.00  sim_bw_subsumption_res:                 0
% 3.01/1.00  sim_tautology_del:                      0
% 3.01/1.00  sim_eq_tautology_del:                   2
% 3.01/1.00  sim_eq_res_simp:                        1
% 3.01/1.00  sim_fw_demodulated:                     0
% 3.01/1.00  sim_bw_demodulated:                     8
% 3.01/1.00  sim_light_normalised:                   23
% 3.01/1.00  sim_joinable_taut:                      0
% 3.01/1.00  sim_joinable_simp:                      0
% 3.01/1.00  sim_ac_normalised:                      0
% 3.01/1.00  sim_smt_subsumption:                    0
% 3.01/1.00  
%------------------------------------------------------------------------------
