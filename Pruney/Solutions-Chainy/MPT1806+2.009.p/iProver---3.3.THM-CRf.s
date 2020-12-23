%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:15 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :  262 (6422 expanded)
%              Number of clauses        :  166 (1313 expanded)
%              Number of leaves         :   19 (1480 expanded)
%              Depth                    :   33
%              Number of atoms          : 1413 (71384 expanded)
%              Number of equality atoms :  265 (1789 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

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

fof(f85,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k9_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f57,plain,(
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
    inference(nnf_transformation,[],[f41])).

fof(f58,plain,(
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
    inference(flattening,[],[f57])).

fof(f60,plain,(
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

fof(f59,plain,
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

fof(f61,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f58,f60,f59])).

fof(f107,plain,
    ( m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f61])).

fof(f99,plain,(
    m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f61])).

fof(f96,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f61])).

fof(f97,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f61])).

fof(f98,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f61])).

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

fof(f37,plain,(
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
    inference(flattening,[],[f37])).

fof(f55,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f56,plain,(
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
    inference(flattening,[],[f55])).

fof(f94,plain,(
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
    inference(cnf_transformation,[],[f56])).

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

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

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

fof(f80,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f104,plain,
    ( v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4))
    | v1_tsep_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f61])).

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

fof(f27,plain,(
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
    inference(flattening,[],[f27])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f52,plain,(
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
    inference(rectify,[],[f51])).

fof(f53,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK2(X0,X1),X0)
        & u1_struct_0(X1) = sK2(X0,X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f52,f53])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(sK2(X0,X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f62,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f95,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f86,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f108,plain,
    ( ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4))
    | ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
    | ~ m1_pre_topc(sK4,sK3)
    | ~ v1_tsep_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f61])).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( v3_pre_topc(X3,X0)
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f114,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f75])).

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

fof(f23,plain,(
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
    inference(flattening,[],[f23])).

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
    inference(nnf_transformation,[],[f24])).

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

fof(f67,plain,(
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

fof(f110,plain,(
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
    inference(equality_resolution,[],[f67])).

fof(f111,plain,(
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
    inference(equality_resolution,[],[f110])).

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

fof(f31,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

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

fof(f82,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f84,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

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

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

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

fof(f88,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f22])).

fof(f65,plain,(
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

fof(f25,plain,(
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
    inference(flattening,[],[f25])).

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
    inference(nnf_transformation,[],[f26])).

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

fof(f71,plain,(
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

fof(f112,plain,(
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
    inference(equality_resolution,[],[f71])).

fof(f113,plain,(
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
    inference(equality_resolution,[],[f112])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v2_struct_0(X0) )
     => v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f63,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | u1_struct_0(X1) = sK2(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_25,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k9_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_35,negated_conjecture,
    ( m1_pre_topc(sK4,sK3)
    | m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_43,negated_conjecture,
    ( m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_278,negated_conjecture,
    ( m1_pre_topc(sK4,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_35,c_43])).

cnf(c_1219,plain,
    ( ~ v2_pre_topc(X0)
    | v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_278])).

cnf(c_1220,plain,
    ( ~ v2_pre_topc(sK3)
    | v1_funct_1(k9_tmap_1(sK3,sK4))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1219])).

cnf(c_46,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_45,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_44,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1222,plain,
    ( v1_funct_1(k9_tmap_1(sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1220,c_46,c_45,c_44])).

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
    inference(cnf_transformation,[],[f94])).

cnf(c_18,plain,
    ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_305,plain,
    ( ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
    | v3_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k7_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_28,c_18])).

cnf(c_38,negated_conjecture,
    ( v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4))
    | v1_tsep_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_618,plain,
    ( v3_pre_topc(X0,X1)
    | v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(k7_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k7_tmap_1(X1,X0) != k9_tmap_1(sK3,sK4)
    | k6_tmap_1(X1,X0) != k8_tmap_1(sK3,sK4)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_305,c_38])).

cnf(c_619,plain,
    ( v3_pre_topc(X0,sK3)
    | v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))))
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(k7_tmap_1(sK3,X0))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4)
    | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_618])).

cnf(c_623,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_tsep_1(sK4,sK3)
    | v3_pre_topc(X0,sK3)
    | ~ v1_funct_1(k7_tmap_1(sK3,X0))
    | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4)
    | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_619,c_46,c_45,c_44])).

cnf(c_624,plain,
    ( v3_pre_topc(X0,sK3)
    | v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))))
    | ~ v1_funct_1(k7_tmap_1(sK3,X0))
    | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4)
    | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4) ),
    inference(renaming,[status(thm)],[c_623])).

cnf(c_13,plain,
    ( ~ v3_pre_topc(sK2(X0,X1),X0)
    | v1_tsep_1(X1,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1143,plain,
    ( ~ v3_pre_topc(sK2(X0,X1),X0)
    | v1_tsep_1(X1,X0)
    | ~ l1_pre_topc(X0)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_278])).

cnf(c_1144,plain,
    ( ~ v3_pre_topc(sK2(sK3,sK4),sK3)
    | v1_tsep_1(sK4,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1143])).

cnf(c_1146,plain,
    ( v1_tsep_1(sK4,sK3)
    | ~ v3_pre_topc(sK2(sK3,sK4),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1144,c_44])).

cnf(c_1147,plain,
    ( ~ v3_pre_topc(sK2(sK3,sK4),sK3)
    | v1_tsep_1(sK4,sK3) ),
    inference(renaming,[status(thm)],[c_1146])).

cnf(c_1525,plain,
    ( v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))))
    | ~ v1_funct_1(k7_tmap_1(sK3,X0))
    | sK2(sK3,sK4) != X0
    | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4)
    | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_624,c_1147])).

cnf(c_1526,plain,
    ( v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(sK2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4))))))
    | ~ v1_funct_1(k7_tmap_1(sK3,sK2(sK3,sK4)))
    | k7_tmap_1(sK3,sK2(sK3,sK4)) != k9_tmap_1(sK3,sK4)
    | k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_1525])).

cnf(c_15,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1278,plain,
    ( v1_tsep_1(X0,X1)
    | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK4 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_278])).

cnf(c_1279,plain,
    ( v1_tsep_1(sK4,sK3)
    | m1_subset_1(sK2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1278])).

cnf(c_1528,plain,
    ( v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4))))))
    | ~ v1_funct_1(k7_tmap_1(sK3,sK2(sK3,sK4)))
    | k7_tmap_1(sK3,sK2(sK3,sK4)) != k9_tmap_1(sK3,sK4)
    | k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1526,c_44,c_1279])).

cnf(c_2316,plain,
    ( v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4))))))
    | k7_tmap_1(sK3,sK2(sK3,sK4)) != k9_tmap_1(sK3,sK4)
    | k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4) ),
    inference(resolution_lifted,[status(thm)],[c_1222,c_1528])).

cnf(c_3751,plain,
    ( v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4))))))
    | k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,sK2(sK3,sK4)) != k9_tmap_1(sK3,sK4) ),
    inference(subtyping,[status(esa)],[c_2316])).

cnf(c_4504,plain,
    ( k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,sK2(sK3,sK4)) != k9_tmap_1(sK3,sK4)
    | v1_tsep_1(sK4,sK3) = iProver_top
    | m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4)))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3751])).

cnf(c_47,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_49,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_2,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_153,plain,
    ( v2_struct_0(X0) = iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_155,plain,
    ( v2_struct_0(sK3) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top
    | l1_struct_0(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_153])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_157,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_159,plain,
    ( l1_pre_topc(sK3) != iProver_top
    | l1_struct_0(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_157])).

cnf(c_33,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1206,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK4 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_278])).

cnf(c_1207,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1206])).

cnf(c_1208,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1207])).

cnf(c_23,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(k9_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X0)))))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1232,plain,
    ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_278])).

cnf(c_1233,plain,
    ( m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1232])).

cnf(c_1235,plain,
    ( m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1233,c_46,c_45,c_44])).

cnf(c_24,plain,
    ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1132,plain,
    ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_278])).

cnf(c_1133,plain,
    ( v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1132])).

cnf(c_1135,plain,
    ( v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1133,c_46,c_45,c_44])).

cnf(c_30,plain,
    ( v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
    | ~ v3_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_34,negated_conjecture,
    ( ~ v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4))
    | ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ v1_tsep_1(sK4,sK3)
    | ~ m1_pre_topc(sK4,sK3)
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4)) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_283,plain,
    ( ~ v1_tsep_1(sK4,sK3)
    | ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_34,c_43])).

cnf(c_284,negated_conjecture,
    ( ~ v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4))
    | ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4)) ),
    inference(renaming,[status(thm)],[c_283])).

cnf(c_582,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ v3_pre_topc(X0,X1)
    | ~ v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k7_tmap_1(X1,X0) != k9_tmap_1(sK3,sK4)
    | k6_tmap_1(X1,X0) != k8_tmap_1(sK3,sK4)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_284])).

cnf(c_583,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ v3_pre_topc(X0,sK3)
    | ~ v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4)
    | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_582])).

cnf(c_587,plain,
    ( ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_tsep_1(sK4,sK3)
    | ~ v3_pre_topc(X0,sK3)
    | ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
    | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4)
    | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_583,c_46,c_45,c_44])).

cnf(c_588,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ v3_pre_topc(X0,sK3)
    | ~ v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
    | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4)
    | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4) ),
    inference(renaming,[status(thm)],[c_587])).

cnf(c_1443,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
    | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4)
    | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1135,c_588])).

cnf(c_1464,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4)
    | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1222,c_1443])).

cnf(c_1470,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4)
    | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1235,c_1464])).

cnf(c_16,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_323,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16,c_33])).

cnf(c_324,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_323])).

cnf(c_1192,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK4 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_324,c_278])).

cnf(c_1193,plain,
    ( v3_pre_topc(u1_struct_0(sK4),sK3)
    | ~ v1_tsep_1(sK4,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1192])).

cnf(c_1195,plain,
    ( ~ v1_tsep_1(sK4,sK3)
    | v3_pre_topc(u1_struct_0(sK4),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1193,c_44])).

cnf(c_1196,plain,
    ( v3_pre_topc(u1_struct_0(sK4),sK3)
    | ~ v1_tsep_1(sK4,sK3) ),
    inference(renaming,[status(thm)],[c_1195])).

cnf(c_1548,plain,
    ( ~ v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4)
    | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
    | u1_struct_0(sK4) != X0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_1470,c_1196])).

cnf(c_1549,plain,
    ( ~ v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | k7_tmap_1(sK3,u1_struct_0(sK4)) != k9_tmap_1(sK3,sK4)
    | k6_tmap_1(sK3,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_1548])).

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
    inference(cnf_transformation,[],[f111])).

cnf(c_22,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_21,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k8_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_20,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_343,plain,
    ( ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8,c_33,c_22,c_21,c_20])).

cnf(c_344,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(renaming,[status(thm)],[c_343])).

cnf(c_1184,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k6_tmap_1(X0,u1_struct_0(X1)) = k8_tmap_1(X0,X1)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_344,c_278])).

cnf(c_1185,plain,
    ( ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_1184])).

cnf(c_1551,plain,
    ( k7_tmap_1(sK3,u1_struct_0(sK4)) != k9_tmap_1(sK3,sK4)
    | ~ v1_tsep_1(sK4,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1549,c_46,c_45,c_44,c_1185,c_1207])).

cnf(c_1552,plain,
    ( ~ v1_tsep_1(sK4,sK3)
    | k7_tmap_1(sK3,u1_struct_0(sK4)) != k9_tmap_1(sK3,sK4) ),
    inference(renaming,[status(thm)],[c_1551])).

cnf(c_3765,plain,
    ( ~ v1_tsep_1(sK4,sK3)
    | k7_tmap_1(sK3,u1_struct_0(sK4)) != k9_tmap_1(sK3,sK4) ),
    inference(subtyping,[status(esa)],[c_1552])).

cnf(c_1209,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1207,c_44])).

cnf(c_3772,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subtyping,[status(esa)],[c_1209])).

cnf(c_4483,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3772])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1734,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_45])).

cnf(c_1735,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | u1_struct_0(k6_tmap_1(sK3,X0)) = u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_1734])).

cnf(c_1739,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | u1_struct_0(k6_tmap_1(sK3,X0)) = u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1735,c_46,c_44])).

cnf(c_3762,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3)))
    | u1_struct_0(k6_tmap_1(sK3,X0_56)) = u1_struct_0(sK3) ),
    inference(subtyping,[status(esa)],[c_1739])).

cnf(c_4493,plain,
    ( u1_struct_0(k6_tmap_1(sK3,X0_56)) = u1_struct_0(sK3)
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3762])).

cnf(c_4907,plain,
    ( u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))) = u1_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_4483,c_4493])).

cnf(c_1187,plain,
    ( k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1185,c_46,c_45,c_44])).

cnf(c_3773,plain,
    ( k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4) ),
    inference(subtyping,[status(esa)],[c_1187])).

cnf(c_4914,plain,
    ( u1_struct_0(k8_tmap_1(sK3,sK4)) = u1_struct_0(sK3) ),
    inference(light_normalisation,[status(thm)],[c_4907,c_3773])).

cnf(c_4,plain,
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
    inference(cnf_transformation,[],[f65])).

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
    inference(cnf_transformation,[],[f113])).

cnf(c_333,plain,
    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_24])).

cnf(c_1112,plain,
    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
    | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_333,c_278])).

cnf(c_1113,plain,
    ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1112])).

cnf(c_1115,plain,
    ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1113,c_46,c_45,c_44])).

cnf(c_1116,plain,
    ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4)) ),
    inference(renaming,[status(thm)],[c_1115])).

cnf(c_1216,plain,
    ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1209,c_1116])).

cnf(c_1229,plain,
    ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1222,c_1216])).

cnf(c_1242,plain,
    ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1235,c_1229])).

cnf(c_1650,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X5)
    | X3 = X0
    | k7_tmap_1(sK3,u1_struct_0(sK4)) != X3
    | k9_tmap_1(sK3,sK4) != X0
    | u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))) != X5
    | u1_struct_0(k8_tmap_1(sK3,sK4)) != X2
    | u1_struct_0(sK3) != X4
    | u1_struct_0(sK3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_1242])).

cnf(c_1651,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
    | ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4)))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4)))
    | k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_1650])).

cnf(c_1653,plain,
    ( ~ v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4)))
    | ~ v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
    | ~ m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4)))
    | k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1651,c_46,c_45,c_44,c_1133,c_1220,c_1233])).

cnf(c_1654,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
    | ~ m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))))
    | ~ v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4)))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4)))
    | k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4) ),
    inference(renaming,[status(thm)],[c_1653])).

cnf(c_546,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_0,c_2])).

cnf(c_1267,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(k8_tmap_1(X0,X1))
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_278])).

cnf(c_1268,plain,
    ( ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | l1_pre_topc(k8_tmap_1(sK3,sK4))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1267])).

cnf(c_1270,plain,
    ( l1_pre_topc(k8_tmap_1(sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1268,c_46,c_45,c_44])).

cnf(c_1948,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | k8_tmap_1(sK3,sK4) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_546,c_1270])).

cnf(c_1949,plain,
    ( v2_struct_0(k8_tmap_1(sK3,sK4))
    | ~ v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4))) ),
    inference(unflattening,[status(thm)],[c_1948])).

cnf(c_2851,plain,
    ( v2_struct_0(k8_tmap_1(sK3,sK4))
    | ~ v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4))) ),
    inference(prop_impl,[status(thm)],[c_1949])).

cnf(c_2902,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
    | ~ m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))))
    | ~ v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4)))
    | v2_struct_0(k8_tmap_1(sK3,sK4))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
    | k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4) ),
    inference(bin_hyper_res,[status(thm)],[c_1654,c_2851])).

cnf(c_3749,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
    | ~ m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))))
    | ~ v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4)))
    | v2_struct_0(k8_tmap_1(sK3,sK4))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
    | k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4) ),
    inference(subtyping,[status(esa)],[c_2902])).

cnf(c_4506,plain,
    ( k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4)
    | v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4))) != iProver_top
    | v2_struct_0(k8_tmap_1(sK3,sK4)) = iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3749])).

cnf(c_4619,plain,
    ( k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4)
    | v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4))) != iProver_top
    | v2_struct_0(k8_tmap_1(sK3,sK4)) = iProver_top
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4506,c_3773])).

cnf(c_1,plain,
    ( ~ v2_struct_0(X0)
    | v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_560,plain,
    ( ~ v2_struct_0(X0)
    | v1_xboole_0(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_0,c_1])).

cnf(c_1938,plain,
    ( ~ v2_struct_0(X0)
    | v1_xboole_0(u1_struct_0(X0))
    | k8_tmap_1(sK3,sK4) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_560,c_1270])).

cnf(c_1939,plain,
    ( ~ v2_struct_0(k8_tmap_1(sK3,sK4))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4))) ),
    inference(unflattening,[status(thm)],[c_1938])).

cnf(c_2853,plain,
    ( ~ v2_struct_0(k8_tmap_1(sK3,sK4))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4))) ),
    inference(prop_impl,[status(thm)],[c_1939])).

cnf(c_3753,plain,
    ( ~ v2_struct_0(k8_tmap_1(sK3,sK4))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4))) ),
    inference(subtyping,[status(esa)],[c_2853])).

cnf(c_4502,plain,
    ( v2_struct_0(k8_tmap_1(sK3,sK4)) != iProver_top
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3753])).

cnf(c_4626,plain,
    ( k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4)
    | v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4))) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4619,c_4502])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k7_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1770,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_funct_1(k7_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_45])).

cnf(c_1771,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_funct_1(k7_tmap_1(sK3,X0))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1770])).

cnf(c_1775,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_funct_1(k7_tmap_1(sK3,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1771,c_46,c_44])).

cnf(c_3760,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_funct_1(k7_tmap_1(sK3,X0_56)) ),
    inference(subtyping,[status(esa)],[c_1775])).

cnf(c_4706,plain,
    ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_3760])).

cnf(c_4707,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4706])).

cnf(c_4877,plain,
    ( m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) != iProver_top
    | v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
    | k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4)
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4626,c_49,c_1208,c_4707])).

cnf(c_4878,plain,
    ( k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4)
    | v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) != iProver_top
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4))) = iProver_top ),
    inference(renaming,[status(thm)],[c_4877])).

cnf(c_4918,plain,
    ( k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4)
    | v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4914,c_4878])).

cnf(c_1695,plain,
    ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_45])).

cnf(c_1696,plain,
    ( v1_funct_2(k7_tmap_1(sK3,X0),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1695])).

cnf(c_1700,plain,
    ( v1_funct_2(k7_tmap_1(sK3,X0),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1696,c_46,c_44])).

cnf(c_3764,plain,
    ( v1_funct_2(k7_tmap_1(sK3,X0_56),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0_56)))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subtyping,[status(esa)],[c_1700])).

cnf(c_4491,plain,
    ( v1_funct_2(k7_tmap_1(sK3,X0_56),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0_56))) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3764])).

cnf(c_5079,plain,
    ( v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) = iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3773,c_4491])).

cnf(c_5080,plain,
    ( v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5079,c_4914])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1788,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_45])).

cnf(c_1789,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1788])).

cnf(c_1793,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1789,c_46,c_44])).

cnf(c_3759,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k7_tmap_1(sK3,X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0_56))))) ),
    inference(subtyping,[status(esa)],[c_1793])).

cnf(c_4496,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK3,X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0_56))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3759])).

cnf(c_5085,plain,
    ( m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) = iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3773,c_4496])).

cnf(c_5086,plain,
    ( m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) = iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5085,c_4914])).

cnf(c_5346,plain,
    ( ~ m1_subset_1(sK2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4)))))) ),
    inference(instantiation,[status(thm)],[c_3759])).

cnf(c_5606,plain,
    ( k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,sK2(sK3,sK4)) != k9_tmap_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4504,c_47,c_44,c_49,c_155,c_159,c_1208,c_1279,c_3765,c_3751,c_4918,c_5080,c_5086,c_5346])).

cnf(c_14,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK2(X1,X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1292,plain,
    ( v1_tsep_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK2(X1,X0) = u1_struct_0(X0)
    | sK4 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_278])).

cnf(c_1293,plain,
    ( v1_tsep_1(sK4,sK3)
    | ~ l1_pre_topc(sK3)
    | sK2(sK3,sK4) = u1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1292])).

cnf(c_1295,plain,
    ( v1_tsep_1(sK4,sK3)
    | sK2(sK3,sK4) = u1_struct_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1293,c_44])).

cnf(c_3768,plain,
    ( v1_tsep_1(sK4,sK3)
    | sK2(sK3,sK4) = u1_struct_0(sK4) ),
    inference(subtyping,[status(esa)],[c_1295])).

cnf(c_4487,plain,
    ( sK2(sK3,sK4) = u1_struct_0(sK4)
    | v1_tsep_1(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3768])).

cnf(c_5134,plain,
    ( sK2(sK3,sK4) = u1_struct_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4487,c_47,c_49,c_155,c_159,c_1208,c_3768,c_3765,c_4918,c_5080,c_5086])).

cnf(c_5608,plain,
    ( k8_tmap_1(sK3,sK4) != k8_tmap_1(sK3,sK4)
    | k7_tmap_1(sK3,u1_struct_0(sK4)) != k9_tmap_1(sK3,sK4) ),
    inference(light_normalisation,[status(thm)],[c_5606,c_3773,c_5134])).

cnf(c_5609,plain,
    ( k7_tmap_1(sK3,u1_struct_0(sK4)) != k9_tmap_1(sK3,sK4) ),
    inference(equality_resolution_simp,[status(thm)],[c_5608])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5609,c_5086,c_5080,c_4918,c_1208,c_159,c_155,c_49,c_47])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:34:40 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.73/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/0.98  
% 2.73/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.73/0.98  
% 2.73/0.98  ------  iProver source info
% 2.73/0.98  
% 2.73/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.73/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.73/0.98  git: non_committed_changes: false
% 2.73/0.98  git: last_make_outside_of_git: false
% 2.73/0.98  
% 2.73/0.98  ------ 
% 2.73/0.98  
% 2.73/0.98  ------ Input Options
% 2.73/0.98  
% 2.73/0.98  --out_options                           all
% 2.73/0.98  --tptp_safe_out                         true
% 2.73/0.98  --problem_path                          ""
% 2.73/0.98  --include_path                          ""
% 2.73/0.98  --clausifier                            res/vclausify_rel
% 2.73/0.98  --clausifier_options                    --mode clausify
% 2.73/0.98  --stdin                                 false
% 2.73/0.98  --stats_out                             all
% 2.73/0.98  
% 2.73/0.98  ------ General Options
% 2.73/0.98  
% 2.73/0.98  --fof                                   false
% 2.73/0.98  --time_out_real                         305.
% 2.73/0.98  --time_out_virtual                      -1.
% 2.73/0.98  --symbol_type_check                     false
% 2.73/0.98  --clausify_out                          false
% 2.73/0.98  --sig_cnt_out                           false
% 2.73/0.98  --trig_cnt_out                          false
% 2.73/0.98  --trig_cnt_out_tolerance                1.
% 2.73/0.98  --trig_cnt_out_sk_spl                   false
% 2.73/0.98  --abstr_cl_out                          false
% 2.73/0.98  
% 2.73/0.98  ------ Global Options
% 2.73/0.98  
% 2.73/0.98  --schedule                              default
% 2.73/0.98  --add_important_lit                     false
% 2.73/0.98  --prop_solver_per_cl                    1000
% 2.73/0.98  --min_unsat_core                        false
% 2.73/0.98  --soft_assumptions                      false
% 2.73/0.98  --soft_lemma_size                       3
% 2.73/0.98  --prop_impl_unit_size                   0
% 2.73/0.98  --prop_impl_unit                        []
% 2.73/0.98  --share_sel_clauses                     true
% 2.73/0.98  --reset_solvers                         false
% 2.73/0.98  --bc_imp_inh                            [conj_cone]
% 2.73/0.98  --conj_cone_tolerance                   3.
% 2.73/0.98  --extra_neg_conj                        none
% 2.73/0.98  --large_theory_mode                     true
% 2.73/0.98  --prolific_symb_bound                   200
% 2.73/0.98  --lt_threshold                          2000
% 2.73/0.98  --clause_weak_htbl                      true
% 2.73/0.98  --gc_record_bc_elim                     false
% 2.73/0.98  
% 2.73/0.98  ------ Preprocessing Options
% 2.73/0.98  
% 2.73/0.98  --preprocessing_flag                    true
% 2.73/0.98  --time_out_prep_mult                    0.1
% 2.73/0.98  --splitting_mode                        input
% 2.73/0.98  --splitting_grd                         true
% 2.73/0.98  --splitting_cvd                         false
% 2.73/0.98  --splitting_cvd_svl                     false
% 2.73/0.98  --splitting_nvd                         32
% 2.73/0.98  --sub_typing                            true
% 2.73/0.98  --prep_gs_sim                           true
% 2.73/0.98  --prep_unflatten                        true
% 2.73/0.98  --prep_res_sim                          true
% 2.73/0.98  --prep_upred                            true
% 2.73/0.98  --prep_sem_filter                       exhaustive
% 2.73/0.98  --prep_sem_filter_out                   false
% 2.73/0.98  --pred_elim                             true
% 2.73/0.98  --res_sim_input                         true
% 2.73/0.98  --eq_ax_congr_red                       true
% 2.73/0.98  --pure_diseq_elim                       true
% 2.73/0.98  --brand_transform                       false
% 2.73/0.98  --non_eq_to_eq                          false
% 2.73/0.98  --prep_def_merge                        true
% 2.73/0.98  --prep_def_merge_prop_impl              false
% 2.73/0.98  --prep_def_merge_mbd                    true
% 2.73/0.98  --prep_def_merge_tr_red                 false
% 2.73/0.98  --prep_def_merge_tr_cl                  false
% 2.73/0.98  --smt_preprocessing                     true
% 2.73/0.98  --smt_ac_axioms                         fast
% 2.73/0.98  --preprocessed_out                      false
% 2.73/0.98  --preprocessed_stats                    false
% 2.73/0.98  
% 2.73/0.98  ------ Abstraction refinement Options
% 2.73/0.98  
% 2.73/0.98  --abstr_ref                             []
% 2.73/0.98  --abstr_ref_prep                        false
% 2.73/0.98  --abstr_ref_until_sat                   false
% 2.73/0.98  --abstr_ref_sig_restrict                funpre
% 2.73/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.73/0.98  --abstr_ref_under                       []
% 2.73/0.98  
% 2.73/0.98  ------ SAT Options
% 2.73/0.98  
% 2.73/0.98  --sat_mode                              false
% 2.73/0.98  --sat_fm_restart_options                ""
% 2.73/0.98  --sat_gr_def                            false
% 2.73/0.98  --sat_epr_types                         true
% 2.73/0.98  --sat_non_cyclic_types                  false
% 2.73/0.98  --sat_finite_models                     false
% 2.73/0.98  --sat_fm_lemmas                         false
% 2.73/0.98  --sat_fm_prep                           false
% 2.73/0.98  --sat_fm_uc_incr                        true
% 2.73/0.98  --sat_out_model                         small
% 2.73/0.98  --sat_out_clauses                       false
% 2.73/0.98  
% 2.73/0.98  ------ QBF Options
% 2.73/0.98  
% 2.73/0.98  --qbf_mode                              false
% 2.73/0.98  --qbf_elim_univ                         false
% 2.73/0.98  --qbf_dom_inst                          none
% 2.73/0.98  --qbf_dom_pre_inst                      false
% 2.73/0.98  --qbf_sk_in                             false
% 2.73/0.98  --qbf_pred_elim                         true
% 2.73/0.98  --qbf_split                             512
% 2.73/0.98  
% 2.73/0.98  ------ BMC1 Options
% 2.73/0.98  
% 2.73/0.98  --bmc1_incremental                      false
% 2.73/0.98  --bmc1_axioms                           reachable_all
% 2.73/0.98  --bmc1_min_bound                        0
% 2.73/0.98  --bmc1_max_bound                        -1
% 2.73/0.98  --bmc1_max_bound_default                -1
% 2.73/0.98  --bmc1_symbol_reachability              true
% 2.73/0.98  --bmc1_property_lemmas                  false
% 2.73/0.98  --bmc1_k_induction                      false
% 2.73/0.98  --bmc1_non_equiv_states                 false
% 2.73/0.98  --bmc1_deadlock                         false
% 2.73/0.98  --bmc1_ucm                              false
% 2.73/0.98  --bmc1_add_unsat_core                   none
% 2.73/0.98  --bmc1_unsat_core_children              false
% 2.73/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.73/0.98  --bmc1_out_stat                         full
% 2.73/0.98  --bmc1_ground_init                      false
% 2.73/0.98  --bmc1_pre_inst_next_state              false
% 2.73/0.98  --bmc1_pre_inst_state                   false
% 2.73/0.98  --bmc1_pre_inst_reach_state             false
% 2.73/0.98  --bmc1_out_unsat_core                   false
% 2.73/0.98  --bmc1_aig_witness_out                  false
% 2.73/0.98  --bmc1_verbose                          false
% 2.73/0.98  --bmc1_dump_clauses_tptp                false
% 2.73/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.73/0.98  --bmc1_dump_file                        -
% 2.73/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.73/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.73/0.98  --bmc1_ucm_extend_mode                  1
% 2.73/0.98  --bmc1_ucm_init_mode                    2
% 2.73/0.98  --bmc1_ucm_cone_mode                    none
% 2.73/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.73/0.98  --bmc1_ucm_relax_model                  4
% 2.73/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.73/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.73/0.98  --bmc1_ucm_layered_model                none
% 2.73/0.98  --bmc1_ucm_max_lemma_size               10
% 2.73/0.98  
% 2.73/0.98  ------ AIG Options
% 2.73/0.98  
% 2.73/0.98  --aig_mode                              false
% 2.73/0.98  
% 2.73/0.98  ------ Instantiation Options
% 2.73/0.98  
% 2.73/0.98  --instantiation_flag                    true
% 2.73/0.98  --inst_sos_flag                         false
% 2.73/0.98  --inst_sos_phase                        true
% 2.73/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.73/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.73/0.98  --inst_lit_sel_side                     num_symb
% 2.73/0.98  --inst_solver_per_active                1400
% 2.73/0.98  --inst_solver_calls_frac                1.
% 2.73/0.98  --inst_passive_queue_type               priority_queues
% 2.73/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.73/0.98  --inst_passive_queues_freq              [25;2]
% 2.73/0.98  --inst_dismatching                      true
% 2.73/0.98  --inst_eager_unprocessed_to_passive     true
% 2.73/0.98  --inst_prop_sim_given                   true
% 2.73/0.98  --inst_prop_sim_new                     false
% 2.73/0.98  --inst_subs_new                         false
% 2.73/0.98  --inst_eq_res_simp                      false
% 2.73/0.98  --inst_subs_given                       false
% 2.73/0.98  --inst_orphan_elimination               true
% 2.73/0.98  --inst_learning_loop_flag               true
% 2.73/0.98  --inst_learning_start                   3000
% 2.73/0.98  --inst_learning_factor                  2
% 2.73/0.98  --inst_start_prop_sim_after_learn       3
% 2.73/0.98  --inst_sel_renew                        solver
% 2.73/0.98  --inst_lit_activity_flag                true
% 2.73/0.98  --inst_restr_to_given                   false
% 2.73/0.98  --inst_activity_threshold               500
% 2.73/0.98  --inst_out_proof                        true
% 2.73/0.98  
% 2.73/0.98  ------ Resolution Options
% 2.73/0.98  
% 2.73/0.98  --resolution_flag                       true
% 2.73/0.98  --res_lit_sel                           adaptive
% 2.73/0.98  --res_lit_sel_side                      none
% 2.73/0.98  --res_ordering                          kbo
% 2.73/0.98  --res_to_prop_solver                    active
% 2.73/0.98  --res_prop_simpl_new                    false
% 2.73/0.98  --res_prop_simpl_given                  true
% 2.73/0.98  --res_passive_queue_type                priority_queues
% 2.73/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.73/0.98  --res_passive_queues_freq               [15;5]
% 2.73/0.98  --res_forward_subs                      full
% 2.73/0.98  --res_backward_subs                     full
% 2.73/0.98  --res_forward_subs_resolution           true
% 2.73/0.98  --res_backward_subs_resolution          true
% 2.73/0.98  --res_orphan_elimination                true
% 2.73/0.98  --res_time_limit                        2.
% 2.73/0.98  --res_out_proof                         true
% 2.73/0.98  
% 2.73/0.98  ------ Superposition Options
% 2.73/0.98  
% 2.73/0.98  --superposition_flag                    true
% 2.73/0.98  --sup_passive_queue_type                priority_queues
% 2.73/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.73/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.73/0.98  --demod_completeness_check              fast
% 2.73/0.98  --demod_use_ground                      true
% 2.73/0.98  --sup_to_prop_solver                    passive
% 2.73/0.98  --sup_prop_simpl_new                    true
% 2.73/0.98  --sup_prop_simpl_given                  true
% 2.73/0.98  --sup_fun_splitting                     false
% 2.73/0.98  --sup_smt_interval                      50000
% 2.73/0.98  
% 2.73/0.98  ------ Superposition Simplification Setup
% 2.73/0.98  
% 2.73/0.98  --sup_indices_passive                   []
% 2.73/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.73/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/0.98  --sup_full_bw                           [BwDemod]
% 2.73/0.98  --sup_immed_triv                        [TrivRules]
% 2.73/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.73/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/0.98  --sup_immed_bw_main                     []
% 2.73/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.73/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/0.98  
% 2.73/0.98  ------ Combination Options
% 2.73/0.98  
% 2.73/0.98  --comb_res_mult                         3
% 2.73/0.98  --comb_sup_mult                         2
% 2.73/0.98  --comb_inst_mult                        10
% 2.73/0.98  
% 2.73/0.98  ------ Debug Options
% 2.73/0.98  
% 2.73/0.98  --dbg_backtrace                         false
% 2.73/0.98  --dbg_dump_prop_clauses                 false
% 2.73/0.98  --dbg_dump_prop_clauses_file            -
% 2.73/0.98  --dbg_out_stat                          false
% 2.73/0.98  ------ Parsing...
% 2.73/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.73/0.98  
% 2.73/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 2.73/0.98  
% 2.73/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.73/0.98  
% 2.73/0.98  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.73/0.98  ------ Proving...
% 2.73/0.98  ------ Problem Properties 
% 2.73/0.98  
% 2.73/0.98  
% 2.73/0.98  clauses                                 27
% 2.73/0.98  conjectures                             1
% 2.73/0.98  EPR                                     1
% 2.73/0.98  Horn                                    16
% 2.73/0.98  unary                                   7
% 2.73/0.98  binary                                  10
% 2.73/0.98  lits                                    71
% 2.73/0.98  lits eq                                 15
% 2.73/0.98  fd_pure                                 0
% 2.73/0.98  fd_pseudo                               0
% 2.73/0.98  fd_cond                                 3
% 2.73/0.98  fd_pseudo_cond                          0
% 2.73/0.98  AC symbols                              0
% 2.73/0.98  
% 2.73/0.98  ------ Schedule dynamic 5 is on 
% 2.73/0.98  
% 2.73/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.73/0.98  
% 2.73/0.98  
% 2.73/0.98  ------ 
% 2.73/0.98  Current options:
% 2.73/0.98  ------ 
% 2.73/0.98  
% 2.73/0.98  ------ Input Options
% 2.73/0.98  
% 2.73/0.98  --out_options                           all
% 2.73/0.98  --tptp_safe_out                         true
% 2.73/0.98  --problem_path                          ""
% 2.73/0.98  --include_path                          ""
% 2.73/0.98  --clausifier                            res/vclausify_rel
% 2.73/0.98  --clausifier_options                    --mode clausify
% 2.73/0.98  --stdin                                 false
% 2.73/0.98  --stats_out                             all
% 2.73/0.98  
% 2.73/0.98  ------ General Options
% 2.73/0.98  
% 2.73/0.98  --fof                                   false
% 2.73/0.98  --time_out_real                         305.
% 2.73/0.98  --time_out_virtual                      -1.
% 2.73/0.98  --symbol_type_check                     false
% 2.73/0.98  --clausify_out                          false
% 2.73/0.98  --sig_cnt_out                           false
% 2.73/0.98  --trig_cnt_out                          false
% 2.73/0.98  --trig_cnt_out_tolerance                1.
% 2.73/0.98  --trig_cnt_out_sk_spl                   false
% 2.73/0.98  --abstr_cl_out                          false
% 2.73/0.98  
% 2.73/0.98  ------ Global Options
% 2.73/0.98  
% 2.73/0.98  --schedule                              default
% 2.73/0.98  --add_important_lit                     false
% 2.73/0.98  --prop_solver_per_cl                    1000
% 2.73/0.98  --min_unsat_core                        false
% 2.73/0.98  --soft_assumptions                      false
% 2.73/0.98  --soft_lemma_size                       3
% 2.73/0.98  --prop_impl_unit_size                   0
% 2.73/0.98  --prop_impl_unit                        []
% 2.73/0.98  --share_sel_clauses                     true
% 2.73/0.98  --reset_solvers                         false
% 2.73/0.98  --bc_imp_inh                            [conj_cone]
% 2.73/0.98  --conj_cone_tolerance                   3.
% 2.73/0.98  --extra_neg_conj                        none
% 2.73/0.98  --large_theory_mode                     true
% 2.73/0.98  --prolific_symb_bound                   200
% 2.73/0.98  --lt_threshold                          2000
% 2.73/0.98  --clause_weak_htbl                      true
% 2.73/0.98  --gc_record_bc_elim                     false
% 2.73/0.98  
% 2.73/0.98  ------ Preprocessing Options
% 2.73/0.98  
% 2.73/0.98  --preprocessing_flag                    true
% 2.73/0.98  --time_out_prep_mult                    0.1
% 2.73/0.98  --splitting_mode                        input
% 2.73/0.98  --splitting_grd                         true
% 2.73/0.98  --splitting_cvd                         false
% 2.73/0.98  --splitting_cvd_svl                     false
% 2.73/0.98  --splitting_nvd                         32
% 2.73/0.98  --sub_typing                            true
% 2.73/0.98  --prep_gs_sim                           true
% 2.73/0.98  --prep_unflatten                        true
% 2.73/0.98  --prep_res_sim                          true
% 2.73/0.98  --prep_upred                            true
% 2.73/0.98  --prep_sem_filter                       exhaustive
% 2.73/0.98  --prep_sem_filter_out                   false
% 2.73/0.98  --pred_elim                             true
% 2.73/0.98  --res_sim_input                         true
% 2.73/0.98  --eq_ax_congr_red                       true
% 2.73/0.98  --pure_diseq_elim                       true
% 2.73/0.98  --brand_transform                       false
% 2.73/0.98  --non_eq_to_eq                          false
% 2.73/0.98  --prep_def_merge                        true
% 2.73/0.98  --prep_def_merge_prop_impl              false
% 2.73/0.98  --prep_def_merge_mbd                    true
% 2.73/0.98  --prep_def_merge_tr_red                 false
% 2.73/0.98  --prep_def_merge_tr_cl                  false
% 2.73/0.98  --smt_preprocessing                     true
% 2.73/0.98  --smt_ac_axioms                         fast
% 2.73/0.98  --preprocessed_out                      false
% 2.73/0.98  --preprocessed_stats                    false
% 2.73/0.98  
% 2.73/0.98  ------ Abstraction refinement Options
% 2.73/0.98  
% 2.73/0.98  --abstr_ref                             []
% 2.73/0.98  --abstr_ref_prep                        false
% 2.73/0.98  --abstr_ref_until_sat                   false
% 2.73/0.98  --abstr_ref_sig_restrict                funpre
% 2.73/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.73/0.98  --abstr_ref_under                       []
% 2.73/0.98  
% 2.73/0.98  ------ SAT Options
% 2.73/0.98  
% 2.73/0.98  --sat_mode                              false
% 2.73/0.98  --sat_fm_restart_options                ""
% 2.73/0.98  --sat_gr_def                            false
% 2.73/0.98  --sat_epr_types                         true
% 2.73/0.98  --sat_non_cyclic_types                  false
% 2.73/0.98  --sat_finite_models                     false
% 2.73/0.98  --sat_fm_lemmas                         false
% 2.73/0.98  --sat_fm_prep                           false
% 2.73/0.98  --sat_fm_uc_incr                        true
% 2.73/0.98  --sat_out_model                         small
% 2.73/0.98  --sat_out_clauses                       false
% 2.73/0.98  
% 2.73/0.98  ------ QBF Options
% 2.73/0.98  
% 2.73/0.98  --qbf_mode                              false
% 2.73/0.98  --qbf_elim_univ                         false
% 2.73/0.98  --qbf_dom_inst                          none
% 2.73/0.98  --qbf_dom_pre_inst                      false
% 2.73/0.98  --qbf_sk_in                             false
% 2.73/0.98  --qbf_pred_elim                         true
% 2.73/0.98  --qbf_split                             512
% 2.73/0.98  
% 2.73/0.98  ------ BMC1 Options
% 2.73/0.98  
% 2.73/0.98  --bmc1_incremental                      false
% 2.73/0.98  --bmc1_axioms                           reachable_all
% 2.73/0.98  --bmc1_min_bound                        0
% 2.73/0.98  --bmc1_max_bound                        -1
% 2.73/0.98  --bmc1_max_bound_default                -1
% 2.73/0.98  --bmc1_symbol_reachability              true
% 2.73/0.98  --bmc1_property_lemmas                  false
% 2.73/0.98  --bmc1_k_induction                      false
% 2.73/0.98  --bmc1_non_equiv_states                 false
% 2.73/0.98  --bmc1_deadlock                         false
% 2.73/0.98  --bmc1_ucm                              false
% 2.73/0.98  --bmc1_add_unsat_core                   none
% 2.73/0.98  --bmc1_unsat_core_children              false
% 2.73/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.73/0.98  --bmc1_out_stat                         full
% 2.73/0.98  --bmc1_ground_init                      false
% 2.73/0.98  --bmc1_pre_inst_next_state              false
% 2.73/0.98  --bmc1_pre_inst_state                   false
% 2.73/0.98  --bmc1_pre_inst_reach_state             false
% 2.73/0.98  --bmc1_out_unsat_core                   false
% 2.73/0.98  --bmc1_aig_witness_out                  false
% 2.73/0.98  --bmc1_verbose                          false
% 2.73/0.98  --bmc1_dump_clauses_tptp                false
% 2.73/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.73/0.98  --bmc1_dump_file                        -
% 2.73/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.73/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.73/0.98  --bmc1_ucm_extend_mode                  1
% 2.73/0.98  --bmc1_ucm_init_mode                    2
% 2.73/0.98  --bmc1_ucm_cone_mode                    none
% 2.73/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.73/0.98  --bmc1_ucm_relax_model                  4
% 2.73/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.73/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.73/0.98  --bmc1_ucm_layered_model                none
% 2.73/0.98  --bmc1_ucm_max_lemma_size               10
% 2.73/0.98  
% 2.73/0.98  ------ AIG Options
% 2.73/0.98  
% 2.73/0.98  --aig_mode                              false
% 2.73/0.98  
% 2.73/0.98  ------ Instantiation Options
% 2.73/0.98  
% 2.73/0.98  --instantiation_flag                    true
% 2.73/0.98  --inst_sos_flag                         false
% 2.73/0.98  --inst_sos_phase                        true
% 2.73/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.73/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.73/0.98  --inst_lit_sel_side                     none
% 2.73/0.98  --inst_solver_per_active                1400
% 2.73/0.98  --inst_solver_calls_frac                1.
% 2.73/0.98  --inst_passive_queue_type               priority_queues
% 2.73/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.73/0.98  --inst_passive_queues_freq              [25;2]
% 2.73/0.98  --inst_dismatching                      true
% 2.73/0.98  --inst_eager_unprocessed_to_passive     true
% 2.73/0.98  --inst_prop_sim_given                   true
% 2.73/0.98  --inst_prop_sim_new                     false
% 2.73/0.98  --inst_subs_new                         false
% 2.73/0.98  --inst_eq_res_simp                      false
% 2.73/0.98  --inst_subs_given                       false
% 2.73/0.98  --inst_orphan_elimination               true
% 2.73/0.98  --inst_learning_loop_flag               true
% 2.73/0.98  --inst_learning_start                   3000
% 2.73/0.98  --inst_learning_factor                  2
% 2.73/0.98  --inst_start_prop_sim_after_learn       3
% 2.73/0.98  --inst_sel_renew                        solver
% 2.73/0.98  --inst_lit_activity_flag                true
% 2.73/0.98  --inst_restr_to_given                   false
% 2.73/0.98  --inst_activity_threshold               500
% 2.73/0.98  --inst_out_proof                        true
% 2.73/0.98  
% 2.73/0.98  ------ Resolution Options
% 2.73/0.98  
% 2.73/0.98  --resolution_flag                       false
% 2.73/0.98  --res_lit_sel                           adaptive
% 2.73/0.98  --res_lit_sel_side                      none
% 2.73/0.98  --res_ordering                          kbo
% 2.73/0.98  --res_to_prop_solver                    active
% 2.73/0.98  --res_prop_simpl_new                    false
% 2.73/0.98  --res_prop_simpl_given                  true
% 2.73/0.98  --res_passive_queue_type                priority_queues
% 2.73/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.73/0.98  --res_passive_queues_freq               [15;5]
% 2.73/0.98  --res_forward_subs                      full
% 2.73/0.98  --res_backward_subs                     full
% 2.73/0.98  --res_forward_subs_resolution           true
% 2.73/0.98  --res_backward_subs_resolution          true
% 2.73/0.98  --res_orphan_elimination                true
% 2.73/0.98  --res_time_limit                        2.
% 2.73/0.98  --res_out_proof                         true
% 2.73/0.98  
% 2.73/0.98  ------ Superposition Options
% 2.73/0.98  
% 2.73/0.98  --superposition_flag                    true
% 2.73/0.98  --sup_passive_queue_type                priority_queues
% 2.73/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.73/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.73/0.98  --demod_completeness_check              fast
% 2.73/0.98  --demod_use_ground                      true
% 2.73/0.98  --sup_to_prop_solver                    passive
% 2.73/0.98  --sup_prop_simpl_new                    true
% 2.73/0.98  --sup_prop_simpl_given                  true
% 2.73/0.98  --sup_fun_splitting                     false
% 2.73/0.98  --sup_smt_interval                      50000
% 2.73/0.98  
% 2.73/0.98  ------ Superposition Simplification Setup
% 2.73/0.98  
% 2.73/0.98  --sup_indices_passive                   []
% 2.73/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.73/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/0.98  --sup_full_bw                           [BwDemod]
% 2.73/0.98  --sup_immed_triv                        [TrivRules]
% 2.73/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.73/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/0.98  --sup_immed_bw_main                     []
% 2.73/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.73/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/0.98  
% 2.73/0.98  ------ Combination Options
% 2.73/0.98  
% 2.73/0.98  --comb_res_mult                         3
% 2.73/0.98  --comb_sup_mult                         2
% 2.73/0.98  --comb_inst_mult                        10
% 2.73/0.98  
% 2.73/0.98  ------ Debug Options
% 2.73/0.98  
% 2.73/0.98  --dbg_backtrace                         false
% 2.73/0.98  --dbg_dump_prop_clauses                 false
% 2.73/0.98  --dbg_dump_prop_clauses_file            -
% 2.73/0.98  --dbg_out_stat                          false
% 2.73/0.98  
% 2.73/0.98  
% 2.73/0.98  
% 2.73/0.98  
% 2.73/0.98  ------ Proving...
% 2.73/0.98  
% 2.73/0.98  
% 2.73/0.98  % SZS status Theorem for theBenchmark.p
% 2.73/0.98  
% 2.73/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.73/0.98  
% 2.73/0.98  fof(f10,axiom,(
% 2.73/0.98    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))))),
% 2.73/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/0.98  
% 2.73/0.98  fof(f33,plain,(
% 2.73/0.98    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.73/0.98    inference(ennf_transformation,[],[f10])).
% 2.73/0.98  
% 2.73/0.98  fof(f34,plain,(
% 2.73/0.98    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.73/0.98    inference(flattening,[],[f33])).
% 2.73/0.98  
% 2.73/0.98  fof(f85,plain,(
% 2.73/0.98    ( ! [X0,X1] : (v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/0.98    inference(cnf_transformation,[],[f34])).
% 2.73/0.98  
% 2.73/0.98  fof(f14,conjecture,(
% 2.73/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))))))),
% 2.73/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/0.98  
% 2.73/0.98  fof(f15,negated_conjecture,(
% 2.73/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))))))),
% 2.73/0.98    inference(negated_conjecture,[],[f14])).
% 2.73/0.98  
% 2.73/0.98  fof(f40,plain,(
% 2.73/0.98    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1)))) & m1_pre_topc(X1,X0)) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.73/0.98    inference(ennf_transformation,[],[f15])).
% 2.73/0.98  
% 2.73/0.98  fof(f41,plain,(
% 2.73/0.98    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.73/0.98    inference(flattening,[],[f40])).
% 2.73/0.98  
% 2.73/0.98  fof(f57,plain,(
% 2.73/0.98    ? [X0] : (? [X1] : ((((~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) & ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.73/0.98    inference(nnf_transformation,[],[f41])).
% 2.73/0.98  
% 2.73/0.98  fof(f58,plain,(
% 2.73/0.98    ? [X0] : (? [X1] : ((~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.73/0.98    inference(flattening,[],[f57])).
% 2.73/0.98  
% 2.73/0.98  fof(f60,plain,(
% 2.73/0.98    ( ! [X0] : (? [X1] : ((~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0)) => ((~m1_subset_1(k9_tmap_1(X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,sK4))))) | ~v5_pre_topc(k9_tmap_1(X0,sK4),X0,k8_tmap_1(X0,sK4)) | ~v1_funct_2(k9_tmap_1(X0,sK4),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,sK4))) | ~v1_funct_1(k9_tmap_1(X0,sK4)) | ~m1_pre_topc(sK4,X0) | ~v1_tsep_1(sK4,X0)) & ((m1_subset_1(k9_tmap_1(X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,sK4))))) & v5_pre_topc(k9_tmap_1(X0,sK4),X0,k8_tmap_1(X0,sK4)) & v1_funct_2(k9_tmap_1(X0,sK4),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,sK4))) & v1_funct_1(k9_tmap_1(X0,sK4))) | (m1_pre_topc(sK4,X0) & v1_tsep_1(sK4,X0))) & m1_pre_topc(sK4,X0))) )),
% 2.73/0.98    introduced(choice_axiom,[])).
% 2.73/0.98  
% 2.73/0.98  fof(f59,plain,(
% 2.73/0.98    ? [X0] : (? [X1] : ((~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~m1_subset_1(k9_tmap_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X1))))) | ~v5_pre_topc(k9_tmap_1(sK3,X1),sK3,k8_tmap_1(sK3,X1)) | ~v1_funct_2(k9_tmap_1(sK3,X1),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X1))) | ~v1_funct_1(k9_tmap_1(sK3,X1)) | ~m1_pre_topc(X1,sK3) | ~v1_tsep_1(X1,sK3)) & ((m1_subset_1(k9_tmap_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X1))))) & v5_pre_topc(k9_tmap_1(sK3,X1),sK3,k8_tmap_1(sK3,X1)) & v1_funct_2(k9_tmap_1(sK3,X1),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X1))) & v1_funct_1(k9_tmap_1(sK3,X1))) | (m1_pre_topc(X1,sK3) & v1_tsep_1(X1,sK3))) & m1_pre_topc(X1,sK3)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 2.73/0.98    introduced(choice_axiom,[])).
% 2.73/0.98  
% 2.73/0.98  fof(f61,plain,(
% 2.73/0.98    ((~m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) | ~v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4)) | ~v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) | ~v1_funct_1(k9_tmap_1(sK3,sK4)) | ~m1_pre_topc(sK4,sK3) | ~v1_tsep_1(sK4,sK3)) & ((m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) & v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4)) & v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) & v1_funct_1(k9_tmap_1(sK3,sK4))) | (m1_pre_topc(sK4,sK3) & v1_tsep_1(sK4,sK3))) & m1_pre_topc(sK4,sK3)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 2.73/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f58,f60,f59])).
% 2.73/0.98  
% 2.73/0.98  fof(f107,plain,(
% 2.73/0.98    m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) | m1_pre_topc(sK4,sK3)),
% 2.73/0.98    inference(cnf_transformation,[],[f61])).
% 2.73/0.98  
% 2.73/0.98  fof(f99,plain,(
% 2.73/0.98    m1_pre_topc(sK4,sK3)),
% 2.73/0.98    inference(cnf_transformation,[],[f61])).
% 2.73/0.98  
% 2.73/0.98  fof(f96,plain,(
% 2.73/0.98    ~v2_struct_0(sK3)),
% 2.73/0.98    inference(cnf_transformation,[],[f61])).
% 2.73/0.98  
% 2.73/0.98  fof(f97,plain,(
% 2.73/0.98    v2_pre_topc(sK3)),
% 2.73/0.98    inference(cnf_transformation,[],[f61])).
% 2.73/0.98  
% 2.73/0.98  fof(f98,plain,(
% 2.73/0.98    l1_pre_topc(sK3)),
% 2.73/0.98    inference(cnf_transformation,[],[f61])).
% 2.73/0.98  
% 2.73/0.98  fof(f12,axiom,(
% 2.73/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))))),
% 2.73/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/0.98  
% 2.73/0.98  fof(f37,plain,(
% 2.73/0.98    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.73/0.98    inference(ennf_transformation,[],[f12])).
% 2.73/0.98  
% 2.73/0.98  fof(f38,plain,(
% 2.73/0.98    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.73/0.98    inference(flattening,[],[f37])).
% 2.73/0.98  
% 2.73/0.98  fof(f55,plain,(
% 2.73/0.98    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | (~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1)))) & ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.73/0.98    inference(nnf_transformation,[],[f38])).
% 2.73/0.98  
% 2.73/0.98  fof(f56,plain,(
% 2.73/0.98    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1))) & ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.73/0.98    inference(flattening,[],[f55])).
% 2.73/0.98  
% 2.73/0.98  fof(f94,plain,(
% 2.73/0.98    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/0.98    inference(cnf_transformation,[],[f56])).
% 2.73/0.98  
% 2.73/0.98  fof(f8,axiom,(
% 2.73/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 2.73/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/0.98  
% 2.73/0.98  fof(f29,plain,(
% 2.73/0.98    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.73/0.98    inference(ennf_transformation,[],[f8])).
% 2.73/0.98  
% 2.73/0.98  fof(f30,plain,(
% 2.73/0.98    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.73/0.98    inference(flattening,[],[f29])).
% 2.73/0.98  
% 2.73/0.98  fof(f80,plain,(
% 2.73/0.98    ( ! [X0,X1] : (v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/0.98    inference(cnf_transformation,[],[f30])).
% 2.73/0.98  
% 2.73/0.98  fof(f104,plain,(
% 2.73/0.98    v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4)) | v1_tsep_1(sK4,sK3)),
% 2.73/0.98    inference(cnf_transformation,[],[f61])).
% 2.73/0.98  
% 2.73/0.98  fof(f7,axiom,(
% 2.73/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tsep_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v3_pre_topc(X2,X0))))))),
% 2.73/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/0.98  
% 2.73/0.98  fof(f27,plain,(
% 2.73/0.98    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.73/0.98    inference(ennf_transformation,[],[f7])).
% 2.73/0.98  
% 2.73/0.98  fof(f28,plain,(
% 2.73/0.98    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.73/0.98    inference(flattening,[],[f27])).
% 2.73/0.98  
% 2.73/0.98  fof(f51,plain,(
% 2.73/0.98    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.73/0.98    inference(nnf_transformation,[],[f28])).
% 2.73/0.98  
% 2.73/0.98  fof(f52,plain,(
% 2.73/0.98    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.73/0.98    inference(rectify,[],[f51])).
% 2.73/0.98  
% 2.73/0.98  fof(f53,plain,(
% 2.73/0.98    ! [X1,X0] : (? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK2(X0,X1),X0) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.73/0.98    introduced(choice_axiom,[])).
% 2.73/0.98  
% 2.73/0.98  fof(f54,plain,(
% 2.73/0.98    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | (~v3_pre_topc(sK2(X0,X1),X0) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.73/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f52,f53])).
% 2.73/0.98  
% 2.73/0.98  fof(f78,plain,(
% 2.73/0.98    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(sK2(X0,X1),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.73/0.98    inference(cnf_transformation,[],[f54])).
% 2.73/0.98  
% 2.73/0.98  fof(f76,plain,(
% 2.73/0.98    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.73/0.98    inference(cnf_transformation,[],[f54])).
% 2.73/0.98  
% 2.73/0.98  fof(f3,axiom,(
% 2.73/0.98    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.73/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/0.98  
% 2.73/0.98  fof(f19,plain,(
% 2.73/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.73/0.98    inference(ennf_transformation,[],[f3])).
% 2.73/0.98  
% 2.73/0.98  fof(f20,plain,(
% 2.73/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.73/0.98    inference(flattening,[],[f19])).
% 2.73/0.98  
% 2.73/0.98  fof(f64,plain,(
% 2.73/0.98    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.73/0.98    inference(cnf_transformation,[],[f20])).
% 2.73/0.98  
% 2.73/0.98  fof(f1,axiom,(
% 2.73/0.98    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.73/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f16,plain,(
% 2.73/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.73/0.99    inference(ennf_transformation,[],[f1])).
% 2.73/0.99  
% 2.73/0.99  fof(f62,plain,(
% 2.73/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f16])).
% 2.73/0.99  
% 2.73/0.99  fof(f13,axiom,(
% 2.73/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.73/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f39,plain,(
% 2.73/0.99    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.73/0.99    inference(ennf_transformation,[],[f13])).
% 2.73/0.99  
% 2.73/0.99  fof(f95,plain,(
% 2.73/0.99    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f39])).
% 2.73/0.99  
% 2.73/0.99  fof(f87,plain,(
% 2.73/0.99    ( ! [X0,X1] : (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f34])).
% 2.73/0.99  
% 2.73/0.99  fof(f86,plain,(
% 2.73/0.99    ( ! [X0,X1] : (v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f34])).
% 2.73/0.99  
% 2.73/0.99  fof(f92,plain,(
% 2.73/0.99    ( ! [X0,X1] : (v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f56])).
% 2.73/0.99  
% 2.73/0.99  fof(f108,plain,(
% 2.73/0.99    ~m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) | ~v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4)) | ~v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) | ~v1_funct_1(k9_tmap_1(sK3,sK4)) | ~m1_pre_topc(sK4,sK3) | ~v1_tsep_1(sK4,sK3)),
% 2.73/0.99    inference(cnf_transformation,[],[f61])).
% 2.73/0.99  
% 2.73/0.99  fof(f75,plain,(
% 2.73/0.99    ( ! [X0,X3,X1] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f54])).
% 2.73/0.99  
% 2.73/0.99  fof(f114,plain,(
% 2.73/0.99    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.73/0.99    inference(equality_resolution,[],[f75])).
% 2.73/0.99  
% 2.73/0.99  fof(f5,axiom,(
% 2.73/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & v1_pre_topc(X2)) => (k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => k6_tmap_1(X0,X3) = X2))))))),
% 2.73/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f23,plain,(
% 2.73/0.99    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : ((k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.73/0.99    inference(ennf_transformation,[],[f5])).
% 2.73/0.99  
% 2.73/0.99  fof(f24,plain,(
% 2.73/0.99    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.73/0.99    inference(flattening,[],[f23])).
% 2.73/0.99  
% 2.73/0.99  fof(f43,plain,(
% 2.73/0.99    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.73/0.99    inference(nnf_transformation,[],[f24])).
% 2.73/0.99  
% 2.73/0.99  fof(f44,plain,(
% 2.73/0.99    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.73/0.99    inference(rectify,[],[f43])).
% 2.73/0.99  
% 2.73/0.99  fof(f45,plain,(
% 2.73/0.99    ! [X2,X1,X0] : (? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (k6_tmap_1(X0,sK0(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK0(X0,X1,X2) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.73/0.99    introduced(choice_axiom,[])).
% 2.73/0.99  
% 2.73/0.99  fof(f46,plain,(
% 2.73/0.99    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | (k6_tmap_1(X0,sK0(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK0(X0,X1,X2) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.73/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f44,f45])).
% 2.73/0.99  
% 2.73/0.99  fof(f67,plain,(
% 2.73/0.99    ( ! [X4,X2,X0,X1] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f46])).
% 2.73/0.99  
% 2.73/0.99  fof(f110,plain,(
% 2.73/0.99    ( ! [X2,X0,X1] : (k6_tmap_1(X0,u1_struct_0(X1)) = X2 | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/0.99    inference(equality_resolution,[],[f67])).
% 2.73/0.99  
% 2.73/0.99  fof(f111,plain,(
% 2.73/0.99    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/0.99    inference(equality_resolution,[],[f110])).
% 2.73/0.99  
% 2.73/0.99  fof(f9,axiom,(
% 2.73/0.99    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 2.73/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f31,plain,(
% 2.73/0.99    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.73/0.99    inference(ennf_transformation,[],[f9])).
% 2.73/0.99  
% 2.73/0.99  fof(f32,plain,(
% 2.73/0.99    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.73/0.99    inference(flattening,[],[f31])).
% 2.73/0.99  
% 2.73/0.99  fof(f82,plain,(
% 2.73/0.99    ( ! [X0,X1] : (v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f32])).
% 2.73/0.99  
% 2.73/0.99  fof(f83,plain,(
% 2.73/0.99    ( ! [X0,X1] : (v2_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f32])).
% 2.73/0.99  
% 2.73/0.99  fof(f84,plain,(
% 2.73/0.99    ( ! [X0,X1] : (l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f32])).
% 2.73/0.99  
% 2.73/0.99  fof(f11,axiom,(
% 2.73/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 2.73/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f35,plain,(
% 2.73/0.99    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.73/0.99    inference(ennf_transformation,[],[f11])).
% 2.73/0.99  
% 2.73/0.99  fof(f36,plain,(
% 2.73/0.99    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.73/0.99    inference(flattening,[],[f35])).
% 2.73/0.99  
% 2.73/0.99  fof(f88,plain,(
% 2.73/0.99    ( ! [X0,X1] : (u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f36])).
% 2.73/0.99  
% 2.73/0.99  fof(f4,axiom,(
% 2.73/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 2.73/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f21,plain,(
% 2.73/0.99    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 2.73/0.99    inference(ennf_transformation,[],[f4])).
% 2.73/0.99  
% 2.73/0.99  fof(f22,plain,(
% 2.73/0.99    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 2.73/0.99    inference(flattening,[],[f21])).
% 2.73/0.99  
% 2.73/0.99  fof(f42,plain,(
% 2.73/0.99    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 2.73/0.99    inference(nnf_transformation,[],[f22])).
% 2.73/0.99  
% 2.73/0.99  fof(f65,plain,(
% 2.73/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f42])).
% 2.73/0.99  
% 2.73/0.99  fof(f6,axiom,(
% 2.73/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(X2)) => (k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))))))))),
% 2.73/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f25,plain,(
% 2.73/0.99    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : ((r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.73/0.99    inference(ennf_transformation,[],[f6])).
% 2.73/0.99  
% 2.73/0.99  fof(f26,plain,(
% 2.73/0.99    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.73/0.99    inference(flattening,[],[f25])).
% 2.73/0.99  
% 2.73/0.99  fof(f47,plain,(
% 2.73/0.99    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | ? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.73/0.99    inference(nnf_transformation,[],[f26])).
% 2.73/0.99  
% 2.73/0.99  fof(f48,plain,(
% 2.73/0.99    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | ? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.73/0.99    inference(rectify,[],[f47])).
% 2.73/0.99  
% 2.73/0.99  fof(f49,plain,(
% 2.73/0.99    ! [X2,X1,X0] : (? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2))) & u1_struct_0(X1) = sK1(X0,X1,X2) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.73/0.99    introduced(choice_axiom,[])).
% 2.73/0.99  
% 2.73/0.99  fof(f50,plain,(
% 2.73/0.99    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2))) & u1_struct_0(X1) = sK1(X0,X1,X2) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.73/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f48,f49])).
% 2.73/0.99  
% 2.73/0.99  fof(f71,plain,(
% 2.73/0.99    ( ! [X4,X2,X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k9_tmap_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f50])).
% 2.73/0.99  
% 2.73/0.99  fof(f112,plain,(
% 2.73/0.99    ( ! [X2,X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),X2,k7_tmap_1(X0,u1_struct_0(X1))) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k9_tmap_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/0.99    inference(equality_resolution,[],[f71])).
% 2.73/0.99  
% 2.73/0.99  fof(f113,plain,(
% 2.73/0.99    ( ! [X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1))) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/0.99    inference(equality_resolution,[],[f112])).
% 2.73/0.99  
% 2.73/0.99  fof(f2,axiom,(
% 2.73/0.99    ! [X0] : ((l1_struct_0(X0) & v2_struct_0(X0)) => v1_xboole_0(u1_struct_0(X0)))),
% 2.73/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f17,plain,(
% 2.73/0.99    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v2_struct_0(X0)))),
% 2.73/0.99    inference(ennf_transformation,[],[f2])).
% 2.73/0.99  
% 2.73/0.99  fof(f18,plain,(
% 2.73/0.99    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0))),
% 2.73/0.99    inference(flattening,[],[f17])).
% 2.73/0.99  
% 2.73/0.99  fof(f63,plain,(
% 2.73/0.99    ( ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f18])).
% 2.73/0.99  
% 2.73/0.99  fof(f79,plain,(
% 2.73/0.99    ( ! [X0,X1] : (v1_funct_1(k7_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f30])).
% 2.73/0.99  
% 2.73/0.99  fof(f81,plain,(
% 2.73/0.99    ( ! [X0,X1] : (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f30])).
% 2.73/0.99  
% 2.73/0.99  fof(f77,plain,(
% 2.73/0.99    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | u1_struct_0(X1) = sK2(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f54])).
% 2.73/0.99  
% 2.73/0.99  cnf(c_25,plain,
% 2.73/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.73/0.99      | ~ v2_pre_topc(X1)
% 2.73/0.99      | v1_funct_1(k9_tmap_1(X1,X0))
% 2.73/0.99      | v2_struct_0(X1)
% 2.73/0.99      | ~ l1_pre_topc(X1) ),
% 2.73/0.99      inference(cnf_transformation,[],[f85]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_35,negated_conjecture,
% 2.73/0.99      ( m1_pre_topc(sK4,sK3)
% 2.73/0.99      | m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) ),
% 2.73/0.99      inference(cnf_transformation,[],[f107]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_43,negated_conjecture,
% 2.73/0.99      ( m1_pre_topc(sK4,sK3) ),
% 2.73/0.99      inference(cnf_transformation,[],[f99]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_278,negated_conjecture,
% 2.73/0.99      ( m1_pre_topc(sK4,sK3) ),
% 2.73/0.99      inference(global_propositional_subsumption,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_35,c_43]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1219,plain,
% 2.73/0.99      ( ~ v2_pre_topc(X0)
% 2.73/0.99      | v1_funct_1(k9_tmap_1(X0,X1))
% 2.73/0.99      | v2_struct_0(X0)
% 2.73/0.99      | ~ l1_pre_topc(X0)
% 2.73/0.99      | sK4 != X1
% 2.73/0.99      | sK3 != X0 ),
% 2.73/0.99      inference(resolution_lifted,[status(thm)],[c_25,c_278]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1220,plain,
% 2.73/0.99      ( ~ v2_pre_topc(sK3)
% 2.73/0.99      | v1_funct_1(k9_tmap_1(sK3,sK4))
% 2.73/0.99      | v2_struct_0(sK3)
% 2.73/0.99      | ~ l1_pre_topc(sK3) ),
% 2.73/0.99      inference(unflattening,[status(thm)],[c_1219]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_46,negated_conjecture,
% 2.73/0.99      ( ~ v2_struct_0(sK3) ),
% 2.73/0.99      inference(cnf_transformation,[],[f96]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_45,negated_conjecture,
% 2.73/0.99      ( v2_pre_topc(sK3) ),
% 2.73/0.99      inference(cnf_transformation,[],[f97]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_44,negated_conjecture,
% 2.73/0.99      ( l1_pre_topc(sK3) ),
% 2.73/0.99      inference(cnf_transformation,[],[f98]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1222,plain,
% 2.73/0.99      ( v1_funct_1(k9_tmap_1(sK3,sK4)) ),
% 2.73/0.99      inference(global_propositional_subsumption,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_1220,c_46,c_45,c_44]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_28,plain,
% 2.73/0.99      ( ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
% 2.73/0.99      | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
% 2.73/0.99      | v3_pre_topc(X1,X0)
% 2.73/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.73/0.99      | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
% 2.73/0.99      | ~ v2_pre_topc(X0)
% 2.73/0.99      | ~ v1_funct_1(k7_tmap_1(X0,X1))
% 2.73/0.99      | v2_struct_0(X0)
% 2.73/0.99      | ~ l1_pre_topc(X0) ),
% 2.73/0.99      inference(cnf_transformation,[],[f94]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_18,plain,
% 2.73/0.99      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
% 2.73/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.73/0.99      | ~ v2_pre_topc(X0)
% 2.73/0.99      | v2_struct_0(X0)
% 2.73/0.99      | ~ l1_pre_topc(X0) ),
% 2.73/0.99      inference(cnf_transformation,[],[f80]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_305,plain,
% 2.73/0.99      ( ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
% 2.73/0.99      | v3_pre_topc(X1,X0)
% 2.73/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.73/0.99      | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
% 2.73/0.99      | ~ v2_pre_topc(X0)
% 2.73/0.99      | ~ v1_funct_1(k7_tmap_1(X0,X1))
% 2.73/0.99      | v2_struct_0(X0)
% 2.73/0.99      | ~ l1_pre_topc(X0) ),
% 2.73/0.99      inference(global_propositional_subsumption,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_28,c_18]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_38,negated_conjecture,
% 2.73/0.99      ( v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4))
% 2.73/0.99      | v1_tsep_1(sK4,sK3) ),
% 2.73/0.99      inference(cnf_transformation,[],[f104]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_618,plain,
% 2.73/0.99      ( v3_pre_topc(X0,X1)
% 2.73/0.99      | v1_tsep_1(sK4,sK3)
% 2.73/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.73/0.99      | ~ m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
% 2.73/0.99      | ~ v2_pre_topc(X1)
% 2.73/0.99      | ~ v1_funct_1(k7_tmap_1(X1,X0))
% 2.73/0.99      | v2_struct_0(X1)
% 2.73/0.99      | ~ l1_pre_topc(X1)
% 2.73/0.99      | k7_tmap_1(X1,X0) != k9_tmap_1(sK3,sK4)
% 2.73/0.99      | k6_tmap_1(X1,X0) != k8_tmap_1(sK3,sK4)
% 2.73/0.99      | sK3 != X1 ),
% 2.73/0.99      inference(resolution_lifted,[status(thm)],[c_305,c_38]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_619,plain,
% 2.73/0.99      ( v3_pre_topc(X0,sK3)
% 2.73/0.99      | v1_tsep_1(sK4,sK3)
% 2.73/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.73/0.99      | ~ m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))))
% 2.73/0.99      | ~ v2_pre_topc(sK3)
% 2.73/0.99      | ~ v1_funct_1(k7_tmap_1(sK3,X0))
% 2.73/0.99      | v2_struct_0(sK3)
% 2.73/0.99      | ~ l1_pre_topc(sK3)
% 2.73/0.99      | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4)
% 2.73/0.99      | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4) ),
% 2.73/0.99      inference(unflattening,[status(thm)],[c_618]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_623,plain,
% 2.73/0.99      ( ~ m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))))
% 2.73/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.73/0.99      | v1_tsep_1(sK4,sK3)
% 2.73/0.99      | v3_pre_topc(X0,sK3)
% 2.73/0.99      | ~ v1_funct_1(k7_tmap_1(sK3,X0))
% 2.73/0.99      | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4)
% 2.73/0.99      | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4) ),
% 2.73/0.99      inference(global_propositional_subsumption,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_619,c_46,c_45,c_44]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_624,plain,
% 2.73/0.99      ( v3_pre_topc(X0,sK3)
% 2.73/0.99      | v1_tsep_1(sK4,sK3)
% 2.73/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.73/0.99      | ~ m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))))
% 2.73/0.99      | ~ v1_funct_1(k7_tmap_1(sK3,X0))
% 2.73/0.99      | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4)
% 2.73/0.99      | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4) ),
% 2.73/0.99      inference(renaming,[status(thm)],[c_623]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_13,plain,
% 2.73/0.99      ( ~ v3_pre_topc(sK2(X0,X1),X0)
% 2.73/0.99      | v1_tsep_1(X1,X0)
% 2.73/0.99      | ~ m1_pre_topc(X1,X0)
% 2.73/0.99      | ~ l1_pre_topc(X0) ),
% 2.73/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1143,plain,
% 2.73/0.99      ( ~ v3_pre_topc(sK2(X0,X1),X0)
% 2.73/0.99      | v1_tsep_1(X1,X0)
% 2.73/0.99      | ~ l1_pre_topc(X0)
% 2.73/0.99      | sK4 != X1
% 2.73/0.99      | sK3 != X0 ),
% 2.73/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_278]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1144,plain,
% 2.73/0.99      ( ~ v3_pre_topc(sK2(sK3,sK4),sK3)
% 2.73/0.99      | v1_tsep_1(sK4,sK3)
% 2.73/0.99      | ~ l1_pre_topc(sK3) ),
% 2.73/0.99      inference(unflattening,[status(thm)],[c_1143]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1146,plain,
% 2.73/0.99      ( v1_tsep_1(sK4,sK3) | ~ v3_pre_topc(sK2(sK3,sK4),sK3) ),
% 2.73/0.99      inference(global_propositional_subsumption,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_1144,c_44]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1147,plain,
% 2.73/0.99      ( ~ v3_pre_topc(sK2(sK3,sK4),sK3) | v1_tsep_1(sK4,sK3) ),
% 2.73/0.99      inference(renaming,[status(thm)],[c_1146]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1525,plain,
% 2.73/0.99      ( v1_tsep_1(sK4,sK3)
% 2.73/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.73/0.99      | ~ m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))))
% 2.73/0.99      | ~ v1_funct_1(k7_tmap_1(sK3,X0))
% 2.73/0.99      | sK2(sK3,sK4) != X0
% 2.73/0.99      | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4)
% 2.73/0.99      | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
% 2.73/0.99      | sK3 != sK3 ),
% 2.73/0.99      inference(resolution_lifted,[status(thm)],[c_624,c_1147]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1526,plain,
% 2.73/0.99      ( v1_tsep_1(sK4,sK3)
% 2.73/0.99      | ~ m1_subset_1(sK2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.73/0.99      | ~ m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4))))))
% 2.73/0.99      | ~ v1_funct_1(k7_tmap_1(sK3,sK2(sK3,sK4)))
% 2.73/0.99      | k7_tmap_1(sK3,sK2(sK3,sK4)) != k9_tmap_1(sK3,sK4)
% 2.73/0.99      | k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4) ),
% 2.73/0.99      inference(unflattening,[status(thm)],[c_1525]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_15,plain,
% 2.73/0.99      ( v1_tsep_1(X0,X1)
% 2.73/0.99      | ~ m1_pre_topc(X0,X1)
% 2.73/0.99      | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.73/0.99      | ~ l1_pre_topc(X1) ),
% 2.73/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1278,plain,
% 2.73/0.99      ( v1_tsep_1(X0,X1)
% 2.73/0.99      | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.73/0.99      | ~ l1_pre_topc(X1)
% 2.73/0.99      | sK4 != X0
% 2.73/0.99      | sK3 != X1 ),
% 2.73/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_278]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1279,plain,
% 2.73/0.99      ( v1_tsep_1(sK4,sK3)
% 2.73/0.99      | m1_subset_1(sK2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.73/0.99      | ~ l1_pre_topc(sK3) ),
% 2.73/0.99      inference(unflattening,[status(thm)],[c_1278]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1528,plain,
% 2.73/0.99      ( v1_tsep_1(sK4,sK3)
% 2.73/0.99      | ~ m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4))))))
% 2.73/0.99      | ~ v1_funct_1(k7_tmap_1(sK3,sK2(sK3,sK4)))
% 2.73/0.99      | k7_tmap_1(sK3,sK2(sK3,sK4)) != k9_tmap_1(sK3,sK4)
% 2.73/0.99      | k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4) ),
% 2.73/0.99      inference(global_propositional_subsumption,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_1526,c_44,c_1279]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_2316,plain,
% 2.73/0.99      ( v1_tsep_1(sK4,sK3)
% 2.73/0.99      | ~ m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4))))))
% 2.73/0.99      | k7_tmap_1(sK3,sK2(sK3,sK4)) != k9_tmap_1(sK3,sK4)
% 2.73/0.99      | k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4) ),
% 2.73/0.99      inference(resolution_lifted,[status(thm)],[c_1222,c_1528]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_3751,plain,
% 2.73/0.99      ( v1_tsep_1(sK4,sK3)
% 2.73/0.99      | ~ m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4))))))
% 2.73/0.99      | k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4)
% 2.73/0.99      | k7_tmap_1(sK3,sK2(sK3,sK4)) != k9_tmap_1(sK3,sK4) ),
% 2.73/0.99      inference(subtyping,[status(esa)],[c_2316]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_4504,plain,
% 2.73/0.99      ( k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4)
% 2.73/0.99      | k7_tmap_1(sK3,sK2(sK3,sK4)) != k9_tmap_1(sK3,sK4)
% 2.73/0.99      | v1_tsep_1(sK4,sK3) = iProver_top
% 2.73/0.99      | m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4)))))) != iProver_top ),
% 2.73/0.99      inference(predicate_to_equality,[status(thm)],[c_3751]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_47,plain,
% 2.73/0.99      ( v2_struct_0(sK3) != iProver_top ),
% 2.73/0.99      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_49,plain,
% 2.73/0.99      ( l1_pre_topc(sK3) = iProver_top ),
% 2.73/0.99      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_2,plain,
% 2.73/0.99      ( v2_struct_0(X0)
% 2.73/0.99      | ~ v1_xboole_0(u1_struct_0(X0))
% 2.73/0.99      | ~ l1_struct_0(X0) ),
% 2.73/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_153,plain,
% 2.73/0.99      ( v2_struct_0(X0) = iProver_top
% 2.73/0.99      | v1_xboole_0(u1_struct_0(X0)) != iProver_top
% 2.73/0.99      | l1_struct_0(X0) != iProver_top ),
% 2.73/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_155,plain,
% 2.73/0.99      ( v2_struct_0(sK3) = iProver_top
% 2.73/0.99      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top
% 2.73/0.99      | l1_struct_0(sK3) != iProver_top ),
% 2.73/0.99      inference(instantiation,[status(thm)],[c_153]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_0,plain,
% 2.73/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.73/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_157,plain,
% 2.73/0.99      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 2.73/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_159,plain,
% 2.73/0.99      ( l1_pre_topc(sK3) != iProver_top
% 2.73/0.99      | l1_struct_0(sK3) = iProver_top ),
% 2.73/0.99      inference(instantiation,[status(thm)],[c_157]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_33,plain,
% 2.73/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.73/0.99      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.73/0.99      | ~ l1_pre_topc(X1) ),
% 2.73/0.99      inference(cnf_transformation,[],[f95]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1206,plain,
% 2.73/0.99      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.73/0.99      | ~ l1_pre_topc(X1)
% 2.73/0.99      | sK4 != X0
% 2.73/0.99      | sK3 != X1 ),
% 2.73/0.99      inference(resolution_lifted,[status(thm)],[c_33,c_278]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1207,plain,
% 2.73/0.99      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.73/0.99      | ~ l1_pre_topc(sK3) ),
% 2.73/0.99      inference(unflattening,[status(thm)],[c_1206]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1208,plain,
% 2.73/0.99      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 2.73/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 2.73/0.99      inference(predicate_to_equality,[status(thm)],[c_1207]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_23,plain,
% 2.73/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.73/0.99      | m1_subset_1(k9_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X0)))))
% 2.73/0.99      | ~ v2_pre_topc(X1)
% 2.73/0.99      | v2_struct_0(X1)
% 2.73/0.99      | ~ l1_pre_topc(X1) ),
% 2.73/0.99      inference(cnf_transformation,[],[f87]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1232,plain,
% 2.73/0.99      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 2.73/0.99      | ~ v2_pre_topc(X0)
% 2.73/0.99      | v2_struct_0(X0)
% 2.73/0.99      | ~ l1_pre_topc(X0)
% 2.73/0.99      | sK4 != X1
% 2.73/0.99      | sK3 != X0 ),
% 2.73/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_278]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1233,plain,
% 2.73/0.99      ( m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 2.73/0.99      | ~ v2_pre_topc(sK3)
% 2.73/0.99      | v2_struct_0(sK3)
% 2.73/0.99      | ~ l1_pre_topc(sK3) ),
% 2.73/0.99      inference(unflattening,[status(thm)],[c_1232]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1235,plain,
% 2.73/0.99      ( m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) ),
% 2.73/0.99      inference(global_propositional_subsumption,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_1233,c_46,c_45,c_44]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_24,plain,
% 2.73/0.99      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 2.73/0.99      | ~ m1_pre_topc(X1,X0)
% 2.73/0.99      | ~ v2_pre_topc(X0)
% 2.73/0.99      | v2_struct_0(X0)
% 2.73/0.99      | ~ l1_pre_topc(X0) ),
% 2.73/0.99      inference(cnf_transformation,[],[f86]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1132,plain,
% 2.73/0.99      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 2.73/0.99      | ~ v2_pre_topc(X0)
% 2.73/0.99      | v2_struct_0(X0)
% 2.73/0.99      | ~ l1_pre_topc(X0)
% 2.73/0.99      | sK4 != X1
% 2.73/0.99      | sK3 != X0 ),
% 2.73/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_278]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1133,plain,
% 2.73/0.99      ( v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 2.73/0.99      | ~ v2_pre_topc(sK3)
% 2.73/0.99      | v2_struct_0(sK3)
% 2.73/0.99      | ~ l1_pre_topc(sK3) ),
% 2.73/0.99      inference(unflattening,[status(thm)],[c_1132]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1135,plain,
% 2.73/0.99      ( v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) ),
% 2.73/0.99      inference(global_propositional_subsumption,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_1133,c_46,c_45,c_44]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_30,plain,
% 2.73/0.99      ( v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
% 2.73/0.99      | ~ v3_pre_topc(X1,X0)
% 2.73/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.73/0.99      | ~ v2_pre_topc(X0)
% 2.73/0.99      | v2_struct_0(X0)
% 2.73/0.99      | ~ l1_pre_topc(X0) ),
% 2.73/0.99      inference(cnf_transformation,[],[f92]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_34,negated_conjecture,
% 2.73/0.99      ( ~ v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4))
% 2.73/0.99      | ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 2.73/0.99      | ~ v1_tsep_1(sK4,sK3)
% 2.73/0.99      | ~ m1_pre_topc(sK4,sK3)
% 2.73/0.99      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 2.73/0.99      | ~ v1_funct_1(k9_tmap_1(sK3,sK4)) ),
% 2.73/0.99      inference(cnf_transformation,[],[f108]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_283,plain,
% 2.73/0.99      ( ~ v1_tsep_1(sK4,sK3)
% 2.73/0.99      | ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 2.73/0.99      | ~ v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4))
% 2.73/0.99      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 2.73/0.99      | ~ v1_funct_1(k9_tmap_1(sK3,sK4)) ),
% 2.73/0.99      inference(global_propositional_subsumption,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_34,c_43]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_284,negated_conjecture,
% 2.73/0.99      ( ~ v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4))
% 2.73/0.99      | ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 2.73/0.99      | ~ v1_tsep_1(sK4,sK3)
% 2.73/0.99      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 2.73/0.99      | ~ v1_funct_1(k9_tmap_1(sK3,sK4)) ),
% 2.73/0.99      inference(renaming,[status(thm)],[c_283]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_582,plain,
% 2.73/0.99      ( ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 2.73/0.99      | ~ v3_pre_topc(X0,X1)
% 2.73/0.99      | ~ v1_tsep_1(sK4,sK3)
% 2.73/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.73/0.99      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 2.73/0.99      | ~ v2_pre_topc(X1)
% 2.73/0.99      | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
% 2.73/0.99      | v2_struct_0(X1)
% 2.73/0.99      | ~ l1_pre_topc(X1)
% 2.73/0.99      | k7_tmap_1(X1,X0) != k9_tmap_1(sK3,sK4)
% 2.73/0.99      | k6_tmap_1(X1,X0) != k8_tmap_1(sK3,sK4)
% 2.73/0.99      | sK3 != X1 ),
% 2.73/0.99      inference(resolution_lifted,[status(thm)],[c_30,c_284]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_583,plain,
% 2.73/0.99      ( ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 2.73/0.99      | ~ v3_pre_topc(X0,sK3)
% 2.73/0.99      | ~ v1_tsep_1(sK4,sK3)
% 2.73/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.73/0.99      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 2.73/0.99      | ~ v2_pre_topc(sK3)
% 2.73/0.99      | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
% 2.73/0.99      | v2_struct_0(sK3)
% 2.73/0.99      | ~ l1_pre_topc(sK3)
% 2.73/0.99      | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4)
% 2.73/0.99      | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4) ),
% 2.73/0.99      inference(unflattening,[status(thm)],[c_582]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_587,plain,
% 2.73/0.99      ( ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 2.73/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.73/0.99      | ~ v1_tsep_1(sK4,sK3)
% 2.73/0.99      | ~ v3_pre_topc(X0,sK3)
% 2.73/0.99      | ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 2.73/0.99      | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
% 2.73/0.99      | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4)
% 2.73/0.99      | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4) ),
% 2.73/0.99      inference(global_propositional_subsumption,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_583,c_46,c_45,c_44]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_588,plain,
% 2.73/0.99      ( ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 2.73/0.99      | ~ v3_pre_topc(X0,sK3)
% 2.73/0.99      | ~ v1_tsep_1(sK4,sK3)
% 2.73/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.73/0.99      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 2.73/0.99      | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
% 2.73/0.99      | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4)
% 2.73/0.99      | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4) ),
% 2.73/0.99      inference(renaming,[status(thm)],[c_587]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1443,plain,
% 2.73/0.99      ( ~ v3_pre_topc(X0,sK3)
% 2.73/0.99      | ~ v1_tsep_1(sK4,sK3)
% 2.73/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.73/0.99      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 2.73/0.99      | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
% 2.73/0.99      | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4)
% 2.73/0.99      | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4) ),
% 2.73/0.99      inference(backward_subsumption_resolution,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_1135,c_588]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1464,plain,
% 2.73/0.99      ( ~ v3_pre_topc(X0,sK3)
% 2.73/0.99      | ~ v1_tsep_1(sK4,sK3)
% 2.73/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.73/0.99      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 2.73/0.99      | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4)
% 2.73/0.99      | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4) ),
% 2.73/0.99      inference(backward_subsumption_resolution,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_1222,c_1443]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1470,plain,
% 2.73/0.99      ( ~ v3_pre_topc(X0,sK3)
% 2.73/0.99      | ~ v1_tsep_1(sK4,sK3)
% 2.73/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.73/0.99      | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4)
% 2.73/0.99      | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4) ),
% 2.73/0.99      inference(backward_subsumption_resolution,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_1235,c_1464]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_16,plain,
% 2.73/0.99      ( v3_pre_topc(u1_struct_0(X0),X1)
% 2.73/0.99      | ~ v1_tsep_1(X0,X1)
% 2.73/0.99      | ~ m1_pre_topc(X0,X1)
% 2.73/0.99      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.73/0.99      | ~ l1_pre_topc(X1) ),
% 2.73/0.99      inference(cnf_transformation,[],[f114]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_323,plain,
% 2.73/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.73/0.99      | ~ v1_tsep_1(X0,X1)
% 2.73/0.99      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.73/0.99      | ~ l1_pre_topc(X1) ),
% 2.73/0.99      inference(global_propositional_subsumption,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_16,c_33]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_324,plain,
% 2.73/0.99      ( v3_pre_topc(u1_struct_0(X0),X1)
% 2.73/0.99      | ~ v1_tsep_1(X0,X1)
% 2.73/0.99      | ~ m1_pre_topc(X0,X1)
% 2.73/0.99      | ~ l1_pre_topc(X1) ),
% 2.73/0.99      inference(renaming,[status(thm)],[c_323]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1192,plain,
% 2.73/0.99      ( v3_pre_topc(u1_struct_0(X0),X1)
% 2.73/0.99      | ~ v1_tsep_1(X0,X1)
% 2.73/0.99      | ~ l1_pre_topc(X1)
% 2.73/0.99      | sK4 != X0
% 2.73/0.99      | sK3 != X1 ),
% 2.73/0.99      inference(resolution_lifted,[status(thm)],[c_324,c_278]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1193,plain,
% 2.73/0.99      ( v3_pre_topc(u1_struct_0(sK4),sK3)
% 2.73/0.99      | ~ v1_tsep_1(sK4,sK3)
% 2.73/0.99      | ~ l1_pre_topc(sK3) ),
% 2.73/0.99      inference(unflattening,[status(thm)],[c_1192]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1195,plain,
% 2.73/0.99      ( ~ v1_tsep_1(sK4,sK3) | v3_pre_topc(u1_struct_0(sK4),sK3) ),
% 2.73/0.99      inference(global_propositional_subsumption,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_1193,c_44]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1196,plain,
% 2.73/0.99      ( v3_pre_topc(u1_struct_0(sK4),sK3) | ~ v1_tsep_1(sK4,sK3) ),
% 2.73/0.99      inference(renaming,[status(thm)],[c_1195]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1548,plain,
% 2.73/0.99      ( ~ v1_tsep_1(sK4,sK3)
% 2.73/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.73/0.99      | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4)
% 2.73/0.99      | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
% 2.73/0.99      | u1_struct_0(sK4) != X0
% 2.73/0.99      | sK3 != sK3 ),
% 2.73/0.99      inference(resolution_lifted,[status(thm)],[c_1470,c_1196]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1549,plain,
% 2.73/0.99      ( ~ v1_tsep_1(sK4,sK3)
% 2.73/0.99      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.73/0.99      | k7_tmap_1(sK3,u1_struct_0(sK4)) != k9_tmap_1(sK3,sK4)
% 2.73/0.99      | k6_tmap_1(sK3,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4) ),
% 2.73/0.99      inference(unflattening,[status(thm)],[c_1548]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_8,plain,
% 2.73/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.73/0.99      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.73/0.99      | ~ v1_pre_topc(k8_tmap_1(X1,X0))
% 2.73/0.99      | ~ v2_pre_topc(X1)
% 2.73/0.99      | ~ v2_pre_topc(k8_tmap_1(X1,X0))
% 2.73/0.99      | v2_struct_0(X1)
% 2.73/0.99      | ~ l1_pre_topc(X1)
% 2.73/0.99      | ~ l1_pre_topc(k8_tmap_1(X1,X0))
% 2.73/0.99      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 2.73/0.99      inference(cnf_transformation,[],[f111]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_22,plain,
% 2.73/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.73/0.99      | v1_pre_topc(k8_tmap_1(X1,X0))
% 2.73/0.99      | ~ v2_pre_topc(X1)
% 2.73/0.99      | v2_struct_0(X1)
% 2.73/0.99      | ~ l1_pre_topc(X1) ),
% 2.73/0.99      inference(cnf_transformation,[],[f82]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_21,plain,
% 2.73/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.73/0.99      | ~ v2_pre_topc(X1)
% 2.73/0.99      | v2_pre_topc(k8_tmap_1(X1,X0))
% 2.73/0.99      | v2_struct_0(X1)
% 2.73/0.99      | ~ l1_pre_topc(X1) ),
% 2.73/0.99      inference(cnf_transformation,[],[f83]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_20,plain,
% 2.73/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.73/0.99      | ~ v2_pre_topc(X1)
% 2.73/0.99      | v2_struct_0(X1)
% 2.73/0.99      | ~ l1_pre_topc(X1)
% 2.73/0.99      | l1_pre_topc(k8_tmap_1(X1,X0)) ),
% 2.73/0.99      inference(cnf_transformation,[],[f84]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_343,plain,
% 2.73/0.99      ( ~ l1_pre_topc(X1)
% 2.73/0.99      | v2_struct_0(X1)
% 2.73/0.99      | ~ m1_pre_topc(X0,X1)
% 2.73/0.99      | ~ v2_pre_topc(X1)
% 2.73/0.99      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 2.73/0.99      inference(global_propositional_subsumption,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_8,c_33,c_22,c_21,c_20]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_344,plain,
% 2.73/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.73/0.99      | ~ v2_pre_topc(X1)
% 2.73/0.99      | v2_struct_0(X1)
% 2.73/0.99      | ~ l1_pre_topc(X1)
% 2.73/0.99      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 2.73/0.99      inference(renaming,[status(thm)],[c_343]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1184,plain,
% 2.73/0.99      ( ~ v2_pre_topc(X0)
% 2.73/0.99      | v2_struct_0(X0)
% 2.73/0.99      | ~ l1_pre_topc(X0)
% 2.73/0.99      | k6_tmap_1(X0,u1_struct_0(X1)) = k8_tmap_1(X0,X1)
% 2.73/0.99      | sK4 != X1
% 2.73/0.99      | sK3 != X0 ),
% 2.73/0.99      inference(resolution_lifted,[status(thm)],[c_344,c_278]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1185,plain,
% 2.73/0.99      ( ~ v2_pre_topc(sK3)
% 2.73/0.99      | v2_struct_0(sK3)
% 2.73/0.99      | ~ l1_pre_topc(sK3)
% 2.73/0.99      | k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4) ),
% 2.73/0.99      inference(unflattening,[status(thm)],[c_1184]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1551,plain,
% 2.73/0.99      ( k7_tmap_1(sK3,u1_struct_0(sK4)) != k9_tmap_1(sK3,sK4)
% 2.73/0.99      | ~ v1_tsep_1(sK4,sK3) ),
% 2.73/0.99      inference(global_propositional_subsumption,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_1549,c_46,c_45,c_44,c_1185,c_1207]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1552,plain,
% 2.73/0.99      ( ~ v1_tsep_1(sK4,sK3)
% 2.73/0.99      | k7_tmap_1(sK3,u1_struct_0(sK4)) != k9_tmap_1(sK3,sK4) ),
% 2.73/0.99      inference(renaming,[status(thm)],[c_1551]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_3765,plain,
% 2.73/0.99      ( ~ v1_tsep_1(sK4,sK3)
% 2.73/0.99      | k7_tmap_1(sK3,u1_struct_0(sK4)) != k9_tmap_1(sK3,sK4) ),
% 2.73/0.99      inference(subtyping,[status(esa)],[c_1552]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1209,plain,
% 2.73/0.99      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.73/0.99      inference(global_propositional_subsumption,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_1207,c_44]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_3772,plain,
% 2.73/0.99      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.73/0.99      inference(subtyping,[status(esa)],[c_1209]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_4483,plain,
% 2.73/0.99      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.73/0.99      inference(predicate_to_equality,[status(thm)],[c_3772]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_27,plain,
% 2.73/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.73/0.99      | ~ v2_pre_topc(X1)
% 2.73/0.99      | v2_struct_0(X1)
% 2.73/0.99      | ~ l1_pre_topc(X1)
% 2.73/0.99      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
% 2.73/0.99      inference(cnf_transformation,[],[f88]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1734,plain,
% 2.73/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.73/0.99      | v2_struct_0(X1)
% 2.73/0.99      | ~ l1_pre_topc(X1)
% 2.73/0.99      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1)
% 2.73/0.99      | sK3 != X1 ),
% 2.73/0.99      inference(resolution_lifted,[status(thm)],[c_27,c_45]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1735,plain,
% 2.73/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.73/0.99      | v2_struct_0(sK3)
% 2.73/0.99      | ~ l1_pre_topc(sK3)
% 2.73/0.99      | u1_struct_0(k6_tmap_1(sK3,X0)) = u1_struct_0(sK3) ),
% 2.73/0.99      inference(unflattening,[status(thm)],[c_1734]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1739,plain,
% 2.73/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.73/0.99      | u1_struct_0(k6_tmap_1(sK3,X0)) = u1_struct_0(sK3) ),
% 2.73/0.99      inference(global_propositional_subsumption,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_1735,c_46,c_44]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_3762,plain,
% 2.73/0.99      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.73/0.99      | u1_struct_0(k6_tmap_1(sK3,X0_56)) = u1_struct_0(sK3) ),
% 2.73/0.99      inference(subtyping,[status(esa)],[c_1739]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_4493,plain,
% 2.73/0.99      ( u1_struct_0(k6_tmap_1(sK3,X0_56)) = u1_struct_0(sK3)
% 2.73/0.99      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.73/0.99      inference(predicate_to_equality,[status(thm)],[c_3762]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_4907,plain,
% 2.73/0.99      ( u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))) = u1_struct_0(sK3) ),
% 2.73/0.99      inference(superposition,[status(thm)],[c_4483,c_4493]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1187,plain,
% 2.73/0.99      ( k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4) ),
% 2.73/0.99      inference(global_propositional_subsumption,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_1185,c_46,c_45,c_44]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_3773,plain,
% 2.73/0.99      ( k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4) ),
% 2.73/0.99      inference(subtyping,[status(esa)],[c_1187]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_4914,plain,
% 2.73/0.99      ( u1_struct_0(k8_tmap_1(sK3,sK4)) = u1_struct_0(sK3) ),
% 2.73/0.99      inference(light_normalisation,[status(thm)],[c_4907,c_3773]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_4,plain,
% 2.73/0.99      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
% 2.73/0.99      | ~ v1_funct_2(X5,X2,X3)
% 2.73/0.99      | ~ v1_funct_2(X4,X0,X1)
% 2.73/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.73/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.73/0.99      | ~ v1_funct_1(X5)
% 2.73/0.99      | ~ v1_funct_1(X4)
% 2.73/0.99      | v1_xboole_0(X1)
% 2.73/0.99      | v1_xboole_0(X3)
% 2.73/0.99      | X4 = X5 ),
% 2.73/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_12,plain,
% 2.73/0.99      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
% 2.73/0.99      | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 2.73/0.99      | ~ m1_pre_topc(X1,X0)
% 2.73/0.99      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 2.73/0.99      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
% 2.73/0.99      | ~ v2_pre_topc(X0)
% 2.73/0.99      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 2.73/0.99      | v2_struct_0(X0)
% 2.73/0.99      | ~ l1_pre_topc(X0) ),
% 2.73/0.99      inference(cnf_transformation,[],[f113]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_333,plain,
% 2.73/0.99      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
% 2.73/0.99      | ~ m1_pre_topc(X1,X0)
% 2.73/0.99      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 2.73/0.99      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
% 2.73/0.99      | ~ v2_pre_topc(X0)
% 2.73/0.99      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 2.73/0.99      | v2_struct_0(X0)
% 2.73/0.99      | ~ l1_pre_topc(X0) ),
% 2.73/0.99      inference(global_propositional_subsumption,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_12,c_24]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1112,plain,
% 2.73/0.99      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
% 2.73/0.99      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 2.73/0.99      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
% 2.73/0.99      | ~ v2_pre_topc(X0)
% 2.73/0.99      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 2.73/0.99      | v2_struct_0(X0)
% 2.73/0.99      | ~ l1_pre_topc(X0)
% 2.73/0.99      | sK4 != X1
% 2.73/0.99      | sK3 != X0 ),
% 2.73/0.99      inference(resolution_lifted,[status(thm)],[c_333,c_278]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1113,plain,
% 2.73/0.99      ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)))
% 2.73/0.99      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 2.73/0.99      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.73/0.99      | ~ v2_pre_topc(sK3)
% 2.73/0.99      | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
% 2.73/0.99      | v2_struct_0(sK3)
% 2.73/0.99      | ~ l1_pre_topc(sK3) ),
% 2.73/0.99      inference(unflattening,[status(thm)],[c_1112]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1115,plain,
% 2.73/0.99      ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.73/0.99      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 2.73/0.99      | r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)))
% 2.73/0.99      | ~ v1_funct_1(k9_tmap_1(sK3,sK4)) ),
% 2.73/0.99      inference(global_propositional_subsumption,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_1113,c_46,c_45,c_44]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1116,plain,
% 2.73/0.99      ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)))
% 2.73/0.99      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 2.73/0.99      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.73/0.99      | ~ v1_funct_1(k9_tmap_1(sK3,sK4)) ),
% 2.73/0.99      inference(renaming,[status(thm)],[c_1115]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1216,plain,
% 2.73/0.99      ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)))
% 2.73/0.99      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 2.73/0.99      | ~ v1_funct_1(k9_tmap_1(sK3,sK4)) ),
% 2.73/0.99      inference(backward_subsumption_resolution,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_1209,c_1116]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1229,plain,
% 2.73/0.99      ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)))
% 2.73/0.99      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) ),
% 2.73/0.99      inference(backward_subsumption_resolution,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_1222,c_1216]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1242,plain,
% 2.73/0.99      ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4))) ),
% 2.73/0.99      inference(backward_subsumption_resolution,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_1235,c_1229]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1650,plain,
% 2.73/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.73/0.99      | ~ v1_funct_2(X3,X4,X5)
% 2.73/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.73/0.99      | ~ v1_funct_1(X0)
% 2.73/0.99      | ~ v1_funct_1(X3)
% 2.73/0.99      | v1_xboole_0(X2)
% 2.73/0.99      | v1_xboole_0(X5)
% 2.73/0.99      | X3 = X0
% 2.73/0.99      | k7_tmap_1(sK3,u1_struct_0(sK4)) != X3
% 2.73/0.99      | k9_tmap_1(sK3,sK4) != X0
% 2.73/0.99      | u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))) != X5
% 2.73/0.99      | u1_struct_0(k8_tmap_1(sK3,sK4)) != X2
% 2.73/0.99      | u1_struct_0(sK3) != X4
% 2.73/0.99      | u1_struct_0(sK3) != X1 ),
% 2.73/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_1242]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1651,plain,
% 2.73/0.99      ( ~ v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
% 2.73/0.99      | ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 2.73/0.99      | ~ m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))))
% 2.73/0.99      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 2.73/0.99      | ~ v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4)))
% 2.73/0.99      | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
% 2.73/0.99      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
% 2.73/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4)))
% 2.73/0.99      | k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4) ),
% 2.73/0.99      inference(unflattening,[status(thm)],[c_1650]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1653,plain,
% 2.73/0.99      ( ~ v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4)))
% 2.73/0.99      | ~ v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
% 2.73/0.99      | ~ m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))))
% 2.73/0.99      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
% 2.73/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4)))
% 2.73/0.99      | k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4) ),
% 2.73/0.99      inference(global_propositional_subsumption,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_1651,c_46,c_45,c_44,c_1133,c_1220,c_1233]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1654,plain,
% 2.73/0.99      ( ~ v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
% 2.73/0.99      | ~ m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))))
% 2.73/0.99      | ~ v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4)))
% 2.73/0.99      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
% 2.73/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4)))
% 2.73/0.99      | k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4) ),
% 2.73/0.99      inference(renaming,[status(thm)],[c_1653]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_546,plain,
% 2.73/0.99      ( v2_struct_0(X0)
% 2.73/0.99      | ~ v1_xboole_0(u1_struct_0(X0))
% 2.73/0.99      | ~ l1_pre_topc(X0) ),
% 2.73/0.99      inference(resolution,[status(thm)],[c_0,c_2]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1267,plain,
% 2.73/0.99      ( ~ v2_pre_topc(X0)
% 2.73/0.99      | v2_struct_0(X0)
% 2.73/0.99      | ~ l1_pre_topc(X0)
% 2.73/0.99      | l1_pre_topc(k8_tmap_1(X0,X1))
% 2.73/0.99      | sK4 != X1
% 2.73/0.99      | sK3 != X0 ),
% 2.73/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_278]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1268,plain,
% 2.73/0.99      ( ~ v2_pre_topc(sK3)
% 2.73/0.99      | v2_struct_0(sK3)
% 2.73/0.99      | l1_pre_topc(k8_tmap_1(sK3,sK4))
% 2.73/0.99      | ~ l1_pre_topc(sK3) ),
% 2.73/0.99      inference(unflattening,[status(thm)],[c_1267]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1270,plain,
% 2.73/0.99      ( l1_pre_topc(k8_tmap_1(sK3,sK4)) ),
% 2.73/0.99      inference(global_propositional_subsumption,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_1268,c_46,c_45,c_44]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1948,plain,
% 2.73/0.99      ( v2_struct_0(X0)
% 2.73/0.99      | ~ v1_xboole_0(u1_struct_0(X0))
% 2.73/0.99      | k8_tmap_1(sK3,sK4) != X0 ),
% 2.73/0.99      inference(resolution_lifted,[status(thm)],[c_546,c_1270]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1949,plain,
% 2.73/0.99      ( v2_struct_0(k8_tmap_1(sK3,sK4))
% 2.73/0.99      | ~ v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4))) ),
% 2.73/0.99      inference(unflattening,[status(thm)],[c_1948]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_2851,plain,
% 2.73/0.99      ( v2_struct_0(k8_tmap_1(sK3,sK4))
% 2.73/0.99      | ~ v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4))) ),
% 2.73/0.99      inference(prop_impl,[status(thm)],[c_1949]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_2902,plain,
% 2.73/0.99      ( ~ v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
% 2.73/0.99      | ~ m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))))
% 2.73/0.99      | ~ v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4)))
% 2.73/0.99      | v2_struct_0(k8_tmap_1(sK3,sK4))
% 2.73/0.99      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
% 2.73/0.99      | k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4) ),
% 2.73/0.99      inference(bin_hyper_res,[status(thm)],[c_1654,c_2851]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_3749,plain,
% 2.73/0.99      ( ~ v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
% 2.73/0.99      | ~ m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))))
% 2.73/0.99      | ~ v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4)))
% 2.73/0.99      | v2_struct_0(k8_tmap_1(sK3,sK4))
% 2.73/0.99      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
% 2.73/0.99      | k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4) ),
% 2.73/0.99      inference(subtyping,[status(esa)],[c_2902]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_4506,plain,
% 2.73/0.99      ( k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4)
% 2.73/0.99      | v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))) != iProver_top
% 2.73/0.99      | m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))))) != iProver_top
% 2.73/0.99      | v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4))) != iProver_top
% 2.73/0.99      | v2_struct_0(k8_tmap_1(sK3,sK4)) = iProver_top
% 2.73/0.99      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))) = iProver_top ),
% 2.73/0.99      inference(predicate_to_equality,[status(thm)],[c_3749]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_4619,plain,
% 2.73/0.99      ( k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4)
% 2.73/0.99      | v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
% 2.73/0.99      | m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) != iProver_top
% 2.73/0.99      | v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4))) != iProver_top
% 2.73/0.99      | v2_struct_0(k8_tmap_1(sK3,sK4)) = iProver_top
% 2.73/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4))) = iProver_top ),
% 2.73/0.99      inference(light_normalisation,[status(thm)],[c_4506,c_3773]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1,plain,
% 2.73/0.99      ( ~ v2_struct_0(X0)
% 2.73/0.99      | v1_xboole_0(u1_struct_0(X0))
% 2.73/0.99      | ~ l1_struct_0(X0) ),
% 2.73/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_560,plain,
% 2.73/0.99      ( ~ v2_struct_0(X0)
% 2.73/0.99      | v1_xboole_0(u1_struct_0(X0))
% 2.73/0.99      | ~ l1_pre_topc(X0) ),
% 2.73/0.99      inference(resolution,[status(thm)],[c_0,c_1]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1938,plain,
% 2.73/0.99      ( ~ v2_struct_0(X0)
% 2.73/0.99      | v1_xboole_0(u1_struct_0(X0))
% 2.73/0.99      | k8_tmap_1(sK3,sK4) != X0 ),
% 2.73/0.99      inference(resolution_lifted,[status(thm)],[c_560,c_1270]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1939,plain,
% 2.73/0.99      ( ~ v2_struct_0(k8_tmap_1(sK3,sK4))
% 2.73/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4))) ),
% 2.73/0.99      inference(unflattening,[status(thm)],[c_1938]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_2853,plain,
% 2.73/0.99      ( ~ v2_struct_0(k8_tmap_1(sK3,sK4))
% 2.73/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4))) ),
% 2.73/0.99      inference(prop_impl,[status(thm)],[c_1939]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_3753,plain,
% 2.73/0.99      ( ~ v2_struct_0(k8_tmap_1(sK3,sK4))
% 2.73/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4))) ),
% 2.73/0.99      inference(subtyping,[status(esa)],[c_2853]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_4502,plain,
% 2.73/0.99      ( v2_struct_0(k8_tmap_1(sK3,sK4)) != iProver_top
% 2.73/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4))) = iProver_top ),
% 2.73/0.99      inference(predicate_to_equality,[status(thm)],[c_3753]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_4626,plain,
% 2.73/0.99      ( k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4)
% 2.73/0.99      | v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
% 2.73/0.99      | m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) != iProver_top
% 2.73/0.99      | v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4))) != iProver_top
% 2.73/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4))) = iProver_top ),
% 2.73/0.99      inference(forward_subsumption_resolution,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_4619,c_4502]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_19,plain,
% 2.73/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.73/0.99      | ~ v2_pre_topc(X1)
% 2.73/0.99      | v1_funct_1(k7_tmap_1(X1,X0))
% 2.73/0.99      | v2_struct_0(X1)
% 2.73/0.99      | ~ l1_pre_topc(X1) ),
% 2.73/0.99      inference(cnf_transformation,[],[f79]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1770,plain,
% 2.73/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.73/0.99      | v1_funct_1(k7_tmap_1(X1,X0))
% 2.73/0.99      | v2_struct_0(X1)
% 2.73/0.99      | ~ l1_pre_topc(X1)
% 2.73/0.99      | sK3 != X1 ),
% 2.73/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_45]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1771,plain,
% 2.73/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.73/0.99      | v1_funct_1(k7_tmap_1(sK3,X0))
% 2.73/0.99      | v2_struct_0(sK3)
% 2.73/0.99      | ~ l1_pre_topc(sK3) ),
% 2.73/0.99      inference(unflattening,[status(thm)],[c_1770]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1775,plain,
% 2.73/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.73/0.99      | v1_funct_1(k7_tmap_1(sK3,X0)) ),
% 2.73/0.99      inference(global_propositional_subsumption,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_1771,c_46,c_44]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_3760,plain,
% 2.73/0.99      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.73/0.99      | v1_funct_1(k7_tmap_1(sK3,X0_56)) ),
% 2.73/0.99      inference(subtyping,[status(esa)],[c_1775]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_4706,plain,
% 2.73/0.99      ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.73/0.99      | v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4))) ),
% 2.73/0.99      inference(instantiation,[status(thm)],[c_3760]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_4707,plain,
% 2.73/0.99      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.73/0.99      | v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4))) = iProver_top ),
% 2.73/0.99      inference(predicate_to_equality,[status(thm)],[c_4706]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_4877,plain,
% 2.73/0.99      ( m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) != iProver_top
% 2.73/0.99      | v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
% 2.73/0.99      | k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4)
% 2.73/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4))) = iProver_top ),
% 2.73/0.99      inference(global_propositional_subsumption,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_4626,c_49,c_1208,c_4707]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_4878,plain,
% 2.73/0.99      ( k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4)
% 2.73/0.99      | v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
% 2.73/0.99      | m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) != iProver_top
% 2.73/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4))) = iProver_top ),
% 2.73/0.99      inference(renaming,[status(thm)],[c_4877]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_4918,plain,
% 2.73/0.99      ( k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4)
% 2.73/0.99      | v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
% 2.73/0.99      | m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) != iProver_top
% 2.73/0.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 2.73/0.99      inference(demodulation,[status(thm)],[c_4914,c_4878]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1695,plain,
% 2.73/0.99      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
% 2.73/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.73/0.99      | v2_struct_0(X0)
% 2.73/0.99      | ~ l1_pre_topc(X0)
% 2.73/0.99      | sK3 != X0 ),
% 2.73/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_45]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1696,plain,
% 2.73/0.99      ( v1_funct_2(k7_tmap_1(sK3,X0),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))
% 2.73/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.73/0.99      | v2_struct_0(sK3)
% 2.73/0.99      | ~ l1_pre_topc(sK3) ),
% 2.73/0.99      inference(unflattening,[status(thm)],[c_1695]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1700,plain,
% 2.73/0.99      ( v1_funct_2(k7_tmap_1(sK3,X0),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))
% 2.73/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.73/0.99      inference(global_propositional_subsumption,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_1696,c_46,c_44]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_3764,plain,
% 2.73/0.99      ( v1_funct_2(k7_tmap_1(sK3,X0_56),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0_56)))
% 2.73/0.99      | ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.73/0.99      inference(subtyping,[status(esa)],[c_1700]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_4491,plain,
% 2.73/0.99      ( v1_funct_2(k7_tmap_1(sK3,X0_56),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0_56))) = iProver_top
% 2.73/0.99      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.73/0.99      inference(predicate_to_equality,[status(thm)],[c_3764]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_5079,plain,
% 2.73/0.99      ( v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) = iProver_top
% 2.73/0.99      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.73/0.99      inference(superposition,[status(thm)],[c_3773,c_4491]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_5080,plain,
% 2.73/0.99      ( v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(sK3)) = iProver_top
% 2.73/0.99      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.73/0.99      inference(light_normalisation,[status(thm)],[c_5079,c_4914]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_17,plain,
% 2.73/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.73/0.99      | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
% 2.73/0.99      | ~ v2_pre_topc(X1)
% 2.73/0.99      | v2_struct_0(X1)
% 2.73/0.99      | ~ l1_pre_topc(X1) ),
% 2.73/0.99      inference(cnf_transformation,[],[f81]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1788,plain,
% 2.73/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.73/0.99      | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
% 2.73/0.99      | v2_struct_0(X1)
% 2.73/0.99      | ~ l1_pre_topc(X1)
% 2.73/0.99      | sK3 != X1 ),
% 2.73/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_45]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1789,plain,
% 2.73/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.73/0.99      | m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))))
% 2.73/0.99      | v2_struct_0(sK3)
% 2.73/0.99      | ~ l1_pre_topc(sK3) ),
% 2.73/0.99      inference(unflattening,[status(thm)],[c_1788]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1793,plain,
% 2.73/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.73/0.99      | m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0))))) ),
% 2.73/0.99      inference(global_propositional_subsumption,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_1789,c_46,c_44]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_3759,plain,
% 2.73/0.99      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.73/0.99      | m1_subset_1(k7_tmap_1(sK3,X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0_56))))) ),
% 2.73/0.99      inference(subtyping,[status(esa)],[c_1793]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_4496,plain,
% 2.73/0.99      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.73/0.99      | m1_subset_1(k7_tmap_1(sK3,X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0_56))))) = iProver_top ),
% 2.73/0.99      inference(predicate_to_equality,[status(thm)],[c_3759]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_5085,plain,
% 2.73/0.99      ( m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) = iProver_top
% 2.73/0.99      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.73/0.99      inference(superposition,[status(thm)],[c_3773,c_4496]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_5086,plain,
% 2.73/0.99      ( m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) = iProver_top
% 2.73/0.99      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.73/0.99      inference(light_normalisation,[status(thm)],[c_5085,c_4914]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_5346,plain,
% 2.73/0.99      ( ~ m1_subset_1(sK2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.73/0.99      | m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4)))))) ),
% 2.73/0.99      inference(instantiation,[status(thm)],[c_3759]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_5606,plain,
% 2.73/0.99      ( k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4)
% 2.73/0.99      | k7_tmap_1(sK3,sK2(sK3,sK4)) != k9_tmap_1(sK3,sK4) ),
% 2.73/0.99      inference(global_propositional_subsumption,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_4504,c_47,c_44,c_49,c_155,c_159,c_1208,c_1279,c_3765,
% 2.73/0.99                 c_3751,c_4918,c_5080,c_5086,c_5346]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_14,plain,
% 2.73/0.99      ( v1_tsep_1(X0,X1)
% 2.73/0.99      | ~ m1_pre_topc(X0,X1)
% 2.73/0.99      | ~ l1_pre_topc(X1)
% 2.73/0.99      | sK2(X1,X0) = u1_struct_0(X0) ),
% 2.73/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1292,plain,
% 2.73/0.99      ( v1_tsep_1(X0,X1)
% 2.73/0.99      | ~ l1_pre_topc(X1)
% 2.73/0.99      | sK2(X1,X0) = u1_struct_0(X0)
% 2.73/0.99      | sK4 != X0
% 2.73/0.99      | sK3 != X1 ),
% 2.73/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_278]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1293,plain,
% 2.73/0.99      ( v1_tsep_1(sK4,sK3)
% 2.73/0.99      | ~ l1_pre_topc(sK3)
% 2.73/0.99      | sK2(sK3,sK4) = u1_struct_0(sK4) ),
% 2.73/0.99      inference(unflattening,[status(thm)],[c_1292]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1295,plain,
% 2.73/0.99      ( v1_tsep_1(sK4,sK3) | sK2(sK3,sK4) = u1_struct_0(sK4) ),
% 2.73/0.99      inference(global_propositional_subsumption,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_1293,c_44]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_3768,plain,
% 2.73/0.99      ( v1_tsep_1(sK4,sK3) | sK2(sK3,sK4) = u1_struct_0(sK4) ),
% 2.73/0.99      inference(subtyping,[status(esa)],[c_1295]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_4487,plain,
% 2.73/0.99      ( sK2(sK3,sK4) = u1_struct_0(sK4)
% 2.73/0.99      | v1_tsep_1(sK4,sK3) = iProver_top ),
% 2.73/0.99      inference(predicate_to_equality,[status(thm)],[c_3768]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_5134,plain,
% 2.73/0.99      ( sK2(sK3,sK4) = u1_struct_0(sK4) ),
% 2.73/0.99      inference(global_propositional_subsumption,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_4487,c_47,c_49,c_155,c_159,c_1208,c_3768,c_3765,
% 2.73/0.99                 c_4918,c_5080,c_5086]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_5608,plain,
% 2.73/0.99      ( k8_tmap_1(sK3,sK4) != k8_tmap_1(sK3,sK4)
% 2.73/0.99      | k7_tmap_1(sK3,u1_struct_0(sK4)) != k9_tmap_1(sK3,sK4) ),
% 2.73/0.99      inference(light_normalisation,[status(thm)],[c_5606,c_3773,c_5134]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_5609,plain,
% 2.73/0.99      ( k7_tmap_1(sK3,u1_struct_0(sK4)) != k9_tmap_1(sK3,sK4) ),
% 2.73/0.99      inference(equality_resolution_simp,[status(thm)],[c_5608]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(contradiction,plain,
% 2.73/0.99      ( $false ),
% 2.73/0.99      inference(minisat,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_5609,c_5086,c_5080,c_4918,c_1208,c_159,c_155,c_49,
% 2.73/0.99                 c_47]) ).
% 2.73/0.99  
% 2.73/0.99  
% 2.73/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.73/0.99  
% 2.73/0.99  ------                               Statistics
% 2.73/0.99  
% 2.73/0.99  ------ General
% 2.73/0.99  
% 2.73/0.99  abstr_ref_over_cycles:                  0
% 2.73/0.99  abstr_ref_under_cycles:                 0
% 2.73/0.99  gc_basic_clause_elim:                   0
% 2.73/0.99  forced_gc_time:                         0
% 2.73/0.99  parsing_time:                           0.011
% 2.73/0.99  unif_index_cands_time:                  0.
% 2.73/0.99  unif_index_add_time:                    0.
% 2.73/0.99  orderings_time:                         0.
% 2.73/0.99  out_proof_time:                         0.016
% 2.73/0.99  total_time:                             0.182
% 2.73/0.99  num_of_symbols:                         66
% 2.73/0.99  num_of_terms:                           4206
% 2.73/0.99  
% 2.73/0.99  ------ Preprocessing
% 2.73/0.99  
% 2.73/0.99  num_of_splits:                          0
% 2.73/0.99  num_of_split_atoms:                     0
% 2.73/0.99  num_of_reused_defs:                     0
% 2.73/0.99  num_eq_ax_congr_red:                    18
% 2.73/0.99  num_of_sem_filtered_clauses:            7
% 2.73/0.99  num_of_subtypes:                        4
% 2.73/0.99  monotx_restored_types:                  0
% 2.73/0.99  sat_num_of_epr_types:                   0
% 2.73/0.99  sat_num_of_non_cyclic_types:            0
% 2.73/0.99  sat_guarded_non_collapsed_types:        1
% 2.73/0.99  num_pure_diseq_elim:                    0
% 2.73/0.99  simp_replaced_by:                       0
% 2.73/0.99  res_preprocessed:                       164
% 2.73/0.99  prep_upred:                             0
% 2.73/0.99  prep_unflattend:                        130
% 2.73/0.99  smt_new_axioms:                         0
% 2.73/0.99  pred_elim_cands:                        6
% 2.73/0.99  pred_elim:                              8
% 2.73/0.99  pred_elim_cl:                           13
% 2.73/0.99  pred_elim_cycles:                       20
% 2.73/0.99  merged_defs:                            6
% 2.73/0.99  merged_defs_ncl:                        0
% 2.73/0.99  bin_hyper_res:                          8
% 2.73/0.99  prep_cycles:                            4
% 2.73/0.99  pred_elim_time:                         0.076
% 2.73/0.99  splitting_time:                         0.
% 2.73/0.99  sem_filter_time:                        0.
% 2.73/0.99  monotx_time:                            0.
% 2.73/0.99  subtype_inf_time:                       0.
% 2.73/0.99  
% 2.73/0.99  ------ Problem properties
% 2.73/0.99  
% 2.73/0.99  clauses:                                27
% 2.73/0.99  conjectures:                            1
% 2.73/0.99  epr:                                    1
% 2.73/0.99  horn:                                   16
% 2.73/0.99  ground:                                 14
% 2.73/0.99  unary:                                  7
% 2.73/0.99  binary:                                 10
% 2.73/0.99  lits:                                   71
% 2.73/0.99  lits_eq:                                15
% 2.73/0.99  fd_pure:                                0
% 2.73/0.99  fd_pseudo:                              0
% 2.73/0.99  fd_cond:                                3
% 2.73/0.99  fd_pseudo_cond:                         0
% 2.73/0.99  ac_symbols:                             0
% 2.73/0.99  
% 2.73/0.99  ------ Propositional Solver
% 2.73/0.99  
% 2.73/0.99  prop_solver_calls:                      27
% 2.73/0.99  prop_fast_solver_calls:                 2052
% 2.73/0.99  smt_solver_calls:                       0
% 2.73/0.99  smt_fast_solver_calls:                  0
% 2.73/0.99  prop_num_of_clauses:                    1136
% 2.73/0.99  prop_preprocess_simplified:             5099
% 2.73/0.99  prop_fo_subsumed:                       111
% 2.73/0.99  prop_solver_time:                       0.
% 2.73/0.99  smt_solver_time:                        0.
% 2.73/0.99  smt_fast_solver_time:                   0.
% 2.73/0.99  prop_fast_solver_time:                  0.
% 2.73/0.99  prop_unsat_core_time:                   0.
% 2.73/0.99  
% 2.73/0.99  ------ QBF
% 2.73/0.99  
% 2.73/0.99  qbf_q_res:                              0
% 2.73/0.99  qbf_num_tautologies:                    0
% 2.73/0.99  qbf_prep_cycles:                        0
% 2.73/0.99  
% 2.73/0.99  ------ BMC1
% 2.73/0.99  
% 2.73/0.99  bmc1_current_bound:                     -1
% 2.73/0.99  bmc1_last_solved_bound:                 -1
% 2.73/0.99  bmc1_unsat_core_size:                   -1
% 2.73/0.99  bmc1_unsat_core_parents_size:           -1
% 2.73/0.99  bmc1_merge_next_fun:                    0
% 2.73/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.73/0.99  
% 2.73/0.99  ------ Instantiation
% 2.73/0.99  
% 2.73/0.99  inst_num_of_clauses:                    209
% 2.73/0.99  inst_num_in_passive:                    47
% 2.73/0.99  inst_num_in_active:                     139
% 2.73/0.99  inst_num_in_unprocessed:                23
% 2.73/0.99  inst_num_of_loops:                      150
% 2.73/0.99  inst_num_of_learning_restarts:          0
% 2.73/0.99  inst_num_moves_active_passive:          8
% 2.73/0.99  inst_lit_activity:                      0
% 2.73/0.99  inst_lit_activity_moves:                0
% 2.73/0.99  inst_num_tautologies:                   0
% 2.73/0.99  inst_num_prop_implied:                  0
% 2.73/0.99  inst_num_existing_simplified:           0
% 2.73/0.99  inst_num_eq_res_simplified:             0
% 2.73/0.99  inst_num_child_elim:                    0
% 2.73/0.99  inst_num_of_dismatching_blockings:      33
% 2.73/0.99  inst_num_of_non_proper_insts:           151
% 2.73/0.99  inst_num_of_duplicates:                 0
% 2.73/0.99  inst_inst_num_from_inst_to_res:         0
% 2.73/0.99  inst_dismatching_checking_time:         0.
% 2.73/0.99  
% 2.73/0.99  ------ Resolution
% 2.73/0.99  
% 2.73/0.99  res_num_of_clauses:                     0
% 2.73/0.99  res_num_in_passive:                     0
% 2.73/0.99  res_num_in_active:                      0
% 2.73/0.99  res_num_of_loops:                       168
% 2.73/0.99  res_forward_subset_subsumed:            34
% 2.73/0.99  res_backward_subset_subsumed:           1
% 2.73/0.99  res_forward_subsumed:                   2
% 2.73/0.99  res_backward_subsumed:                  3
% 2.73/0.99  res_forward_subsumption_resolution:     14
% 2.73/0.99  res_backward_subsumption_resolution:    6
% 2.73/0.99  res_clause_to_clause_subsumption:       349
% 2.73/0.99  res_orphan_elimination:                 0
% 2.73/0.99  res_tautology_del:                      70
% 2.73/0.99  res_num_eq_res_simplified:              0
% 2.73/0.99  res_num_sel_changes:                    0
% 2.73/0.99  res_moves_from_active_to_pass:          0
% 2.73/0.99  
% 2.73/0.99  ------ Superposition
% 2.73/0.99  
% 2.73/0.99  sup_time_total:                         0.
% 2.73/0.99  sup_time_generating:                    0.
% 2.73/0.99  sup_time_sim_full:                      0.
% 2.73/0.99  sup_time_sim_immed:                     0.
% 2.73/0.99  
% 2.73/0.99  sup_num_of_clauses:                     34
% 2.73/0.99  sup_num_in_active:                      23
% 2.73/0.99  sup_num_in_passive:                     11
% 2.73/0.99  sup_num_of_loops:                       29
% 2.73/0.99  sup_fw_superposition:                   8
% 2.73/0.99  sup_bw_superposition:                   5
% 2.73/0.99  sup_immediate_simplified:               6
% 2.73/0.99  sup_given_eliminated:                   0
% 2.73/0.99  comparisons_done:                       0
% 2.73/0.99  comparisons_avoided:                    0
% 2.73/0.99  
% 2.73/0.99  ------ Simplifications
% 2.73/0.99  
% 2.73/0.99  
% 2.73/0.99  sim_fw_subset_subsumed:                 2
% 2.73/0.99  sim_bw_subset_subsumed:                 1
% 2.73/0.99  sim_fw_subsumed:                        0
% 2.73/0.99  sim_bw_subsumed:                        0
% 2.73/0.99  sim_fw_subsumption_res:                 1
% 2.73/0.99  sim_bw_subsumption_res:                 0
% 2.73/0.99  sim_tautology_del:                      1
% 2.73/0.99  sim_eq_tautology_del:                   2
% 2.73/0.99  sim_eq_res_simp:                        1
% 2.73/0.99  sim_fw_demodulated:                     0
% 2.73/0.99  sim_bw_demodulated:                     6
% 2.73/0.99  sim_light_normalised:                   9
% 2.73/0.99  sim_joinable_taut:                      0
% 2.73/0.99  sim_joinable_simp:                      0
% 2.73/0.99  sim_ac_normalised:                      0
% 2.73/0.99  sim_smt_subsumption:                    0
% 2.73/0.99  
%------------------------------------------------------------------------------
