%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:14 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.04s
% Verified   : 
% Statistics : Number of formulae       :  309 (4047 expanded)
%              Number of clauses        :  215 ( 862 expanded)
%              Number of leaves         :   26 ( 950 expanded)
%              Depth                    :   27
%              Number of atoms          : 1634 (46276 expanded)
%              Number of equality atoms :  398 (1171 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f13,conjecture,(
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

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f54,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f55,plain,(
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
    inference(flattening,[],[f54])).

fof(f57,plain,(
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

fof(f56,plain,
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

fof(f58,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f55,f57,f56])).

fof(f92,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f93,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f94,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f58])).

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

fof(f18,plain,(
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

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f19])).

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
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f103,plain,
    ( m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f95,plain,(
    m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k9_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f91,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
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

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f45,plain,(
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
    inference(rectify,[],[f44])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2)))
        & u1_struct_0(X1) = sK1(X0,X1,X2)
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f45,f46])).

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
    inference(cnf_transformation,[],[f47])).

fof(f108,plain,(
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

fof(f109,plain,(
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
    inference(equality_resolution,[],[f108])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f59,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
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

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k6_tmap_1(X0,X3) != X2
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k6_tmap_1(X0,sK0(X0,X1,X2)) != X2
        & u1_struct_0(X1) = sK0(X0,X1,X2)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f42])).

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
    inference(cnf_transformation,[],[f43])).

fof(f106,plain,(
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

fof(f107,plain,(
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
    inference(equality_resolution,[],[f106])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f65,plain,(
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
    inference(cnf_transformation,[],[f43])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f77,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f66,plain,(
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
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f84,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f11,axiom,(
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

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f53,plain,(
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
    inference(flattening,[],[f52])).

fof(f90,plain,(
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
    inference(cnf_transformation,[],[f53])).

fof(f100,plain,
    ( v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4))
    | v1_tsep_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f6,axiom,(
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

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f49,plain,(
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
    inference(rectify,[],[f48])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK2(X0,X1),X0)
        & u1_struct_0(X1) = sK2(X0,X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f49,f50])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(sK2(X0,X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f88,plain,(
    ! [X0,X1] :
      ( v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f104,plain,
    ( ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4))
    | ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
    | ~ m1_pre_topc(sK4,sK3)
    | ~ v1_tsep_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( v3_pre_topc(X3,X0)
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f110,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f71])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | u1_struct_0(X1) = sK2(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_3070,plain,
    ( X0_57 != X1_57
    | X2_57 != X1_57
    | X2_57 = X0_57 ),
    theory(equality)).

cnf(c_3971,plain,
    ( X0_57 != X1_57
    | X0_57 = k9_tmap_1(sK3,sK4)
    | k9_tmap_1(sK3,sK4) != X1_57 ),
    inference(instantiation,[status(thm)],[c_3070])).

cnf(c_5938,plain,
    ( X0_57 != k7_tmap_1(sK3,u1_struct_0(sK4))
    | X0_57 = k9_tmap_1(sK3,sK4)
    | k9_tmap_1(sK3,sK4) != k7_tmap_1(sK3,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3971])).

cnf(c_6890,plain,
    ( k7_tmap_1(X0_56,sK2(sK3,sK4)) != k7_tmap_1(sK3,u1_struct_0(sK4))
    | k7_tmap_1(X0_56,sK2(sK3,sK4)) = k9_tmap_1(sK3,sK4)
    | k9_tmap_1(sK3,sK4) != k7_tmap_1(sK3,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_5938])).

cnf(c_6891,plain,
    ( k7_tmap_1(sK3,sK2(sK3,sK4)) != k7_tmap_1(sK3,u1_struct_0(sK4))
    | k7_tmap_1(sK3,sK2(sK3,sK4)) = k9_tmap_1(sK3,sK4)
    | k9_tmap_1(sK3,sK4) != k7_tmap_1(sK3,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_6890])).

cnf(c_3069,plain,
    ( X0_56 != X1_56
    | X2_56 != X1_56
    | X2_56 = X0_56 ),
    theory(equality)).

cnf(c_4375,plain,
    ( X0_56 != X1_56
    | X0_56 = k8_tmap_1(sK3,sK4)
    | k8_tmap_1(sK3,sK4) != X1_56 ),
    inference(instantiation,[status(thm)],[c_3069])).

cnf(c_4912,plain,
    ( X0_56 != k6_tmap_1(sK3,u1_struct_0(sK4))
    | X0_56 = k8_tmap_1(sK3,sK4)
    | k8_tmap_1(sK3,sK4) != k6_tmap_1(sK3,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_4375])).

cnf(c_6579,plain,
    ( k6_tmap_1(X0_56,sK2(sK3,sK4)) != k6_tmap_1(sK3,u1_struct_0(sK4))
    | k6_tmap_1(X0_56,sK2(sK3,sK4)) = k8_tmap_1(sK3,sK4)
    | k8_tmap_1(sK3,sK4) != k6_tmap_1(sK3,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_4912])).

cnf(c_6581,plain,
    ( k6_tmap_1(sK3,sK2(sK3,sK4)) != k6_tmap_1(sK3,u1_struct_0(sK4))
    | k6_tmap_1(sK3,sK2(sK3,sK4)) = k8_tmap_1(sK3,sK4)
    | k8_tmap_1(sK3,sK4) != k6_tmap_1(sK3,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_6579])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_45,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1846,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_45])).

cnf(c_1847,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1846])).

cnf(c_44,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_43,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1851,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1847,c_44,c_43])).

cnf(c_3045,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k7_tmap_1(sK3,X0_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0_57))))) ),
    inference(subtyping,[status(esa)],[c_1851])).

cnf(c_6121,plain,
    ( ~ m1_subset_1(sK2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4)))))) ),
    inference(instantiation,[status(thm)],[c_3045])).

cnf(c_3082,plain,
    ( X0_57 != X1_57
    | X0_56 != X1_56
    | k6_tmap_1(X0_56,X0_57) = k6_tmap_1(X1_56,X1_57) ),
    theory(equality)).

cnf(c_4335,plain,
    ( X0_57 != u1_struct_0(sK4)
    | X0_56 != sK3
    | k6_tmap_1(X0_56,X0_57) = k6_tmap_1(sK3,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3082])).

cnf(c_6098,plain,
    ( sK2(sK3,sK4) != u1_struct_0(sK4)
    | X0_56 != sK3
    | k6_tmap_1(X0_56,sK2(sK3,sK4)) = k6_tmap_1(sK3,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_4335])).

cnf(c_6107,plain,
    ( sK2(sK3,sK4) != u1_struct_0(sK4)
    | k6_tmap_1(sK3,sK2(sK3,sK4)) = k6_tmap_1(sK3,u1_struct_0(sK4))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_6098])).

cnf(c_3086,plain,
    ( X0_57 != X1_57
    | k7_tmap_1(X0_56,X0_57) = k7_tmap_1(X1_56,X1_57)
    | X0_56 != X1_56 ),
    theory(equality)).

cnf(c_4134,plain,
    ( X0_57 != u1_struct_0(sK4)
    | k7_tmap_1(X0_56,X0_57) = k7_tmap_1(sK3,u1_struct_0(sK4))
    | X0_56 != sK3 ),
    inference(instantiation,[status(thm)],[c_3086])).

cnf(c_6100,plain,
    ( sK2(sK3,sK4) != u1_struct_0(sK4)
    | k7_tmap_1(X0_56,sK2(sK3,sK4)) = k7_tmap_1(sK3,u1_struct_0(sK4))
    | X0_56 != sK3 ),
    inference(instantiation,[status(thm)],[c_4134])).

cnf(c_6106,plain,
    ( sK2(sK3,sK4) != u1_struct_0(sK4)
    | k7_tmap_1(sK3,sK2(sK3,sK4)) = k7_tmap_1(sK3,u1_struct_0(sK4))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_6100])).

cnf(c_4071,plain,
    ( X0_57 != X1_57
    | k9_tmap_1(sK3,sK4) != X1_57
    | k9_tmap_1(sK3,sK4) = X0_57 ),
    inference(instantiation,[status(thm)],[c_3070])).

cnf(c_4299,plain,
    ( X0_57 != k9_tmap_1(sK3,sK4)
    | k9_tmap_1(sK3,sK4) = X0_57
    | k9_tmap_1(sK3,sK4) != k9_tmap_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_4071])).

cnf(c_6059,plain,
    ( k7_tmap_1(sK3,u1_struct_0(sK4)) != k9_tmap_1(sK3,sK4)
    | k9_tmap_1(sK3,sK4) = k7_tmap_1(sK3,u1_struct_0(sK4))
    | k9_tmap_1(sK3,sK4) != k9_tmap_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_4299])).

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
    inference(cnf_transformation,[],[f61])).

cnf(c_22,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(k9_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X0)))))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_34,negated_conjecture,
    ( m1_pre_topc(sK4,sK3)
    | m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_42,negated_conjecture,
    ( m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_274,negated_conjecture,
    ( m1_pre_topc(sK4,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_34,c_42])).

cnf(c_1260,plain,
    ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_274])).

cnf(c_1261,plain,
    ( m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1260])).

cnf(c_1263,plain,
    ( m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1261,c_45,c_44,c_43])).

cnf(c_24,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k9_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1247,plain,
    ( ~ v2_pre_topc(X0)
    | v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_274])).

cnf(c_1248,plain,
    ( ~ v2_pre_topc(sK3)
    | v1_funct_1(k9_tmap_1(sK3,sK4))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1247])).

cnf(c_1250,plain,
    ( v1_funct_1(k9_tmap_1(sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1248,c_45,c_44,c_43])).

cnf(c_32,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1234,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK4 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_274])).

cnf(c_1235,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1234])).

cnf(c_1237,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1235,c_43])).

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
    inference(cnf_transformation,[],[f109])).

cnf(c_23,plain,
    ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_329,plain,
    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_23])).

cnf(c_1128,plain,
    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
    | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_329,c_274])).

cnf(c_1129,plain,
    ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1128])).

cnf(c_1131,plain,
    ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1129,c_45,c_44,c_43])).

cnf(c_1132,plain,
    ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4)) ),
    inference(renaming,[status(thm)],[c_1131])).

cnf(c_1244,plain,
    ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1237,c_1132])).

cnf(c_1257,plain,
    ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1250,c_1244])).

cnf(c_1270,plain,
    ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1263,c_1257])).

cnf(c_2188,plain,
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
    inference(resolution_lifted,[status(thm)],[c_3,c_1270])).

cnf(c_2189,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
    | ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4)))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4)))
    | k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_2188])).

cnf(c_1148,plain,
    ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_274])).

cnf(c_1149,plain,
    ( v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1148])).

cnf(c_2191,plain,
    ( ~ v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4)))
    | ~ v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
    | ~ m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4)))
    | k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2189,c_45,c_44,c_43,c_1149,c_1248,c_1261])).

cnf(c_2192,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
    | ~ m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))))
    | ~ v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4)))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4)))
    | k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4) ),
    inference(renaming,[status(thm)],[c_2191])).

cnf(c_3037,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
    | ~ m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))))
    | ~ v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4)))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4)))
    | k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4) ),
    inference(subtyping,[status(esa)],[c_2192])).

cnf(c_3646,plain,
    ( k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4)
    | v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))) = iProver_top
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3037])).

cnf(c_46,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_48,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_1,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_152,plain,
    ( v2_struct_0(X0) = iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_154,plain,
    ( v2_struct_0(sK3) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top
    | l1_struct_0(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_152])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_155,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_157,plain,
    ( l1_pre_topc(sK3) != iProver_top
    | l1_struct_0(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_155])).

cnf(c_1236,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1235])).

cnf(c_3073,plain,
    ( u1_struct_0(X0_56) = u1_struct_0(X1_56)
    | X0_56 != X1_56 ),
    theory(equality)).

cnf(c_3092,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_3073])).

cnf(c_3065,plain,
    ( X0_56 = X0_56 ),
    theory(equality)).

cnf(c_3111,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_3065])).

cnf(c_3168,plain,
    ( k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4)
    | v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))) = iProver_top
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3037])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k7_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1828,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k7_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_45])).

cnf(c_1829,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | v1_funct_1(k7_tmap_1(sK3,X0))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1828])).

cnf(c_1833,plain,
    ( v1_funct_1(k7_tmap_1(sK3,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1829,c_44,c_43])).

cnf(c_1834,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_funct_1(k7_tmap_1(sK3,X0)) ),
    inference(renaming,[status(thm)],[c_1833])).

cnf(c_3046,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_funct_1(k7_tmap_1(sK3,X0_57)) ),
    inference(subtyping,[status(esa)],[c_1834])).

cnf(c_3864,plain,
    ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_3046])).

cnf(c_3865,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3864])).

cnf(c_3870,plain,
    ( m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_3045])).

cnf(c_3871,plain,
    ( m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))))) = iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3870])).

cnf(c_20,plain,
    ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1774,plain,
    ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_45])).

cnf(c_1775,plain,
    ( v1_funct_2(k7_tmap_1(sK3,X0),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1774])).

cnf(c_1779,plain,
    ( v1_funct_2(k7_tmap_1(sK3,X0),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1775,c_44,c_43])).

cnf(c_3049,plain,
    ( v1_funct_2(k7_tmap_1(sK3,X0_57),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0_57)))
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subtyping,[status(esa)],[c_1779])).

cnf(c_3873,plain,
    ( v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_3049])).

cnf(c_3874,plain,
    ( v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))) = iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3873])).

cnf(c_3074,plain,
    ( ~ v1_xboole_0(X0_57)
    | v1_xboole_0(X1_57)
    | X1_57 != X0_57 ),
    theory(equality)).

cnf(c_4014,plain,
    ( v1_xboole_0(X0_57)
    | ~ v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4)))
    | X0_57 != u1_struct_0(k8_tmap_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_3074])).

cnf(c_4165,plain,
    ( v1_xboole_0(u1_struct_0(X0_56))
    | ~ v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4)))
    | u1_struct_0(X0_56) != u1_struct_0(k8_tmap_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_4014])).

cnf(c_4167,plain,
    ( u1_struct_0(X0_56) != u1_struct_0(k8_tmap_1(sK3,sK4))
    | v1_xboole_0(u1_struct_0(X0_56)) = iProver_top
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4165])).

cnf(c_4169,plain,
    ( u1_struct_0(sK3) != u1_struct_0(k8_tmap_1(sK3,sK4))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4167])).

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
    inference(cnf_transformation,[],[f107])).

cnf(c_339,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(k8_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(k8_tmap_1(X1,X0))
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7,c_32])).

cnf(c_1200,plain,
    ( ~ v1_pre_topc(k8_tmap_1(X0,X1))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(k8_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(k8_tmap_1(X0,X1))
    | k6_tmap_1(X0,u1_struct_0(X1)) = k8_tmap_1(X0,X1)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_339,c_274])).

cnf(c_1201,plain,
    ( ~ v1_pre_topc(k8_tmap_1(sK3,sK4))
    | ~ v2_pre_topc(k8_tmap_1(sK3,sK4))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(k8_tmap_1(sK3,sK4))
    | ~ l1_pre_topc(sK3)
    | k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_1200])).

cnf(c_1203,plain,
    ( ~ l1_pre_topc(k8_tmap_1(sK3,sK4))
    | ~ v2_pre_topc(k8_tmap_1(sK3,sK4))
    | ~ v1_pre_topc(k8_tmap_1(sK3,sK4))
    | k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1201,c_45,c_44,c_43])).

cnf(c_1204,plain,
    ( ~ v1_pre_topc(k8_tmap_1(sK3,sK4))
    | ~ v2_pre_topc(k8_tmap_1(sK3,sK4))
    | ~ l1_pre_topc(k8_tmap_1(sK3,sK4))
    | k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4) ),
    inference(renaming,[status(thm)],[c_1203])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_pre_topc(k6_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1864,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_pre_topc(k6_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_45])).

cnf(c_1865,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_pre_topc(k6_tmap_1(sK3,X0))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1864])).

cnf(c_1869,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_pre_topc(k6_tmap_1(sK3,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1865,c_44,c_43])).

cnf(c_2007,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(k8_tmap_1(sK3,sK4))
    | ~ l1_pre_topc(k8_tmap_1(sK3,sK4))
    | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
    | k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4) ),
    inference(resolution_lifted,[status(thm)],[c_1204,c_1869])).

cnf(c_3039,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(k8_tmap_1(sK3,sK4))
    | ~ l1_pre_topc(k8_tmap_1(sK3,sK4))
    | k6_tmap_1(sK3,X0_57) != k8_tmap_1(sK3,sK4)
    | k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4) ),
    inference(subtyping,[status(esa)],[c_2007])).

cnf(c_3063,plain,
    ( ~ v2_pre_topc(k8_tmap_1(sK3,sK4))
    | ~ l1_pre_topc(k8_tmap_1(sK3,sK4))
    | sP0_iProver_split
    | k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_3039])).

cnf(c_3643,plain,
    ( k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4)
    | v2_pre_topc(k8_tmap_1(sK3,sK4)) != iProver_top
    | l1_pre_topc(k8_tmap_1(sK3,sK4)) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3063])).

cnf(c_3058,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subtyping,[status(esa)],[c_1237])).

cnf(c_3624,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3058])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | sK0(X1,X0,X2) = u1_struct_0(X0)
    | k8_tmap_1(X1,X0) = X2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1328,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | sK0(X1,X2,X0) = u1_struct_0(X2)
    | k8_tmap_1(X1,X2) = X0
    | sK4 != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_274])).

cnf(c_1329,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3)
    | sK0(sK3,sK4,X0) = u1_struct_0(sK4)
    | k8_tmap_1(sK3,sK4) = X0 ),
    inference(unflattening,[status(thm)],[c_1328])).

cnf(c_1333,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | sK0(sK3,sK4,X0) = u1_struct_0(sK4)
    | k8_tmap_1(sK3,sK4) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1329,c_45,c_44,c_43])).

cnf(c_1334,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK0(sK3,sK4,X0) = u1_struct_0(sK4)
    | k8_tmap_1(sK3,sK4) = X0 ),
    inference(renaming,[status(thm)],[c_1333])).

cnf(c_1965,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK0(sK3,sK4,X1) = u1_struct_0(sK4)
    | k6_tmap_1(sK3,X0) != X1
    | k8_tmap_1(sK3,sK4) = X1 ),
    inference(resolution_lifted,[status(thm)],[c_1334,c_1869])).

cnf(c_1966,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(k6_tmap_1(sK3,X0))
    | ~ l1_pre_topc(k6_tmap_1(sK3,X0))
    | sK0(sK3,sK4,k6_tmap_1(sK3,X0)) = u1_struct_0(sK4)
    | k8_tmap_1(sK3,sK4) = k6_tmap_1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_1965])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k6_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1882,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k6_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_45])).

cnf(c_1883,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_pre_topc(k6_tmap_1(sK3,X0))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1882])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k6_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1900,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k6_tmap_1(X1,X0))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_45])).

cnf(c_1901,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | l1_pre_topc(k6_tmap_1(sK3,X0))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1900])).

cnf(c_1970,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | sK0(sK3,sK4,k6_tmap_1(sK3,X0)) = u1_struct_0(sK4)
    | k8_tmap_1(sK3,sK4) = k6_tmap_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1966,c_44,c_43,c_1883,c_1901])).

cnf(c_3041,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK3)))
    | sK0(sK3,sK4,k6_tmap_1(sK3,X0_57)) = u1_struct_0(sK4)
    | k8_tmap_1(sK3,sK4) = k6_tmap_1(sK3,X0_57) ),
    inference(subtyping,[status(esa)],[c_1970])).

cnf(c_3641,plain,
    ( sK0(sK3,sK4,k6_tmap_1(sK3,X0_57)) = u1_struct_0(sK4)
    | k8_tmap_1(sK3,sK4) = k6_tmap_1(sK3,X0_57)
    | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3041])).

cnf(c_4857,plain,
    ( sK0(sK3,sK4,k6_tmap_1(sK3,u1_struct_0(sK4))) = u1_struct_0(sK4)
    | k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_3624,c_3641])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k6_tmap_1(X1,sK0(X1,X0,X2)) != X2
    | k8_tmap_1(X1,X0) = X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1355,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(X1,sK0(X1,X2,X0)) != X0
    | k8_tmap_1(X1,X2) = X0
    | sK4 != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_274])).

cnf(c_1356,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3)
    | k6_tmap_1(sK3,sK0(sK3,sK4,X0)) != X0
    | k8_tmap_1(sK3,sK4) = X0 ),
    inference(unflattening,[status(thm)],[c_1355])).

cnf(c_1360,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | k6_tmap_1(sK3,sK0(sK3,sK4,X0)) != X0
    | k8_tmap_1(sK3,sK4) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1356,c_45,c_44,c_43])).

cnf(c_1361,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k6_tmap_1(sK3,sK0(sK3,sK4,X0)) != X0
    | k8_tmap_1(sK3,sK4) = X0 ),
    inference(renaming,[status(thm)],[c_1360])).

cnf(c_1944,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(sK3,X0) != X1
    | k6_tmap_1(sK3,sK0(sK3,sK4,X1)) != X1
    | k8_tmap_1(sK3,sK4) = X1 ),
    inference(resolution_lifted,[status(thm)],[c_1361,c_1869])).

cnf(c_1945,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(k6_tmap_1(sK3,X0))
    | ~ l1_pre_topc(k6_tmap_1(sK3,X0))
    | k6_tmap_1(sK3,sK0(sK3,sK4,k6_tmap_1(sK3,X0))) != k6_tmap_1(sK3,X0)
    | k8_tmap_1(sK3,sK4) = k6_tmap_1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_1944])).

cnf(c_1949,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k6_tmap_1(sK3,sK0(sK3,sK4,k6_tmap_1(sK3,X0))) != k6_tmap_1(sK3,X0)
    | k8_tmap_1(sK3,sK4) = k6_tmap_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1945,c_44,c_43,c_1883,c_1901])).

cnf(c_3042,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK3)))
    | k6_tmap_1(sK3,sK0(sK3,sK4,k6_tmap_1(sK3,X0_57))) != k6_tmap_1(sK3,X0_57)
    | k8_tmap_1(sK3,sK4) = k6_tmap_1(sK3,X0_57) ),
    inference(subtyping,[status(esa)],[c_1949])).

cnf(c_3640,plain,
    ( k6_tmap_1(sK3,sK0(sK3,sK4,k6_tmap_1(sK3,X0_57))) != k6_tmap_1(sK3,X0_57)
    | k8_tmap_1(sK3,sK4) = k6_tmap_1(sK3,X0_57)
    | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3042])).

cnf(c_4928,plain,
    ( k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4)
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4857,c_3640])).

cnf(c_5009,plain,
    ( k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3643,c_48,c_1236,c_4928])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1792,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_45])).

cnf(c_1793,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | u1_struct_0(k6_tmap_1(sK3,X0)) = u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_1792])).

cnf(c_1797,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | u1_struct_0(k6_tmap_1(sK3,X0)) = u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1793,c_44,c_43])).

cnf(c_3048,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK3)))
    | u1_struct_0(k6_tmap_1(sK3,X0_57)) = u1_struct_0(sK3) ),
    inference(subtyping,[status(esa)],[c_1797])).

cnf(c_3634,plain,
    ( u1_struct_0(k6_tmap_1(sK3,X0_57)) = u1_struct_0(sK3)
    | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3048])).

cnf(c_4096,plain,
    ( u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))) = u1_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_3624,c_3634])).

cnf(c_5014,plain,
    ( u1_struct_0(k8_tmap_1(sK3,sK4)) = u1_struct_0(sK3) ),
    inference(demodulation,[status(thm)],[c_5009,c_4096])).

cnf(c_4251,plain,
    ( X0_57 != X1_57
    | u1_struct_0(sK3) != X1_57
    | u1_struct_0(sK3) = X0_57 ),
    inference(instantiation,[status(thm)],[c_3070])).

cnf(c_4533,plain,
    ( X0_57 != u1_struct_0(sK3)
    | u1_struct_0(sK3) = X0_57
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_4251])).

cnf(c_4757,plain,
    ( u1_struct_0(X0_56) != u1_struct_0(sK3)
    | u1_struct_0(sK3) = u1_struct_0(X0_56)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_4533])).

cnf(c_5327,plain,
    ( u1_struct_0(k8_tmap_1(sK3,sK4)) != u1_struct_0(sK3)
    | u1_struct_0(sK3) = u1_struct_0(k8_tmap_1(sK3,sK4))
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_4757])).

cnf(c_5445,plain,
    ( v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))) = iProver_top
    | k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3646,c_46,c_48,c_154,c_157,c_1236,c_3092,c_3111,c_3168,c_3865,c_3871,c_3874,c_4169,c_5014,c_5327])).

cnf(c_5446,plain,
    ( k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4)
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))) = iProver_top ),
    inference(renaming,[status(thm)],[c_5445])).

cnf(c_5449,plain,
    ( k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4)
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5446,c_5009])).

cnf(c_4059,plain,
    ( X0_56 != X1_56
    | k8_tmap_1(sK3,sK4) != X1_56
    | k8_tmap_1(sK3,sK4) = X0_56 ),
    inference(instantiation,[status(thm)],[c_3069])).

cnf(c_4282,plain,
    ( X0_56 != k8_tmap_1(sK3,sK4)
    | k8_tmap_1(sK3,sK4) = X0_56
    | k8_tmap_1(sK3,sK4) != k8_tmap_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_4059])).

cnf(c_4590,plain,
    ( k6_tmap_1(sK3,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4)
    | k8_tmap_1(sK3,sK4) = k6_tmap_1(sK3,u1_struct_0(sK4))
    | k8_tmap_1(sK3,sK4) != k8_tmap_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_4282])).

cnf(c_4283,plain,
    ( k8_tmap_1(sK3,sK4) = k8_tmap_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_3065])).

cnf(c_3066,plain,
    ( X0_57 = X0_57 ),
    theory(equality)).

cnf(c_4020,plain,
    ( k9_tmap_1(sK3,sK4) = k9_tmap_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_3066])).

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
    inference(cnf_transformation,[],[f90])).

cnf(c_301,plain,
    ( ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
    | v3_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k7_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_27,c_20])).

cnf(c_37,negated_conjecture,
    ( v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4))
    | v1_tsep_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_593,plain,
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
    inference(resolution_lifted,[status(thm)],[c_301,c_37])).

cnf(c_594,plain,
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
    inference(unflattening,[status(thm)],[c_593])).

cnf(c_598,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_tsep_1(sK4,sK3)
    | v3_pre_topc(X0,sK3)
    | ~ v1_funct_1(k7_tmap_1(sK3,X0))
    | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4)
    | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_594,c_45,c_44,c_43])).

cnf(c_599,plain,
    ( v3_pre_topc(X0,sK3)
    | v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))))
    | ~ v1_funct_1(k7_tmap_1(sK3,X0))
    | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4)
    | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4) ),
    inference(renaming,[status(thm)],[c_598])).

cnf(c_12,plain,
    ( ~ v3_pre_topc(sK2(X0,X1),X0)
    | v1_tsep_1(X1,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1159,plain,
    ( ~ v3_pre_topc(sK2(X0,X1),X0)
    | v1_tsep_1(X1,X0)
    | ~ l1_pre_topc(X0)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_274])).

cnf(c_1160,plain,
    ( ~ v3_pre_topc(sK2(sK3,sK4),sK3)
    | v1_tsep_1(sK4,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1159])).

cnf(c_1162,plain,
    ( v1_tsep_1(sK4,sK3)
    | ~ v3_pre_topc(sK2(sK3,sK4),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1160,c_43])).

cnf(c_1163,plain,
    ( ~ v3_pre_topc(sK2(sK3,sK4),sK3)
    | v1_tsep_1(sK4,sK3) ),
    inference(renaming,[status(thm)],[c_1162])).

cnf(c_1512,plain,
    ( v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))))
    | ~ v1_funct_1(k7_tmap_1(sK3,X0))
    | sK2(sK3,sK4) != X0
    | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4)
    | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_599,c_1163])).

cnf(c_1513,plain,
    ( v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(sK2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4))))))
    | ~ v1_funct_1(k7_tmap_1(sK3,sK2(sK3,sK4)))
    | k7_tmap_1(sK3,sK2(sK3,sK4)) != k9_tmap_1(sK3,sK4)
    | k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_1512])).

cnf(c_14,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1273,plain,
    ( v1_tsep_1(X0,X1)
    | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK4 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_274])).

cnf(c_1274,plain,
    ( v1_tsep_1(sK4,sK3)
    | m1_subset_1(sK2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1273])).

cnf(c_1515,plain,
    ( v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4))))))
    | ~ v1_funct_1(k7_tmap_1(sK3,sK2(sK3,sK4)))
    | k7_tmap_1(sK3,sK2(sK3,sK4)) != k9_tmap_1(sK3,sK4)
    | k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1513,c_43,c_1274])).

cnf(c_2314,plain,
    ( v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4))))))
    | k7_tmap_1(sK3,sK2(sK3,sK4)) != k9_tmap_1(sK3,sK4)
    | k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4) ),
    inference(resolution_lifted,[status(thm)],[c_1250,c_1515])).

cnf(c_3036,plain,
    ( v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4))))))
    | k7_tmap_1(sK3,sK2(sK3,sK4)) != k9_tmap_1(sK3,sK4)
    | k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4) ),
    inference(subtyping,[status(esa)],[c_2314])).

cnf(c_1151,plain,
    ( v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1149,c_45,c_44,c_43])).

cnf(c_29,plain,
    ( v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
    | ~ v3_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_33,negated_conjecture,
    ( ~ v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4))
    | ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ v1_tsep_1(sK4,sK3)
    | ~ m1_pre_topc(sK4,sK3)
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4)) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_279,plain,
    ( ~ v1_tsep_1(sK4,sK3)
    | ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_33,c_42])).

cnf(c_280,negated_conjecture,
    ( ~ v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4))
    | ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4)) ),
    inference(renaming,[status(thm)],[c_279])).

cnf(c_557,plain,
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
    inference(resolution_lifted,[status(thm)],[c_29,c_280])).

cnf(c_558,plain,
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
    inference(unflattening,[status(thm)],[c_557])).

cnf(c_562,plain,
    ( ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_tsep_1(sK4,sK3)
    | ~ v3_pre_topc(X0,sK3)
    | ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
    | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4)
    | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_558,c_45,c_44,c_43])).

cnf(c_563,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ v3_pre_topc(X0,sK3)
    | ~ v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
    | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4)
    | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4) ),
    inference(renaming,[status(thm)],[c_562])).

cnf(c_1438,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
    | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4)
    | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1151,c_563])).

cnf(c_1463,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4)
    | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1250,c_1438])).

cnf(c_1469,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4)
    | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1263,c_1463])).

cnf(c_15,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_319,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_32])).

cnf(c_320,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_319])).

cnf(c_1220,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK4 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_320,c_274])).

cnf(c_1221,plain,
    ( v3_pre_topc(u1_struct_0(sK4),sK3)
    | ~ v1_tsep_1(sK4,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1220])).

cnf(c_1223,plain,
    ( ~ v1_tsep_1(sK4,sK3)
    | v3_pre_topc(u1_struct_0(sK4),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1221,c_43])).

cnf(c_1224,plain,
    ( v3_pre_topc(u1_struct_0(sK4),sK3)
    | ~ v1_tsep_1(sK4,sK3) ),
    inference(renaming,[status(thm)],[c_1223])).

cnf(c_1535,plain,
    ( ~ v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4)
    | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
    | u1_struct_0(sK4) != X0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_1469,c_1224])).

cnf(c_1536,plain,
    ( ~ v1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | k7_tmap_1(sK3,u1_struct_0(sK4)) != k9_tmap_1(sK3,sK4)
    | k6_tmap_1(sK3,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_1535])).

cnf(c_1538,plain,
    ( ~ v1_tsep_1(sK4,sK3)
    | k7_tmap_1(sK3,u1_struct_0(sK4)) != k9_tmap_1(sK3,sK4)
    | k6_tmap_1(sK3,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1536,c_43,c_1235])).

cnf(c_3051,plain,
    ( ~ v1_tsep_1(sK4,sK3)
    | k7_tmap_1(sK3,u1_struct_0(sK4)) != k9_tmap_1(sK3,sK4)
    | k6_tmap_1(sK3,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4) ),
    inference(subtyping,[status(esa)],[c_1538])).

cnf(c_13,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK2(X1,X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1287,plain,
    ( v1_tsep_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK2(X1,X0) = u1_struct_0(X0)
    | sK4 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_274])).

cnf(c_1288,plain,
    ( v1_tsep_1(sK4,sK3)
    | ~ l1_pre_topc(sK3)
    | sK2(sK3,sK4) = u1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1287])).

cnf(c_1290,plain,
    ( v1_tsep_1(sK4,sK3)
    | sK2(sK3,sK4) = u1_struct_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1288,c_43])).

cnf(c_3054,plain,
    ( v1_tsep_1(sK4,sK3)
    | sK2(sK3,sK4) = u1_struct_0(sK4) ),
    inference(subtyping,[status(esa)],[c_1290])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6891,c_6581,c_6121,c_6107,c_6106,c_6059,c_5449,c_5327,c_5014,c_4928,c_4590,c_4283,c_4169,c_4020,c_3036,c_3051,c_3054,c_3111,c_3092,c_1274,c_1236,c_157,c_154,c_48,c_43,c_46])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:14:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.04/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/0.99  
% 3.04/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.04/0.99  
% 3.04/0.99  ------  iProver source info
% 3.04/0.99  
% 3.04/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.04/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.04/0.99  git: non_committed_changes: false
% 3.04/0.99  git: last_make_outside_of_git: false
% 3.04/0.99  
% 3.04/0.99  ------ 
% 3.04/0.99  
% 3.04/0.99  ------ Input Options
% 3.04/0.99  
% 3.04/0.99  --out_options                           all
% 3.04/0.99  --tptp_safe_out                         true
% 3.04/0.99  --problem_path                          ""
% 3.04/0.99  --include_path                          ""
% 3.04/0.99  --clausifier                            res/vclausify_rel
% 3.04/0.99  --clausifier_options                    --mode clausify
% 3.04/0.99  --stdin                                 false
% 3.04/0.99  --stats_out                             all
% 3.04/0.99  
% 3.04/0.99  ------ General Options
% 3.04/0.99  
% 3.04/0.99  --fof                                   false
% 3.04/0.99  --time_out_real                         305.
% 3.04/0.99  --time_out_virtual                      -1.
% 3.04/0.99  --symbol_type_check                     false
% 3.04/0.99  --clausify_out                          false
% 3.04/0.99  --sig_cnt_out                           false
% 3.04/0.99  --trig_cnt_out                          false
% 3.04/0.99  --trig_cnt_out_tolerance                1.
% 3.04/0.99  --trig_cnt_out_sk_spl                   false
% 3.04/0.99  --abstr_cl_out                          false
% 3.04/0.99  
% 3.04/0.99  ------ Global Options
% 3.04/0.99  
% 3.04/0.99  --schedule                              default
% 3.04/0.99  --add_important_lit                     false
% 3.04/0.99  --prop_solver_per_cl                    1000
% 3.04/0.99  --min_unsat_core                        false
% 3.04/0.99  --soft_assumptions                      false
% 3.04/0.99  --soft_lemma_size                       3
% 3.04/0.99  --prop_impl_unit_size                   0
% 3.04/0.99  --prop_impl_unit                        []
% 3.04/0.99  --share_sel_clauses                     true
% 3.04/0.99  --reset_solvers                         false
% 3.04/0.99  --bc_imp_inh                            [conj_cone]
% 3.04/0.99  --conj_cone_tolerance                   3.
% 3.04/0.99  --extra_neg_conj                        none
% 3.04/0.99  --large_theory_mode                     true
% 3.04/0.99  --prolific_symb_bound                   200
% 3.04/0.99  --lt_threshold                          2000
% 3.04/0.99  --clause_weak_htbl                      true
% 3.04/0.99  --gc_record_bc_elim                     false
% 3.04/0.99  
% 3.04/0.99  ------ Preprocessing Options
% 3.04/0.99  
% 3.04/0.99  --preprocessing_flag                    true
% 3.04/0.99  --time_out_prep_mult                    0.1
% 3.04/0.99  --splitting_mode                        input
% 3.04/0.99  --splitting_grd                         true
% 3.04/0.99  --splitting_cvd                         false
% 3.04/0.99  --splitting_cvd_svl                     false
% 3.04/0.99  --splitting_nvd                         32
% 3.04/0.99  --sub_typing                            true
% 3.04/0.99  --prep_gs_sim                           true
% 3.04/0.99  --prep_unflatten                        true
% 3.04/0.99  --prep_res_sim                          true
% 3.04/0.99  --prep_upred                            true
% 3.04/0.99  --prep_sem_filter                       exhaustive
% 3.04/0.99  --prep_sem_filter_out                   false
% 3.04/0.99  --pred_elim                             true
% 3.04/0.99  --res_sim_input                         true
% 3.04/0.99  --eq_ax_congr_red                       true
% 3.04/0.99  --pure_diseq_elim                       true
% 3.04/0.99  --brand_transform                       false
% 3.04/0.99  --non_eq_to_eq                          false
% 3.04/0.99  --prep_def_merge                        true
% 3.04/0.99  --prep_def_merge_prop_impl              false
% 3.04/0.99  --prep_def_merge_mbd                    true
% 3.04/0.99  --prep_def_merge_tr_red                 false
% 3.04/0.99  --prep_def_merge_tr_cl                  false
% 3.04/0.99  --smt_preprocessing                     true
% 3.04/0.99  --smt_ac_axioms                         fast
% 3.04/0.99  --preprocessed_out                      false
% 3.04/0.99  --preprocessed_stats                    false
% 3.04/0.99  
% 3.04/0.99  ------ Abstraction refinement Options
% 3.04/0.99  
% 3.04/0.99  --abstr_ref                             []
% 3.04/0.99  --abstr_ref_prep                        false
% 3.04/0.99  --abstr_ref_until_sat                   false
% 3.04/0.99  --abstr_ref_sig_restrict                funpre
% 3.04/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.04/0.99  --abstr_ref_under                       []
% 3.04/0.99  
% 3.04/0.99  ------ SAT Options
% 3.04/0.99  
% 3.04/0.99  --sat_mode                              false
% 3.04/0.99  --sat_fm_restart_options                ""
% 3.04/0.99  --sat_gr_def                            false
% 3.04/0.99  --sat_epr_types                         true
% 3.04/0.99  --sat_non_cyclic_types                  false
% 3.04/0.99  --sat_finite_models                     false
% 3.04/0.99  --sat_fm_lemmas                         false
% 3.04/0.99  --sat_fm_prep                           false
% 3.04/0.99  --sat_fm_uc_incr                        true
% 3.04/0.99  --sat_out_model                         small
% 3.04/0.99  --sat_out_clauses                       false
% 3.04/0.99  
% 3.04/0.99  ------ QBF Options
% 3.04/0.99  
% 3.04/0.99  --qbf_mode                              false
% 3.04/0.99  --qbf_elim_univ                         false
% 3.04/0.99  --qbf_dom_inst                          none
% 3.04/0.99  --qbf_dom_pre_inst                      false
% 3.04/0.99  --qbf_sk_in                             false
% 3.04/0.99  --qbf_pred_elim                         true
% 3.04/0.99  --qbf_split                             512
% 3.04/0.99  
% 3.04/0.99  ------ BMC1 Options
% 3.04/0.99  
% 3.04/0.99  --bmc1_incremental                      false
% 3.04/0.99  --bmc1_axioms                           reachable_all
% 3.04/0.99  --bmc1_min_bound                        0
% 3.04/0.99  --bmc1_max_bound                        -1
% 3.04/0.99  --bmc1_max_bound_default                -1
% 3.04/0.99  --bmc1_symbol_reachability              true
% 3.04/0.99  --bmc1_property_lemmas                  false
% 3.04/0.99  --bmc1_k_induction                      false
% 3.04/0.99  --bmc1_non_equiv_states                 false
% 3.04/0.99  --bmc1_deadlock                         false
% 3.04/0.99  --bmc1_ucm                              false
% 3.04/0.99  --bmc1_add_unsat_core                   none
% 3.04/0.99  --bmc1_unsat_core_children              false
% 3.04/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.04/0.99  --bmc1_out_stat                         full
% 3.04/0.99  --bmc1_ground_init                      false
% 3.04/0.99  --bmc1_pre_inst_next_state              false
% 3.04/0.99  --bmc1_pre_inst_state                   false
% 3.04/0.99  --bmc1_pre_inst_reach_state             false
% 3.04/0.99  --bmc1_out_unsat_core                   false
% 3.04/0.99  --bmc1_aig_witness_out                  false
% 3.04/0.99  --bmc1_verbose                          false
% 3.04/0.99  --bmc1_dump_clauses_tptp                false
% 3.04/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.04/0.99  --bmc1_dump_file                        -
% 3.04/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.04/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.04/0.99  --bmc1_ucm_extend_mode                  1
% 3.04/0.99  --bmc1_ucm_init_mode                    2
% 3.04/0.99  --bmc1_ucm_cone_mode                    none
% 3.04/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.04/0.99  --bmc1_ucm_relax_model                  4
% 3.04/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.04/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.04/0.99  --bmc1_ucm_layered_model                none
% 3.04/0.99  --bmc1_ucm_max_lemma_size               10
% 3.04/0.99  
% 3.04/0.99  ------ AIG Options
% 3.04/0.99  
% 3.04/0.99  --aig_mode                              false
% 3.04/0.99  
% 3.04/0.99  ------ Instantiation Options
% 3.04/0.99  
% 3.04/0.99  --instantiation_flag                    true
% 3.04/0.99  --inst_sos_flag                         false
% 3.04/0.99  --inst_sos_phase                        true
% 3.04/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.04/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.04/0.99  --inst_lit_sel_side                     num_symb
% 3.04/0.99  --inst_solver_per_active                1400
% 3.04/0.99  --inst_solver_calls_frac                1.
% 3.04/0.99  --inst_passive_queue_type               priority_queues
% 3.04/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.04/0.99  --inst_passive_queues_freq              [25;2]
% 3.04/0.99  --inst_dismatching                      true
% 3.04/0.99  --inst_eager_unprocessed_to_passive     true
% 3.04/0.99  --inst_prop_sim_given                   true
% 3.04/0.99  --inst_prop_sim_new                     false
% 3.04/0.99  --inst_subs_new                         false
% 3.04/0.99  --inst_eq_res_simp                      false
% 3.04/0.99  --inst_subs_given                       false
% 3.04/0.99  --inst_orphan_elimination               true
% 3.04/0.99  --inst_learning_loop_flag               true
% 3.04/0.99  --inst_learning_start                   3000
% 3.04/0.99  --inst_learning_factor                  2
% 3.04/0.99  --inst_start_prop_sim_after_learn       3
% 3.04/0.99  --inst_sel_renew                        solver
% 3.04/0.99  --inst_lit_activity_flag                true
% 3.04/0.99  --inst_restr_to_given                   false
% 3.04/0.99  --inst_activity_threshold               500
% 3.04/0.99  --inst_out_proof                        true
% 3.04/0.99  
% 3.04/0.99  ------ Resolution Options
% 3.04/0.99  
% 3.04/0.99  --resolution_flag                       true
% 3.04/0.99  --res_lit_sel                           adaptive
% 3.04/0.99  --res_lit_sel_side                      none
% 3.04/0.99  --res_ordering                          kbo
% 3.04/0.99  --res_to_prop_solver                    active
% 3.04/0.99  --res_prop_simpl_new                    false
% 3.04/0.99  --res_prop_simpl_given                  true
% 3.04/0.99  --res_passive_queue_type                priority_queues
% 3.04/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.04/0.99  --res_passive_queues_freq               [15;5]
% 3.04/0.99  --res_forward_subs                      full
% 3.04/0.99  --res_backward_subs                     full
% 3.04/0.99  --res_forward_subs_resolution           true
% 3.04/0.99  --res_backward_subs_resolution          true
% 3.04/0.99  --res_orphan_elimination                true
% 3.04/0.99  --res_time_limit                        2.
% 3.04/0.99  --res_out_proof                         true
% 3.04/0.99  
% 3.04/0.99  ------ Superposition Options
% 3.04/0.99  
% 3.04/0.99  --superposition_flag                    true
% 3.04/0.99  --sup_passive_queue_type                priority_queues
% 3.04/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.04/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.04/0.99  --demod_completeness_check              fast
% 3.04/0.99  --demod_use_ground                      true
% 3.04/0.99  --sup_to_prop_solver                    passive
% 3.04/0.99  --sup_prop_simpl_new                    true
% 3.04/0.99  --sup_prop_simpl_given                  true
% 3.04/0.99  --sup_fun_splitting                     false
% 3.04/0.99  --sup_smt_interval                      50000
% 3.04/0.99  
% 3.04/0.99  ------ Superposition Simplification Setup
% 3.04/0.99  
% 3.04/0.99  --sup_indices_passive                   []
% 3.04/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.04/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.99  --sup_full_bw                           [BwDemod]
% 3.04/0.99  --sup_immed_triv                        [TrivRules]
% 3.04/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.04/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.99  --sup_immed_bw_main                     []
% 3.04/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.04/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.04/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.04/0.99  
% 3.04/0.99  ------ Combination Options
% 3.04/0.99  
% 3.04/0.99  --comb_res_mult                         3
% 3.04/0.99  --comb_sup_mult                         2
% 3.04/0.99  --comb_inst_mult                        10
% 3.04/0.99  
% 3.04/0.99  ------ Debug Options
% 3.04/0.99  
% 3.04/0.99  --dbg_backtrace                         false
% 3.04/0.99  --dbg_dump_prop_clauses                 false
% 3.04/0.99  --dbg_dump_prop_clauses_file            -
% 3.04/0.99  --dbg_out_stat                          false
% 3.04/0.99  ------ Parsing...
% 3.04/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.04/0.99  
% 3.04/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 3.04/0.99  
% 3.04/0.99  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.04/0.99  
% 3.04/0.99  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.04/0.99  ------ Proving...
% 3.04/0.99  ------ Problem Properties 
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  clauses                                 27
% 3.04/0.99  conjectures                             2
% 3.04/0.99  EPR                                     2
% 3.04/0.99  Horn                                    18
% 3.04/0.99  unary                                   7
% 3.04/0.99  binary                                  9
% 3.04/0.99  lits                                    73
% 3.04/0.99  lits eq                                 20
% 3.04/0.99  fd_pure                                 0
% 3.04/0.99  fd_pseudo                               0
% 3.04/0.99  fd_cond                                 3
% 3.04/0.99  fd_pseudo_cond                          0
% 3.04/0.99  AC symbols                              0
% 3.04/0.99  
% 3.04/0.99  ------ Schedule dynamic 5 is on 
% 3.04/0.99  
% 3.04/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  ------ 
% 3.04/0.99  Current options:
% 3.04/0.99  ------ 
% 3.04/0.99  
% 3.04/0.99  ------ Input Options
% 3.04/0.99  
% 3.04/0.99  --out_options                           all
% 3.04/0.99  --tptp_safe_out                         true
% 3.04/0.99  --problem_path                          ""
% 3.04/0.99  --include_path                          ""
% 3.04/0.99  --clausifier                            res/vclausify_rel
% 3.04/0.99  --clausifier_options                    --mode clausify
% 3.04/0.99  --stdin                                 false
% 3.04/0.99  --stats_out                             all
% 3.04/0.99  
% 3.04/0.99  ------ General Options
% 3.04/0.99  
% 3.04/0.99  --fof                                   false
% 3.04/0.99  --time_out_real                         305.
% 3.04/0.99  --time_out_virtual                      -1.
% 3.04/0.99  --symbol_type_check                     false
% 3.04/0.99  --clausify_out                          false
% 3.04/0.99  --sig_cnt_out                           false
% 3.04/0.99  --trig_cnt_out                          false
% 3.04/0.99  --trig_cnt_out_tolerance                1.
% 3.04/0.99  --trig_cnt_out_sk_spl                   false
% 3.04/0.99  --abstr_cl_out                          false
% 3.04/0.99  
% 3.04/0.99  ------ Global Options
% 3.04/0.99  
% 3.04/0.99  --schedule                              default
% 3.04/0.99  --add_important_lit                     false
% 3.04/0.99  --prop_solver_per_cl                    1000
% 3.04/0.99  --min_unsat_core                        false
% 3.04/0.99  --soft_assumptions                      false
% 3.04/0.99  --soft_lemma_size                       3
% 3.04/0.99  --prop_impl_unit_size                   0
% 3.04/0.99  --prop_impl_unit                        []
% 3.04/0.99  --share_sel_clauses                     true
% 3.04/0.99  --reset_solvers                         false
% 3.04/0.99  --bc_imp_inh                            [conj_cone]
% 3.04/0.99  --conj_cone_tolerance                   3.
% 3.04/0.99  --extra_neg_conj                        none
% 3.04/0.99  --large_theory_mode                     true
% 3.04/0.99  --prolific_symb_bound                   200
% 3.04/0.99  --lt_threshold                          2000
% 3.04/0.99  --clause_weak_htbl                      true
% 3.04/0.99  --gc_record_bc_elim                     false
% 3.04/0.99  
% 3.04/0.99  ------ Preprocessing Options
% 3.04/0.99  
% 3.04/0.99  --preprocessing_flag                    true
% 3.04/0.99  --time_out_prep_mult                    0.1
% 3.04/0.99  --splitting_mode                        input
% 3.04/0.99  --splitting_grd                         true
% 3.04/0.99  --splitting_cvd                         false
% 3.04/0.99  --splitting_cvd_svl                     false
% 3.04/0.99  --splitting_nvd                         32
% 3.04/0.99  --sub_typing                            true
% 3.04/0.99  --prep_gs_sim                           true
% 3.04/0.99  --prep_unflatten                        true
% 3.04/0.99  --prep_res_sim                          true
% 3.04/0.99  --prep_upred                            true
% 3.04/0.99  --prep_sem_filter                       exhaustive
% 3.04/0.99  --prep_sem_filter_out                   false
% 3.04/0.99  --pred_elim                             true
% 3.04/0.99  --res_sim_input                         true
% 3.04/0.99  --eq_ax_congr_red                       true
% 3.04/0.99  --pure_diseq_elim                       true
% 3.04/0.99  --brand_transform                       false
% 3.04/0.99  --non_eq_to_eq                          false
% 3.04/0.99  --prep_def_merge                        true
% 3.04/0.99  --prep_def_merge_prop_impl              false
% 3.04/0.99  --prep_def_merge_mbd                    true
% 3.04/0.99  --prep_def_merge_tr_red                 false
% 3.04/0.99  --prep_def_merge_tr_cl                  false
% 3.04/0.99  --smt_preprocessing                     true
% 3.04/0.99  --smt_ac_axioms                         fast
% 3.04/0.99  --preprocessed_out                      false
% 3.04/0.99  --preprocessed_stats                    false
% 3.04/0.99  
% 3.04/0.99  ------ Abstraction refinement Options
% 3.04/0.99  
% 3.04/0.99  --abstr_ref                             []
% 3.04/0.99  --abstr_ref_prep                        false
% 3.04/0.99  --abstr_ref_until_sat                   false
% 3.04/0.99  --abstr_ref_sig_restrict                funpre
% 3.04/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.04/0.99  --abstr_ref_under                       []
% 3.04/0.99  
% 3.04/0.99  ------ SAT Options
% 3.04/0.99  
% 3.04/0.99  --sat_mode                              false
% 3.04/0.99  --sat_fm_restart_options                ""
% 3.04/0.99  --sat_gr_def                            false
% 3.04/0.99  --sat_epr_types                         true
% 3.04/0.99  --sat_non_cyclic_types                  false
% 3.04/0.99  --sat_finite_models                     false
% 3.04/0.99  --sat_fm_lemmas                         false
% 3.04/0.99  --sat_fm_prep                           false
% 3.04/0.99  --sat_fm_uc_incr                        true
% 3.04/0.99  --sat_out_model                         small
% 3.04/0.99  --sat_out_clauses                       false
% 3.04/0.99  
% 3.04/0.99  ------ QBF Options
% 3.04/0.99  
% 3.04/0.99  --qbf_mode                              false
% 3.04/0.99  --qbf_elim_univ                         false
% 3.04/0.99  --qbf_dom_inst                          none
% 3.04/0.99  --qbf_dom_pre_inst                      false
% 3.04/0.99  --qbf_sk_in                             false
% 3.04/0.99  --qbf_pred_elim                         true
% 3.04/0.99  --qbf_split                             512
% 3.04/0.99  
% 3.04/0.99  ------ BMC1 Options
% 3.04/0.99  
% 3.04/0.99  --bmc1_incremental                      false
% 3.04/0.99  --bmc1_axioms                           reachable_all
% 3.04/0.99  --bmc1_min_bound                        0
% 3.04/0.99  --bmc1_max_bound                        -1
% 3.04/0.99  --bmc1_max_bound_default                -1
% 3.04/0.99  --bmc1_symbol_reachability              true
% 3.04/0.99  --bmc1_property_lemmas                  false
% 3.04/0.99  --bmc1_k_induction                      false
% 3.04/0.99  --bmc1_non_equiv_states                 false
% 3.04/0.99  --bmc1_deadlock                         false
% 3.04/0.99  --bmc1_ucm                              false
% 3.04/0.99  --bmc1_add_unsat_core                   none
% 3.04/0.99  --bmc1_unsat_core_children              false
% 3.04/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.04/0.99  --bmc1_out_stat                         full
% 3.04/0.99  --bmc1_ground_init                      false
% 3.04/0.99  --bmc1_pre_inst_next_state              false
% 3.04/0.99  --bmc1_pre_inst_state                   false
% 3.04/0.99  --bmc1_pre_inst_reach_state             false
% 3.04/0.99  --bmc1_out_unsat_core                   false
% 3.04/0.99  --bmc1_aig_witness_out                  false
% 3.04/0.99  --bmc1_verbose                          false
% 3.04/0.99  --bmc1_dump_clauses_tptp                false
% 3.04/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.04/0.99  --bmc1_dump_file                        -
% 3.04/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.04/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.04/0.99  --bmc1_ucm_extend_mode                  1
% 3.04/0.99  --bmc1_ucm_init_mode                    2
% 3.04/0.99  --bmc1_ucm_cone_mode                    none
% 3.04/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.04/0.99  --bmc1_ucm_relax_model                  4
% 3.04/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.04/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.04/0.99  --bmc1_ucm_layered_model                none
% 3.04/0.99  --bmc1_ucm_max_lemma_size               10
% 3.04/0.99  
% 3.04/0.99  ------ AIG Options
% 3.04/0.99  
% 3.04/0.99  --aig_mode                              false
% 3.04/0.99  
% 3.04/0.99  ------ Instantiation Options
% 3.04/0.99  
% 3.04/0.99  --instantiation_flag                    true
% 3.04/0.99  --inst_sos_flag                         false
% 3.04/0.99  --inst_sos_phase                        true
% 3.04/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.04/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.04/0.99  --inst_lit_sel_side                     none
% 3.04/0.99  --inst_solver_per_active                1400
% 3.04/0.99  --inst_solver_calls_frac                1.
% 3.04/0.99  --inst_passive_queue_type               priority_queues
% 3.04/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.04/0.99  --inst_passive_queues_freq              [25;2]
% 3.04/0.99  --inst_dismatching                      true
% 3.04/0.99  --inst_eager_unprocessed_to_passive     true
% 3.04/0.99  --inst_prop_sim_given                   true
% 3.04/0.99  --inst_prop_sim_new                     false
% 3.04/0.99  --inst_subs_new                         false
% 3.04/0.99  --inst_eq_res_simp                      false
% 3.04/0.99  --inst_subs_given                       false
% 3.04/0.99  --inst_orphan_elimination               true
% 3.04/0.99  --inst_learning_loop_flag               true
% 3.04/0.99  --inst_learning_start                   3000
% 3.04/0.99  --inst_learning_factor                  2
% 3.04/0.99  --inst_start_prop_sim_after_learn       3
% 3.04/0.99  --inst_sel_renew                        solver
% 3.04/0.99  --inst_lit_activity_flag                true
% 3.04/0.99  --inst_restr_to_given                   false
% 3.04/0.99  --inst_activity_threshold               500
% 3.04/0.99  --inst_out_proof                        true
% 3.04/0.99  
% 3.04/0.99  ------ Resolution Options
% 3.04/0.99  
% 3.04/0.99  --resolution_flag                       false
% 3.04/0.99  --res_lit_sel                           adaptive
% 3.04/0.99  --res_lit_sel_side                      none
% 3.04/0.99  --res_ordering                          kbo
% 3.04/0.99  --res_to_prop_solver                    active
% 3.04/0.99  --res_prop_simpl_new                    false
% 3.04/0.99  --res_prop_simpl_given                  true
% 3.04/0.99  --res_passive_queue_type                priority_queues
% 3.04/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.04/0.99  --res_passive_queues_freq               [15;5]
% 3.04/0.99  --res_forward_subs                      full
% 3.04/0.99  --res_backward_subs                     full
% 3.04/0.99  --res_forward_subs_resolution           true
% 3.04/0.99  --res_backward_subs_resolution          true
% 3.04/0.99  --res_orphan_elimination                true
% 3.04/0.99  --res_time_limit                        2.
% 3.04/0.99  --res_out_proof                         true
% 3.04/0.99  
% 3.04/0.99  ------ Superposition Options
% 3.04/0.99  
% 3.04/0.99  --superposition_flag                    true
% 3.04/0.99  --sup_passive_queue_type                priority_queues
% 3.04/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.04/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.04/0.99  --demod_completeness_check              fast
% 3.04/0.99  --demod_use_ground                      true
% 3.04/0.99  --sup_to_prop_solver                    passive
% 3.04/0.99  --sup_prop_simpl_new                    true
% 3.04/0.99  --sup_prop_simpl_given                  true
% 3.04/0.99  --sup_fun_splitting                     false
% 3.04/0.99  --sup_smt_interval                      50000
% 3.04/0.99  
% 3.04/0.99  ------ Superposition Simplification Setup
% 3.04/0.99  
% 3.04/0.99  --sup_indices_passive                   []
% 3.04/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.04/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.99  --sup_full_bw                           [BwDemod]
% 3.04/0.99  --sup_immed_triv                        [TrivRules]
% 3.04/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.04/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.99  --sup_immed_bw_main                     []
% 3.04/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.04/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.04/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.04/0.99  
% 3.04/0.99  ------ Combination Options
% 3.04/0.99  
% 3.04/0.99  --comb_res_mult                         3
% 3.04/0.99  --comb_sup_mult                         2
% 3.04/0.99  --comb_inst_mult                        10
% 3.04/0.99  
% 3.04/0.99  ------ Debug Options
% 3.04/0.99  
% 3.04/0.99  --dbg_backtrace                         false
% 3.04/0.99  --dbg_dump_prop_clauses                 false
% 3.04/0.99  --dbg_dump_prop_clauses_file            -
% 3.04/0.99  --dbg_out_stat                          false
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  ------ Proving...
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  % SZS status Theorem for theBenchmark.p
% 3.04/0.99  
% 3.04/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.04/0.99  
% 3.04/0.99  fof(f8,axiom,(
% 3.04/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f28,plain,(
% 3.04/0.99    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.04/0.99    inference(ennf_transformation,[],[f8])).
% 3.04/0.99  
% 3.04/0.99  fof(f29,plain,(
% 3.04/0.99    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.04/0.99    inference(flattening,[],[f28])).
% 3.04/0.99  
% 3.04/0.99  fof(f80,plain,(
% 3.04/0.99    ( ! [X0,X1] : (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f29])).
% 3.04/0.99  
% 3.04/0.99  fof(f13,conjecture,(
% 3.04/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))))))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f14,negated_conjecture,(
% 3.04/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))))))),
% 3.04/0.99    inference(negated_conjecture,[],[f13])).
% 3.04/0.99  
% 3.04/0.99  fof(f37,plain,(
% 3.04/0.99    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1)))) & m1_pre_topc(X1,X0)) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.04/0.99    inference(ennf_transformation,[],[f14])).
% 3.04/0.99  
% 3.04/0.99  fof(f38,plain,(
% 3.04/0.99    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.04/0.99    inference(flattening,[],[f37])).
% 3.04/0.99  
% 3.04/0.99  fof(f54,plain,(
% 3.04/0.99    ? [X0] : (? [X1] : ((((~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) & ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.04/0.99    inference(nnf_transformation,[],[f38])).
% 3.04/0.99  
% 3.04/0.99  fof(f55,plain,(
% 3.04/0.99    ? [X0] : (? [X1] : ((~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.04/0.99    inference(flattening,[],[f54])).
% 3.04/0.99  
% 3.04/0.99  fof(f57,plain,(
% 3.04/0.99    ( ! [X0] : (? [X1] : ((~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0)) => ((~m1_subset_1(k9_tmap_1(X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,sK4))))) | ~v5_pre_topc(k9_tmap_1(X0,sK4),X0,k8_tmap_1(X0,sK4)) | ~v1_funct_2(k9_tmap_1(X0,sK4),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,sK4))) | ~v1_funct_1(k9_tmap_1(X0,sK4)) | ~m1_pre_topc(sK4,X0) | ~v1_tsep_1(sK4,X0)) & ((m1_subset_1(k9_tmap_1(X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,sK4))))) & v5_pre_topc(k9_tmap_1(X0,sK4),X0,k8_tmap_1(X0,sK4)) & v1_funct_2(k9_tmap_1(X0,sK4),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,sK4))) & v1_funct_1(k9_tmap_1(X0,sK4))) | (m1_pre_topc(sK4,X0) & v1_tsep_1(sK4,X0))) & m1_pre_topc(sK4,X0))) )),
% 3.04/0.99    introduced(choice_axiom,[])).
% 3.04/0.99  
% 3.04/0.99  fof(f56,plain,(
% 3.04/0.99    ? [X0] : (? [X1] : ((~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~m1_subset_1(k9_tmap_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X1))))) | ~v5_pre_topc(k9_tmap_1(sK3,X1),sK3,k8_tmap_1(sK3,X1)) | ~v1_funct_2(k9_tmap_1(sK3,X1),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X1))) | ~v1_funct_1(k9_tmap_1(sK3,X1)) | ~m1_pre_topc(X1,sK3) | ~v1_tsep_1(X1,sK3)) & ((m1_subset_1(k9_tmap_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X1))))) & v5_pre_topc(k9_tmap_1(sK3,X1),sK3,k8_tmap_1(sK3,X1)) & v1_funct_2(k9_tmap_1(sK3,X1),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,X1))) & v1_funct_1(k9_tmap_1(sK3,X1))) | (m1_pre_topc(X1,sK3) & v1_tsep_1(X1,sK3))) & m1_pre_topc(X1,sK3)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 3.04/0.99    introduced(choice_axiom,[])).
% 3.04/0.99  
% 3.04/0.99  fof(f58,plain,(
% 3.04/0.99    ((~m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) | ~v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4)) | ~v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) | ~v1_funct_1(k9_tmap_1(sK3,sK4)) | ~m1_pre_topc(sK4,sK3) | ~v1_tsep_1(sK4,sK3)) & ((m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) & v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4)) & v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) & v1_funct_1(k9_tmap_1(sK3,sK4))) | (m1_pre_topc(sK4,sK3) & v1_tsep_1(sK4,sK3))) & m1_pre_topc(sK4,sK3)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 3.04/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f55,f57,f56])).
% 3.04/0.99  
% 3.04/0.99  fof(f92,plain,(
% 3.04/0.99    ~v2_struct_0(sK3)),
% 3.04/0.99    inference(cnf_transformation,[],[f58])).
% 3.04/0.99  
% 3.04/0.99  fof(f93,plain,(
% 3.04/0.99    v2_pre_topc(sK3)),
% 3.04/0.99    inference(cnf_transformation,[],[f58])).
% 3.04/0.99  
% 3.04/0.99  fof(f94,plain,(
% 3.04/0.99    l1_pre_topc(sK3)),
% 3.04/0.99    inference(cnf_transformation,[],[f58])).
% 3.04/0.99  
% 3.04/0.99  fof(f3,axiom,(
% 3.04/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f18,plain,(
% 3.04/0.99    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 3.04/0.99    inference(ennf_transformation,[],[f3])).
% 3.04/0.99  
% 3.04/0.99  fof(f19,plain,(
% 3.04/0.99    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 3.04/0.99    inference(flattening,[],[f18])).
% 3.04/0.99  
% 3.04/0.99  fof(f39,plain,(
% 3.04/0.99    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 3.04/0.99    inference(nnf_transformation,[],[f19])).
% 3.04/0.99  
% 3.04/0.99  fof(f61,plain,(
% 3.04/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f39])).
% 3.04/0.99  
% 3.04/0.99  fof(f9,axiom,(
% 3.04/0.99    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f30,plain,(
% 3.04/0.99    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.04/0.99    inference(ennf_transformation,[],[f9])).
% 3.04/0.99  
% 3.04/0.99  fof(f31,plain,(
% 3.04/0.99    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.04/0.99    inference(flattening,[],[f30])).
% 3.04/0.99  
% 3.04/0.99  fof(f83,plain,(
% 3.04/0.99    ( ! [X0,X1] : (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f31])).
% 3.04/0.99  
% 3.04/0.99  fof(f103,plain,(
% 3.04/0.99    m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) | m1_pre_topc(sK4,sK3)),
% 3.04/0.99    inference(cnf_transformation,[],[f58])).
% 3.04/0.99  
% 3.04/0.99  fof(f95,plain,(
% 3.04/0.99    m1_pre_topc(sK4,sK3)),
% 3.04/0.99    inference(cnf_transformation,[],[f58])).
% 3.04/0.99  
% 3.04/0.99  fof(f81,plain,(
% 3.04/0.99    ( ! [X0,X1] : (v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f31])).
% 3.04/0.99  
% 3.04/0.99  fof(f12,axiom,(
% 3.04/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f36,plain,(
% 3.04/0.99    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.04/0.99    inference(ennf_transformation,[],[f12])).
% 3.04/0.99  
% 3.04/0.99  fof(f91,plain,(
% 3.04/0.99    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f36])).
% 3.04/0.99  
% 3.04/0.99  fof(f5,axiom,(
% 3.04/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(X2)) => (k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))))))))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f22,plain,(
% 3.04/0.99    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : ((r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.04/0.99    inference(ennf_transformation,[],[f5])).
% 3.04/0.99  
% 3.04/0.99  fof(f23,plain,(
% 3.04/0.99    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.04/0.99    inference(flattening,[],[f22])).
% 3.04/0.99  
% 3.04/0.99  fof(f44,plain,(
% 3.04/0.99    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | ? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.04/0.99    inference(nnf_transformation,[],[f23])).
% 3.04/0.99  
% 3.04/0.99  fof(f45,plain,(
% 3.04/0.99    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | ? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.04/0.99    inference(rectify,[],[f44])).
% 3.04/0.99  
% 3.04/0.99  fof(f46,plain,(
% 3.04/0.99    ! [X2,X1,X0] : (? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2))) & u1_struct_0(X1) = sK1(X0,X1,X2) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.04/0.99    introduced(choice_axiom,[])).
% 3.04/0.99  
% 3.04/0.99  fof(f47,plain,(
% 3.04/0.99    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2))) & u1_struct_0(X1) = sK1(X0,X1,X2) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.04/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f45,f46])).
% 3.04/0.99  
% 3.04/0.99  fof(f67,plain,(
% 3.04/0.99    ( ! [X4,X2,X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k9_tmap_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f47])).
% 3.04/0.99  
% 3.04/0.99  fof(f108,plain,(
% 3.04/0.99    ( ! [X2,X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),X2,k7_tmap_1(X0,u1_struct_0(X1))) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k9_tmap_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.04/0.99    inference(equality_resolution,[],[f67])).
% 3.04/0.99  
% 3.04/0.99  fof(f109,plain,(
% 3.04/0.99    ( ! [X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1))) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.04/0.99    inference(equality_resolution,[],[f108])).
% 3.04/0.99  
% 3.04/0.99  fof(f82,plain,(
% 3.04/0.99    ( ! [X0,X1] : (v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f31])).
% 3.04/0.99  
% 3.04/0.99  fof(f2,axiom,(
% 3.04/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f16,plain,(
% 3.04/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.04/0.99    inference(ennf_transformation,[],[f2])).
% 3.04/0.99  
% 3.04/0.99  fof(f17,plain,(
% 3.04/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.04/0.99    inference(flattening,[],[f16])).
% 3.04/0.99  
% 3.04/0.99  fof(f60,plain,(
% 3.04/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f17])).
% 3.04/0.99  
% 3.04/0.99  fof(f1,axiom,(
% 3.04/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f15,plain,(
% 3.04/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.04/0.99    inference(ennf_transformation,[],[f1])).
% 3.04/0.99  
% 3.04/0.99  fof(f59,plain,(
% 3.04/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f15])).
% 3.04/0.99  
% 3.04/0.99  fof(f78,plain,(
% 3.04/0.99    ( ! [X0,X1] : (v1_funct_1(k7_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f29])).
% 3.04/0.99  
% 3.04/0.99  fof(f79,plain,(
% 3.04/0.99    ( ! [X0,X1] : (v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f29])).
% 3.04/0.99  
% 3.04/0.99  fof(f4,axiom,(
% 3.04/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & v1_pre_topc(X2)) => (k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => k6_tmap_1(X0,X3) = X2))))))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f20,plain,(
% 3.04/0.99    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : ((k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.04/0.99    inference(ennf_transformation,[],[f4])).
% 3.04/0.99  
% 3.04/0.99  fof(f21,plain,(
% 3.04/0.99    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.04/0.99    inference(flattening,[],[f20])).
% 3.04/0.99  
% 3.04/0.99  fof(f40,plain,(
% 3.04/0.99    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.04/0.99    inference(nnf_transformation,[],[f21])).
% 3.04/0.99  
% 3.04/0.99  fof(f41,plain,(
% 3.04/0.99    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.04/0.99    inference(rectify,[],[f40])).
% 3.04/0.99  
% 3.04/0.99  fof(f42,plain,(
% 3.04/0.99    ! [X2,X1,X0] : (? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (k6_tmap_1(X0,sK0(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK0(X0,X1,X2) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.04/0.99    introduced(choice_axiom,[])).
% 3.04/0.99  
% 3.04/0.99  fof(f43,plain,(
% 3.04/0.99    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | (k6_tmap_1(X0,sK0(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK0(X0,X1,X2) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.04/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f42])).
% 3.04/0.99  
% 3.04/0.99  fof(f63,plain,(
% 3.04/0.99    ( ! [X4,X2,X0,X1] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f43])).
% 3.04/0.99  
% 3.04/0.99  fof(f106,plain,(
% 3.04/0.99    ( ! [X2,X0,X1] : (k6_tmap_1(X0,u1_struct_0(X1)) = X2 | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.04/0.99    inference(equality_resolution,[],[f63])).
% 3.04/0.99  
% 3.04/0.99  fof(f107,plain,(
% 3.04/0.99    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.04/0.99    inference(equality_resolution,[],[f106])).
% 3.04/0.99  
% 3.04/0.99  fof(f7,axiom,(
% 3.04/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f26,plain,(
% 3.04/0.99    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.04/0.99    inference(ennf_transformation,[],[f7])).
% 3.04/0.99  
% 3.04/0.99  fof(f27,plain,(
% 3.04/0.99    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.04/0.99    inference(flattening,[],[f26])).
% 3.04/0.99  
% 3.04/0.99  fof(f75,plain,(
% 3.04/0.99    ( ! [X0,X1] : (v1_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f27])).
% 3.04/0.99  
% 3.04/0.99  fof(f65,plain,(
% 3.04/0.99    ( ! [X2,X0,X1] : (k8_tmap_1(X0,X1) = X2 | u1_struct_0(X1) = sK0(X0,X1,X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f43])).
% 3.04/0.99  
% 3.04/0.99  fof(f76,plain,(
% 3.04/0.99    ( ! [X0,X1] : (v2_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f27])).
% 3.04/0.99  
% 3.04/0.99  fof(f77,plain,(
% 3.04/0.99    ( ! [X0,X1] : (l1_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f27])).
% 3.04/0.99  
% 3.04/0.99  fof(f66,plain,(
% 3.04/0.99    ( ! [X2,X0,X1] : (k8_tmap_1(X0,X1) = X2 | k6_tmap_1(X0,sK0(X0,X1,X2)) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f43])).
% 3.04/0.99  
% 3.04/0.99  fof(f10,axiom,(
% 3.04/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f32,plain,(
% 3.04/0.99    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.04/0.99    inference(ennf_transformation,[],[f10])).
% 3.04/0.99  
% 3.04/0.99  fof(f33,plain,(
% 3.04/0.99    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.04/0.99    inference(flattening,[],[f32])).
% 3.04/0.99  
% 3.04/0.99  fof(f84,plain,(
% 3.04/0.99    ( ! [X0,X1] : (u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f33])).
% 3.04/0.99  
% 3.04/0.99  fof(f11,axiom,(
% 3.04/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f34,plain,(
% 3.04/0.99    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.04/0.99    inference(ennf_transformation,[],[f11])).
% 3.04/0.99  
% 3.04/0.99  fof(f35,plain,(
% 3.04/0.99    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.04/0.99    inference(flattening,[],[f34])).
% 3.04/0.99  
% 3.04/0.99  fof(f52,plain,(
% 3.04/0.99    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | (~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1)))) & ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.04/0.99    inference(nnf_transformation,[],[f35])).
% 3.04/0.99  
% 3.04/0.99  fof(f53,plain,(
% 3.04/0.99    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1))) & ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.04/0.99    inference(flattening,[],[f52])).
% 3.04/0.99  
% 3.04/0.99  fof(f90,plain,(
% 3.04/0.99    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f53])).
% 3.04/0.99  
% 3.04/0.99  fof(f100,plain,(
% 3.04/0.99    v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4)) | v1_tsep_1(sK4,sK3)),
% 3.04/0.99    inference(cnf_transformation,[],[f58])).
% 3.04/0.99  
% 3.04/0.99  fof(f6,axiom,(
% 3.04/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tsep_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v3_pre_topc(X2,X0))))))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f24,plain,(
% 3.04/0.99    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.04/0.99    inference(ennf_transformation,[],[f6])).
% 3.04/0.99  
% 3.04/0.99  fof(f25,plain,(
% 3.04/0.99    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.04/0.99    inference(flattening,[],[f24])).
% 3.04/0.99  
% 3.04/0.99  fof(f48,plain,(
% 3.04/0.99    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.04/0.99    inference(nnf_transformation,[],[f25])).
% 3.04/0.99  
% 3.04/0.99  fof(f49,plain,(
% 3.04/0.99    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.04/0.99    inference(rectify,[],[f48])).
% 3.04/0.99  
% 3.04/0.99  fof(f50,plain,(
% 3.04/0.99    ! [X1,X0] : (? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK2(X0,X1),X0) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.04/0.99    introduced(choice_axiom,[])).
% 3.04/0.99  
% 3.04/0.99  fof(f51,plain,(
% 3.04/0.99    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | (~v3_pre_topc(sK2(X0,X1),X0) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.04/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f49,f50])).
% 3.04/0.99  
% 3.04/0.99  fof(f74,plain,(
% 3.04/0.99    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(sK2(X0,X1),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f51])).
% 3.04/0.99  
% 3.04/0.99  fof(f72,plain,(
% 3.04/0.99    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f51])).
% 3.04/0.99  
% 3.04/0.99  fof(f88,plain,(
% 3.04/0.99    ( ! [X0,X1] : (v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f53])).
% 3.04/0.99  
% 3.04/0.99  fof(f104,plain,(
% 3.04/0.99    ~m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) | ~v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4)) | ~v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) | ~v1_funct_1(k9_tmap_1(sK3,sK4)) | ~m1_pre_topc(sK4,sK3) | ~v1_tsep_1(sK4,sK3)),
% 3.04/0.99    inference(cnf_transformation,[],[f58])).
% 3.04/0.99  
% 3.04/0.99  fof(f71,plain,(
% 3.04/0.99    ( ! [X0,X3,X1] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f51])).
% 3.04/0.99  
% 3.04/0.99  fof(f110,plain,(
% 3.04/0.99    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.04/0.99    inference(equality_resolution,[],[f71])).
% 3.04/0.99  
% 3.04/0.99  fof(f73,plain,(
% 3.04/0.99    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | u1_struct_0(X1) = sK2(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f51])).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3070,plain,
% 3.04/0.99      ( X0_57 != X1_57 | X2_57 != X1_57 | X2_57 = X0_57 ),
% 3.04/0.99      theory(equality) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3971,plain,
% 3.04/0.99      ( X0_57 != X1_57
% 3.04/0.99      | X0_57 = k9_tmap_1(sK3,sK4)
% 3.04/0.99      | k9_tmap_1(sK3,sK4) != X1_57 ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_3070]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_5938,plain,
% 3.04/0.99      ( X0_57 != k7_tmap_1(sK3,u1_struct_0(sK4))
% 3.04/0.99      | X0_57 = k9_tmap_1(sK3,sK4)
% 3.04/0.99      | k9_tmap_1(sK3,sK4) != k7_tmap_1(sK3,u1_struct_0(sK4)) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_3971]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_6890,plain,
% 3.04/0.99      ( k7_tmap_1(X0_56,sK2(sK3,sK4)) != k7_tmap_1(sK3,u1_struct_0(sK4))
% 3.04/0.99      | k7_tmap_1(X0_56,sK2(sK3,sK4)) = k9_tmap_1(sK3,sK4)
% 3.04/0.99      | k9_tmap_1(sK3,sK4) != k7_tmap_1(sK3,u1_struct_0(sK4)) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_5938]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_6891,plain,
% 3.04/0.99      ( k7_tmap_1(sK3,sK2(sK3,sK4)) != k7_tmap_1(sK3,u1_struct_0(sK4))
% 3.04/0.99      | k7_tmap_1(sK3,sK2(sK3,sK4)) = k9_tmap_1(sK3,sK4)
% 3.04/0.99      | k9_tmap_1(sK3,sK4) != k7_tmap_1(sK3,u1_struct_0(sK4)) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_6890]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3069,plain,
% 3.04/0.99      ( X0_56 != X1_56 | X2_56 != X1_56 | X2_56 = X0_56 ),
% 3.04/0.99      theory(equality) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4375,plain,
% 3.04/0.99      ( X0_56 != X1_56
% 3.04/0.99      | X0_56 = k8_tmap_1(sK3,sK4)
% 3.04/0.99      | k8_tmap_1(sK3,sK4) != X1_56 ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_3069]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4912,plain,
% 3.04/0.99      ( X0_56 != k6_tmap_1(sK3,u1_struct_0(sK4))
% 3.04/0.99      | X0_56 = k8_tmap_1(sK3,sK4)
% 3.04/0.99      | k8_tmap_1(sK3,sK4) != k6_tmap_1(sK3,u1_struct_0(sK4)) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_4375]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_6579,plain,
% 3.04/0.99      ( k6_tmap_1(X0_56,sK2(sK3,sK4)) != k6_tmap_1(sK3,u1_struct_0(sK4))
% 3.04/0.99      | k6_tmap_1(X0_56,sK2(sK3,sK4)) = k8_tmap_1(sK3,sK4)
% 3.04/0.99      | k8_tmap_1(sK3,sK4) != k6_tmap_1(sK3,u1_struct_0(sK4)) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_4912]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_6581,plain,
% 3.04/0.99      ( k6_tmap_1(sK3,sK2(sK3,sK4)) != k6_tmap_1(sK3,u1_struct_0(sK4))
% 3.04/0.99      | k6_tmap_1(sK3,sK2(sK3,sK4)) = k8_tmap_1(sK3,sK4)
% 3.04/0.99      | k8_tmap_1(sK3,sK4) != k6_tmap_1(sK3,u1_struct_0(sK4)) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_6579]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_19,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.04/0.99      | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
% 3.04/0.99      | ~ v2_pre_topc(X1)
% 3.04/0.99      | v2_struct_0(X1)
% 3.04/0.99      | ~ l1_pre_topc(X1) ),
% 3.04/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_45,negated_conjecture,
% 3.04/0.99      ( ~ v2_struct_0(sK3) ),
% 3.04/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1846,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.04/0.99      | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
% 3.04/0.99      | ~ v2_pre_topc(X1)
% 3.04/0.99      | ~ l1_pre_topc(X1)
% 3.04/0.99      | sK3 != X1 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_45]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1847,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.99      | m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))))
% 3.04/0.99      | ~ v2_pre_topc(sK3)
% 3.04/0.99      | ~ l1_pre_topc(sK3) ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_1846]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_44,negated_conjecture,
% 3.04/0.99      ( v2_pre_topc(sK3) ),
% 3.04/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_43,negated_conjecture,
% 3.04/0.99      ( l1_pre_topc(sK3) ),
% 3.04/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1851,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.99      | m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0))))) ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_1847,c_44,c_43]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3045,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.99      | m1_subset_1(k7_tmap_1(sK3,X0_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0_57))))) ),
% 3.04/0.99      inference(subtyping,[status(esa)],[c_1851]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_6121,plain,
% 3.04/0.99      ( ~ m1_subset_1(sK2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.99      | m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4)))))) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_3045]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3082,plain,
% 3.04/0.99      ( X0_57 != X1_57
% 3.04/0.99      | X0_56 != X1_56
% 3.04/0.99      | k6_tmap_1(X0_56,X0_57) = k6_tmap_1(X1_56,X1_57) ),
% 3.04/0.99      theory(equality) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4335,plain,
% 3.04/0.99      ( X0_57 != u1_struct_0(sK4)
% 3.04/0.99      | X0_56 != sK3
% 3.04/0.99      | k6_tmap_1(X0_56,X0_57) = k6_tmap_1(sK3,u1_struct_0(sK4)) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_3082]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_6098,plain,
% 3.04/0.99      ( sK2(sK3,sK4) != u1_struct_0(sK4)
% 3.04/0.99      | X0_56 != sK3
% 3.04/0.99      | k6_tmap_1(X0_56,sK2(sK3,sK4)) = k6_tmap_1(sK3,u1_struct_0(sK4)) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_4335]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_6107,plain,
% 3.04/0.99      ( sK2(sK3,sK4) != u1_struct_0(sK4)
% 3.04/0.99      | k6_tmap_1(sK3,sK2(sK3,sK4)) = k6_tmap_1(sK3,u1_struct_0(sK4))
% 3.04/0.99      | sK3 != sK3 ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_6098]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3086,plain,
% 3.04/0.99      ( X0_57 != X1_57
% 3.04/0.99      | k7_tmap_1(X0_56,X0_57) = k7_tmap_1(X1_56,X1_57)
% 3.04/0.99      | X0_56 != X1_56 ),
% 3.04/0.99      theory(equality) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4134,plain,
% 3.04/0.99      ( X0_57 != u1_struct_0(sK4)
% 3.04/0.99      | k7_tmap_1(X0_56,X0_57) = k7_tmap_1(sK3,u1_struct_0(sK4))
% 3.04/0.99      | X0_56 != sK3 ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_3086]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_6100,plain,
% 3.04/0.99      ( sK2(sK3,sK4) != u1_struct_0(sK4)
% 3.04/0.99      | k7_tmap_1(X0_56,sK2(sK3,sK4)) = k7_tmap_1(sK3,u1_struct_0(sK4))
% 3.04/0.99      | X0_56 != sK3 ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_4134]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_6106,plain,
% 3.04/0.99      ( sK2(sK3,sK4) != u1_struct_0(sK4)
% 3.04/0.99      | k7_tmap_1(sK3,sK2(sK3,sK4)) = k7_tmap_1(sK3,u1_struct_0(sK4))
% 3.04/0.99      | sK3 != sK3 ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_6100]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4071,plain,
% 3.04/0.99      ( X0_57 != X1_57
% 3.04/0.99      | k9_tmap_1(sK3,sK4) != X1_57
% 3.04/0.99      | k9_tmap_1(sK3,sK4) = X0_57 ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_3070]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4299,plain,
% 3.04/0.99      ( X0_57 != k9_tmap_1(sK3,sK4)
% 3.04/0.99      | k9_tmap_1(sK3,sK4) = X0_57
% 3.04/0.99      | k9_tmap_1(sK3,sK4) != k9_tmap_1(sK3,sK4) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_4071]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_6059,plain,
% 3.04/0.99      ( k7_tmap_1(sK3,u1_struct_0(sK4)) != k9_tmap_1(sK3,sK4)
% 3.04/0.99      | k9_tmap_1(sK3,sK4) = k7_tmap_1(sK3,u1_struct_0(sK4))
% 3.04/0.99      | k9_tmap_1(sK3,sK4) != k9_tmap_1(sK3,sK4) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_4299]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3,plain,
% 3.04/0.99      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
% 3.04/0.99      | ~ v1_funct_2(X5,X2,X3)
% 3.04/0.99      | ~ v1_funct_2(X4,X0,X1)
% 3.04/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.04/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.04/0.99      | ~ v1_funct_1(X5)
% 3.04/0.99      | ~ v1_funct_1(X4)
% 3.04/0.99      | v1_xboole_0(X1)
% 3.04/0.99      | v1_xboole_0(X3)
% 3.04/0.99      | X4 = X5 ),
% 3.04/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_22,plain,
% 3.04/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.04/0.99      | m1_subset_1(k9_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X0)))))
% 3.04/0.99      | ~ v2_pre_topc(X1)
% 3.04/0.99      | v2_struct_0(X1)
% 3.04/0.99      | ~ l1_pre_topc(X1) ),
% 3.04/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_34,negated_conjecture,
% 3.04/0.99      ( m1_pre_topc(sK4,sK3)
% 3.04/0.99      | m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) ),
% 3.04/0.99      inference(cnf_transformation,[],[f103]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_42,negated_conjecture,
% 3.04/0.99      ( m1_pre_topc(sK4,sK3) ),
% 3.04/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_274,negated_conjecture,
% 3.04/0.99      ( m1_pre_topc(sK4,sK3) ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_34,c_42]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1260,plain,
% 3.04/0.99      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 3.04/0.99      | ~ v2_pre_topc(X0)
% 3.04/0.99      | v2_struct_0(X0)
% 3.04/0.99      | ~ l1_pre_topc(X0)
% 3.04/0.99      | sK4 != X1
% 3.04/0.99      | sK3 != X0 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_274]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1261,plain,
% 3.04/0.99      ( m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 3.04/0.99      | ~ v2_pre_topc(sK3)
% 3.04/0.99      | v2_struct_0(sK3)
% 3.04/0.99      | ~ l1_pre_topc(sK3) ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_1260]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1263,plain,
% 3.04/0.99      ( m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_1261,c_45,c_44,c_43]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_24,plain,
% 3.04/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.04/0.99      | ~ v2_pre_topc(X1)
% 3.04/0.99      | v1_funct_1(k9_tmap_1(X1,X0))
% 3.04/0.99      | v2_struct_0(X1)
% 3.04/0.99      | ~ l1_pre_topc(X1) ),
% 3.04/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1247,plain,
% 3.04/0.99      ( ~ v2_pre_topc(X0)
% 3.04/0.99      | v1_funct_1(k9_tmap_1(X0,X1))
% 3.04/0.99      | v2_struct_0(X0)
% 3.04/0.99      | ~ l1_pre_topc(X0)
% 3.04/0.99      | sK4 != X1
% 3.04/0.99      | sK3 != X0 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_274]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1248,plain,
% 3.04/0.99      ( ~ v2_pre_topc(sK3)
% 3.04/0.99      | v1_funct_1(k9_tmap_1(sK3,sK4))
% 3.04/0.99      | v2_struct_0(sK3)
% 3.04/0.99      | ~ l1_pre_topc(sK3) ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_1247]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1250,plain,
% 3.04/0.99      ( v1_funct_1(k9_tmap_1(sK3,sK4)) ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_1248,c_45,c_44,c_43]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_32,plain,
% 3.04/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.04/0.99      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.04/0.99      | ~ l1_pre_topc(X1) ),
% 3.04/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1234,plain,
% 3.04/0.99      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.04/0.99      | ~ l1_pre_topc(X1)
% 3.04/0.99      | sK4 != X0
% 3.04/0.99      | sK3 != X1 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_32,c_274]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1235,plain,
% 3.04/0.99      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.99      | ~ l1_pre_topc(sK3) ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_1234]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1237,plain,
% 3.04/0.99      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_1235,c_43]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_11,plain,
% 3.04/0.99      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
% 3.04/0.99      | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 3.04/0.99      | ~ m1_pre_topc(X1,X0)
% 3.04/0.99      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 3.04/0.99      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
% 3.04/0.99      | ~ v2_pre_topc(X0)
% 3.04/0.99      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 3.04/0.99      | v2_struct_0(X0)
% 3.04/0.99      | ~ l1_pre_topc(X0) ),
% 3.04/0.99      inference(cnf_transformation,[],[f109]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_23,plain,
% 3.04/0.99      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 3.04/0.99      | ~ m1_pre_topc(X1,X0)
% 3.04/0.99      | ~ v2_pre_topc(X0)
% 3.04/0.99      | v2_struct_0(X0)
% 3.04/0.99      | ~ l1_pre_topc(X0) ),
% 3.04/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_329,plain,
% 3.04/0.99      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
% 3.04/0.99      | ~ m1_pre_topc(X1,X0)
% 3.04/0.99      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 3.04/0.99      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
% 3.04/0.99      | ~ v2_pre_topc(X0)
% 3.04/0.99      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 3.04/0.99      | v2_struct_0(X0)
% 3.04/0.99      | ~ l1_pre_topc(X0) ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_11,c_23]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1128,plain,
% 3.04/0.99      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
% 3.04/0.99      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 3.04/0.99      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
% 3.04/0.99      | ~ v2_pre_topc(X0)
% 3.04/0.99      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 3.04/0.99      | v2_struct_0(X0)
% 3.04/0.99      | ~ l1_pre_topc(X0)
% 3.04/0.99      | sK4 != X1
% 3.04/0.99      | sK3 != X0 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_329,c_274]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1129,plain,
% 3.04/0.99      ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)))
% 3.04/0.99      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 3.04/0.99      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.99      | ~ v2_pre_topc(sK3)
% 3.04/0.99      | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
% 3.04/0.99      | v2_struct_0(sK3)
% 3.04/0.99      | ~ l1_pre_topc(sK3) ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_1128]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1131,plain,
% 3.04/0.99      ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.99      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 3.04/0.99      | r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)))
% 3.04/0.99      | ~ v1_funct_1(k9_tmap_1(sK3,sK4)) ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_1129,c_45,c_44,c_43]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1132,plain,
% 3.04/0.99      ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)))
% 3.04/0.99      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 3.04/0.99      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.99      | ~ v1_funct_1(k9_tmap_1(sK3,sK4)) ),
% 3.04/0.99      inference(renaming,[status(thm)],[c_1131]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1244,plain,
% 3.04/0.99      ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)))
% 3.04/0.99      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 3.04/0.99      | ~ v1_funct_1(k9_tmap_1(sK3,sK4)) ),
% 3.04/0.99      inference(backward_subsumption_resolution,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_1237,c_1132]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1257,plain,
% 3.04/0.99      ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)))
% 3.04/0.99      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) ),
% 3.04/0.99      inference(backward_subsumption_resolution,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_1250,c_1244]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1270,plain,
% 3.04/0.99      ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4))) ),
% 3.04/0.99      inference(backward_subsumption_resolution,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_1263,c_1257]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2188,plain,
% 3.04/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.04/0.99      | ~ v1_funct_2(X3,X4,X5)
% 3.04/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.04/0.99      | ~ v1_funct_1(X0)
% 3.04/0.99      | ~ v1_funct_1(X3)
% 3.04/0.99      | v1_xboole_0(X2)
% 3.04/0.99      | v1_xboole_0(X5)
% 3.04/0.99      | X3 = X0
% 3.04/0.99      | k7_tmap_1(sK3,u1_struct_0(sK4)) != X3
% 3.04/0.99      | k9_tmap_1(sK3,sK4) != X0
% 3.04/0.99      | u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))) != X5
% 3.04/0.99      | u1_struct_0(k8_tmap_1(sK3,sK4)) != X2
% 3.04/0.99      | u1_struct_0(sK3) != X4
% 3.04/0.99      | u1_struct_0(sK3) != X1 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_1270]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2189,plain,
% 3.04/0.99      ( ~ v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
% 3.04/0.99      | ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 3.04/0.99      | ~ m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))))
% 3.04/0.99      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 3.04/0.99      | ~ v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4)))
% 3.04/0.99      | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
% 3.04/0.99      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
% 3.04/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4)))
% 3.04/0.99      | k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4) ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_2188]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1148,plain,
% 3.04/0.99      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 3.04/0.99      | ~ v2_pre_topc(X0)
% 3.04/0.99      | v2_struct_0(X0)
% 3.04/0.99      | ~ l1_pre_topc(X0)
% 3.04/0.99      | sK4 != X1
% 3.04/0.99      | sK3 != X0 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_274]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1149,plain,
% 3.04/0.99      ( v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 3.04/0.99      | ~ v2_pre_topc(sK3)
% 3.04/0.99      | v2_struct_0(sK3)
% 3.04/0.99      | ~ l1_pre_topc(sK3) ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_1148]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2191,plain,
% 3.04/0.99      ( ~ v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4)))
% 3.04/0.99      | ~ v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
% 3.04/0.99      | ~ m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))))
% 3.04/0.99      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
% 3.04/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4)))
% 3.04/0.99      | k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4) ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_2189,c_45,c_44,c_43,c_1149,c_1248,c_1261]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2192,plain,
% 3.04/0.99      ( ~ v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
% 3.04/0.99      | ~ m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))))
% 3.04/0.99      | ~ v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4)))
% 3.04/0.99      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
% 3.04/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4)))
% 3.04/0.99      | k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4) ),
% 3.04/0.99      inference(renaming,[status(thm)],[c_2191]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3037,plain,
% 3.04/0.99      ( ~ v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
% 3.04/0.99      | ~ m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))))
% 3.04/0.99      | ~ v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4)))
% 3.04/0.99      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
% 3.04/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4)))
% 3.04/0.99      | k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4) ),
% 3.04/0.99      inference(subtyping,[status(esa)],[c_2192]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3646,plain,
% 3.04/0.99      ( k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4)
% 3.04/0.99      | v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))) != iProver_top
% 3.04/0.99      | m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))))) != iProver_top
% 3.04/0.99      | v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4))) != iProver_top
% 3.04/0.99      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))) = iProver_top
% 3.04/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4))) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_3037]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_46,plain,
% 3.04/0.99      ( v2_struct_0(sK3) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_48,plain,
% 3.04/0.99      ( l1_pre_topc(sK3) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1,plain,
% 3.04/0.99      ( v2_struct_0(X0)
% 3.04/0.99      | ~ v1_xboole_0(u1_struct_0(X0))
% 3.04/0.99      | ~ l1_struct_0(X0) ),
% 3.04/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_152,plain,
% 3.04/0.99      ( v2_struct_0(X0) = iProver_top
% 3.04/0.99      | v1_xboole_0(u1_struct_0(X0)) != iProver_top
% 3.04/0.99      | l1_struct_0(X0) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_154,plain,
% 3.04/0.99      ( v2_struct_0(sK3) = iProver_top
% 3.04/0.99      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top
% 3.04/0.99      | l1_struct_0(sK3) != iProver_top ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_152]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_0,plain,
% 3.04/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.04/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_155,plain,
% 3.04/0.99      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_157,plain,
% 3.04/0.99      ( l1_pre_topc(sK3) != iProver_top
% 3.04/0.99      | l1_struct_0(sK3) = iProver_top ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_155]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1236,plain,
% 3.04/0.99      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 3.04/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_1235]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3073,plain,
% 3.04/0.99      ( u1_struct_0(X0_56) = u1_struct_0(X1_56) | X0_56 != X1_56 ),
% 3.04/0.99      theory(equality) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3092,plain,
% 3.04/0.99      ( u1_struct_0(sK3) = u1_struct_0(sK3) | sK3 != sK3 ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_3073]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3065,plain,( X0_56 = X0_56 ),theory(equality) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3111,plain,
% 3.04/0.99      ( sK3 = sK3 ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_3065]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3168,plain,
% 3.04/0.99      ( k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4)
% 3.04/0.99      | v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))) != iProver_top
% 3.04/0.99      | m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))))) != iProver_top
% 3.04/0.99      | v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4))) != iProver_top
% 3.04/0.99      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))) = iProver_top
% 3.04/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4))) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_3037]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_21,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.04/0.99      | ~ v2_pre_topc(X1)
% 3.04/0.99      | v1_funct_1(k7_tmap_1(X1,X0))
% 3.04/0.99      | v2_struct_0(X1)
% 3.04/0.99      | ~ l1_pre_topc(X1) ),
% 3.04/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1828,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.04/0.99      | ~ v2_pre_topc(X1)
% 3.04/0.99      | v1_funct_1(k7_tmap_1(X1,X0))
% 3.04/0.99      | ~ l1_pre_topc(X1)
% 3.04/0.99      | sK3 != X1 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_45]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1829,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.99      | ~ v2_pre_topc(sK3)
% 3.04/0.99      | v1_funct_1(k7_tmap_1(sK3,X0))
% 3.04/0.99      | ~ l1_pre_topc(sK3) ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_1828]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1833,plain,
% 3.04/0.99      ( v1_funct_1(k7_tmap_1(sK3,X0))
% 3.04/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_1829,c_44,c_43]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1834,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.99      | v1_funct_1(k7_tmap_1(sK3,X0)) ),
% 3.04/0.99      inference(renaming,[status(thm)],[c_1833]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3046,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.99      | v1_funct_1(k7_tmap_1(sK3,X0_57)) ),
% 3.04/0.99      inference(subtyping,[status(esa)],[c_1834]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3864,plain,
% 3.04/0.99      ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.99      | v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4))) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_3046]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3865,plain,
% 3.04/0.99      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.04/0.99      | v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4))) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_3864]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3870,plain,
% 3.04/0.99      ( m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))))
% 3.04/0.99      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_3045]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3871,plain,
% 3.04/0.99      ( m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))))) = iProver_top
% 3.04/0.99      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_3870]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_20,plain,
% 3.04/0.99      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
% 3.04/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.04/0.99      | ~ v2_pre_topc(X0)
% 3.04/0.99      | v2_struct_0(X0)
% 3.04/0.99      | ~ l1_pre_topc(X0) ),
% 3.04/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1774,plain,
% 3.04/0.99      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
% 3.04/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.04/0.99      | ~ v2_pre_topc(X0)
% 3.04/0.99      | ~ l1_pre_topc(X0)
% 3.04/0.99      | sK3 != X0 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_45]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1775,plain,
% 3.04/0.99      ( v1_funct_2(k7_tmap_1(sK3,X0),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))
% 3.04/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.99      | ~ v2_pre_topc(sK3)
% 3.04/0.99      | ~ l1_pre_topc(sK3) ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_1774]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1779,plain,
% 3.04/0.99      ( v1_funct_2(k7_tmap_1(sK3,X0),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))
% 3.04/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_1775,c_44,c_43]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3049,plain,
% 3.04/0.99      ( v1_funct_2(k7_tmap_1(sK3,X0_57),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0_57)))
% 3.04/0.99      | ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.04/0.99      inference(subtyping,[status(esa)],[c_1779]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3873,plain,
% 3.04/0.99      ( v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))))
% 3.04/0.99      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_3049]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3874,plain,
% 3.04/0.99      ( v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))) = iProver_top
% 3.04/0.99      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_3873]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3074,plain,
% 3.04/0.99      ( ~ v1_xboole_0(X0_57) | v1_xboole_0(X1_57) | X1_57 != X0_57 ),
% 3.04/0.99      theory(equality) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4014,plain,
% 3.04/0.99      ( v1_xboole_0(X0_57)
% 3.04/0.99      | ~ v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4)))
% 3.04/0.99      | X0_57 != u1_struct_0(k8_tmap_1(sK3,sK4)) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_3074]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4165,plain,
% 3.04/0.99      ( v1_xboole_0(u1_struct_0(X0_56))
% 3.04/0.99      | ~ v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4)))
% 3.04/0.99      | u1_struct_0(X0_56) != u1_struct_0(k8_tmap_1(sK3,sK4)) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_4014]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4167,plain,
% 3.04/0.99      ( u1_struct_0(X0_56) != u1_struct_0(k8_tmap_1(sK3,sK4))
% 3.04/0.99      | v1_xboole_0(u1_struct_0(X0_56)) = iProver_top
% 3.04/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_4165]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4169,plain,
% 3.04/0.99      ( u1_struct_0(sK3) != u1_struct_0(k8_tmap_1(sK3,sK4))
% 3.04/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
% 3.04/0.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_4167]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_7,plain,
% 3.04/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.04/0.99      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.04/0.99      | ~ v1_pre_topc(k8_tmap_1(X1,X0))
% 3.04/0.99      | ~ v2_pre_topc(X1)
% 3.04/0.99      | ~ v2_pre_topc(k8_tmap_1(X1,X0))
% 3.04/0.99      | v2_struct_0(X1)
% 3.04/0.99      | ~ l1_pre_topc(X1)
% 3.04/0.99      | ~ l1_pre_topc(k8_tmap_1(X1,X0))
% 3.04/0.99      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 3.04/0.99      inference(cnf_transformation,[],[f107]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_339,plain,
% 3.04/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.04/0.99      | ~ v1_pre_topc(k8_tmap_1(X1,X0))
% 3.04/0.99      | ~ v2_pre_topc(X1)
% 3.04/0.99      | ~ v2_pre_topc(k8_tmap_1(X1,X0))
% 3.04/0.99      | v2_struct_0(X1)
% 3.04/0.99      | ~ l1_pre_topc(X1)
% 3.04/0.99      | ~ l1_pre_topc(k8_tmap_1(X1,X0))
% 3.04/0.99      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_7,c_32]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1200,plain,
% 3.04/0.99      ( ~ v1_pre_topc(k8_tmap_1(X0,X1))
% 3.04/0.99      | ~ v2_pre_topc(X0)
% 3.04/0.99      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
% 3.04/0.99      | v2_struct_0(X0)
% 3.04/0.99      | ~ l1_pre_topc(X0)
% 3.04/0.99      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
% 3.04/0.99      | k6_tmap_1(X0,u1_struct_0(X1)) = k8_tmap_1(X0,X1)
% 3.04/0.99      | sK4 != X1
% 3.04/0.99      | sK3 != X0 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_339,c_274]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1201,plain,
% 3.04/0.99      ( ~ v1_pre_topc(k8_tmap_1(sK3,sK4))
% 3.04/0.99      | ~ v2_pre_topc(k8_tmap_1(sK3,sK4))
% 3.04/0.99      | ~ v2_pre_topc(sK3)
% 3.04/0.99      | v2_struct_0(sK3)
% 3.04/0.99      | ~ l1_pre_topc(k8_tmap_1(sK3,sK4))
% 3.04/0.99      | ~ l1_pre_topc(sK3)
% 3.04/0.99      | k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4) ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_1200]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1203,plain,
% 3.04/0.99      ( ~ l1_pre_topc(k8_tmap_1(sK3,sK4))
% 3.04/0.99      | ~ v2_pre_topc(k8_tmap_1(sK3,sK4))
% 3.04/0.99      | ~ v1_pre_topc(k8_tmap_1(sK3,sK4))
% 3.04/0.99      | k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4) ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_1201,c_45,c_44,c_43]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1204,plain,
% 3.04/0.99      ( ~ v1_pre_topc(k8_tmap_1(sK3,sK4))
% 3.04/0.99      | ~ v2_pre_topc(k8_tmap_1(sK3,sK4))
% 3.04/0.99      | ~ l1_pre_topc(k8_tmap_1(sK3,sK4))
% 3.04/0.99      | k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4) ),
% 3.04/0.99      inference(renaming,[status(thm)],[c_1203]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_18,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.04/0.99      | v1_pre_topc(k6_tmap_1(X1,X0))
% 3.04/0.99      | ~ v2_pre_topc(X1)
% 3.04/0.99      | v2_struct_0(X1)
% 3.04/0.99      | ~ l1_pre_topc(X1) ),
% 3.04/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1864,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.04/0.99      | v1_pre_topc(k6_tmap_1(X1,X0))
% 3.04/0.99      | ~ v2_pre_topc(X1)
% 3.04/0.99      | ~ l1_pre_topc(X1)
% 3.04/0.99      | sK3 != X1 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_45]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1865,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.99      | v1_pre_topc(k6_tmap_1(sK3,X0))
% 3.04/0.99      | ~ v2_pre_topc(sK3)
% 3.04/0.99      | ~ l1_pre_topc(sK3) ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_1864]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1869,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.99      | v1_pre_topc(k6_tmap_1(sK3,X0)) ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_1865,c_44,c_43]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2007,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.99      | ~ v2_pre_topc(k8_tmap_1(sK3,sK4))
% 3.04/0.99      | ~ l1_pre_topc(k8_tmap_1(sK3,sK4))
% 3.04/0.99      | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
% 3.04/0.99      | k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4) ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_1204,c_1869]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3039,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.99      | ~ v2_pre_topc(k8_tmap_1(sK3,sK4))
% 3.04/0.99      | ~ l1_pre_topc(k8_tmap_1(sK3,sK4))
% 3.04/0.99      | k6_tmap_1(sK3,X0_57) != k8_tmap_1(sK3,sK4)
% 3.04/0.99      | k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4) ),
% 3.04/0.99      inference(subtyping,[status(esa)],[c_2007]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3063,plain,
% 3.04/0.99      ( ~ v2_pre_topc(k8_tmap_1(sK3,sK4))
% 3.04/0.99      | ~ l1_pre_topc(k8_tmap_1(sK3,sK4))
% 3.04/0.99      | sP0_iProver_split
% 3.04/0.99      | k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4) ),
% 3.04/0.99      inference(splitting,
% 3.04/0.99                [splitting(split),new_symbols(definition,[])],
% 3.04/0.99                [c_3039]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3643,plain,
% 3.04/0.99      ( k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4)
% 3.04/0.99      | v2_pre_topc(k8_tmap_1(sK3,sK4)) != iProver_top
% 3.04/0.99      | l1_pre_topc(k8_tmap_1(sK3,sK4)) != iProver_top
% 3.04/0.99      | sP0_iProver_split = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_3063]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3058,plain,
% 3.04/0.99      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.04/0.99      inference(subtyping,[status(esa)],[c_1237]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3624,plain,
% 3.04/0.99      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_3058]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_5,plain,
% 3.04/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.04/0.99      | ~ v1_pre_topc(X2)
% 3.04/0.99      | ~ v2_pre_topc(X2)
% 3.04/0.99      | ~ v2_pre_topc(X1)
% 3.04/0.99      | v2_struct_0(X1)
% 3.04/0.99      | ~ l1_pre_topc(X1)
% 3.04/0.99      | ~ l1_pre_topc(X2)
% 3.04/0.99      | sK0(X1,X0,X2) = u1_struct_0(X0)
% 3.04/0.99      | k8_tmap_1(X1,X0) = X2 ),
% 3.04/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1328,plain,
% 3.04/0.99      ( ~ v1_pre_topc(X0)
% 3.04/0.99      | ~ v2_pre_topc(X0)
% 3.04/0.99      | ~ v2_pre_topc(X1)
% 3.04/0.99      | v2_struct_0(X1)
% 3.04/0.99      | ~ l1_pre_topc(X0)
% 3.04/0.99      | ~ l1_pre_topc(X1)
% 3.04/0.99      | sK0(X1,X2,X0) = u1_struct_0(X2)
% 3.04/0.99      | k8_tmap_1(X1,X2) = X0
% 3.04/0.99      | sK4 != X2
% 3.04/0.99      | sK3 != X1 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_274]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1329,plain,
% 3.04/0.99      ( ~ v1_pre_topc(X0)
% 3.04/0.99      | ~ v2_pre_topc(X0)
% 3.04/0.99      | ~ v2_pre_topc(sK3)
% 3.04/0.99      | v2_struct_0(sK3)
% 3.04/0.99      | ~ l1_pre_topc(X0)
% 3.04/0.99      | ~ l1_pre_topc(sK3)
% 3.04/0.99      | sK0(sK3,sK4,X0) = u1_struct_0(sK4)
% 3.04/0.99      | k8_tmap_1(sK3,sK4) = X0 ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_1328]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1333,plain,
% 3.04/0.99      ( ~ l1_pre_topc(X0)
% 3.04/0.99      | ~ v2_pre_topc(X0)
% 3.04/0.99      | ~ v1_pre_topc(X0)
% 3.04/0.99      | sK0(sK3,sK4,X0) = u1_struct_0(sK4)
% 3.04/0.99      | k8_tmap_1(sK3,sK4) = X0 ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_1329,c_45,c_44,c_43]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1334,plain,
% 3.04/0.99      ( ~ v1_pre_topc(X0)
% 3.04/0.99      | ~ v2_pre_topc(X0)
% 3.04/0.99      | ~ l1_pre_topc(X0)
% 3.04/0.99      | sK0(sK3,sK4,X0) = u1_struct_0(sK4)
% 3.04/0.99      | k8_tmap_1(sK3,sK4) = X0 ),
% 3.04/0.99      inference(renaming,[status(thm)],[c_1333]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1965,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.99      | ~ v2_pre_topc(X1)
% 3.04/0.99      | ~ l1_pre_topc(X1)
% 3.04/0.99      | sK0(sK3,sK4,X1) = u1_struct_0(sK4)
% 3.04/0.99      | k6_tmap_1(sK3,X0) != X1
% 3.04/0.99      | k8_tmap_1(sK3,sK4) = X1 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_1334,c_1869]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1966,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.99      | ~ v2_pre_topc(k6_tmap_1(sK3,X0))
% 3.04/0.99      | ~ l1_pre_topc(k6_tmap_1(sK3,X0))
% 3.04/0.99      | sK0(sK3,sK4,k6_tmap_1(sK3,X0)) = u1_struct_0(sK4)
% 3.04/0.99      | k8_tmap_1(sK3,sK4) = k6_tmap_1(sK3,X0) ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_1965]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_17,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.04/0.99      | ~ v2_pre_topc(X1)
% 3.04/0.99      | v2_pre_topc(k6_tmap_1(X1,X0))
% 3.04/0.99      | v2_struct_0(X1)
% 3.04/0.99      | ~ l1_pre_topc(X1) ),
% 3.04/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1882,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.04/0.99      | ~ v2_pre_topc(X1)
% 3.04/0.99      | v2_pre_topc(k6_tmap_1(X1,X0))
% 3.04/0.99      | ~ l1_pre_topc(X1)
% 3.04/0.99      | sK3 != X1 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_45]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1883,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.99      | v2_pre_topc(k6_tmap_1(sK3,X0))
% 3.04/0.99      | ~ v2_pre_topc(sK3)
% 3.04/0.99      | ~ l1_pre_topc(sK3) ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_1882]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_16,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.04/0.99      | ~ v2_pre_topc(X1)
% 3.04/0.99      | v2_struct_0(X1)
% 3.04/0.99      | ~ l1_pre_topc(X1)
% 3.04/0.99      | l1_pre_topc(k6_tmap_1(X1,X0)) ),
% 3.04/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1900,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.04/0.99      | ~ v2_pre_topc(X1)
% 3.04/0.99      | ~ l1_pre_topc(X1)
% 3.04/0.99      | l1_pre_topc(k6_tmap_1(X1,X0))
% 3.04/0.99      | sK3 != X1 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_45]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1901,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.99      | ~ v2_pre_topc(sK3)
% 3.04/0.99      | l1_pre_topc(k6_tmap_1(sK3,X0))
% 3.04/0.99      | ~ l1_pre_topc(sK3) ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_1900]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1970,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.99      | sK0(sK3,sK4,k6_tmap_1(sK3,X0)) = u1_struct_0(sK4)
% 3.04/0.99      | k8_tmap_1(sK3,sK4) = k6_tmap_1(sK3,X0) ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_1966,c_44,c_43,c_1883,c_1901]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3041,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.99      | sK0(sK3,sK4,k6_tmap_1(sK3,X0_57)) = u1_struct_0(sK4)
% 3.04/0.99      | k8_tmap_1(sK3,sK4) = k6_tmap_1(sK3,X0_57) ),
% 3.04/0.99      inference(subtyping,[status(esa)],[c_1970]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3641,plain,
% 3.04/0.99      ( sK0(sK3,sK4,k6_tmap_1(sK3,X0_57)) = u1_struct_0(sK4)
% 3.04/0.99      | k8_tmap_1(sK3,sK4) = k6_tmap_1(sK3,X0_57)
% 3.04/0.99      | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_3041]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4857,plain,
% 3.04/0.99      ( sK0(sK3,sK4,k6_tmap_1(sK3,u1_struct_0(sK4))) = u1_struct_0(sK4)
% 3.04/0.99      | k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4) ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_3624,c_3641]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4,plain,
% 3.04/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.04/0.99      | ~ v1_pre_topc(X2)
% 3.04/0.99      | ~ v2_pre_topc(X2)
% 3.04/0.99      | ~ v2_pre_topc(X1)
% 3.04/0.99      | v2_struct_0(X1)
% 3.04/0.99      | ~ l1_pre_topc(X1)
% 3.04/0.99      | ~ l1_pre_topc(X2)
% 3.04/0.99      | k6_tmap_1(X1,sK0(X1,X0,X2)) != X2
% 3.04/0.99      | k8_tmap_1(X1,X0) = X2 ),
% 3.04/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1355,plain,
% 3.04/0.99      ( ~ v1_pre_topc(X0)
% 3.04/0.99      | ~ v2_pre_topc(X0)
% 3.04/0.99      | ~ v2_pre_topc(X1)
% 3.04/0.99      | v2_struct_0(X1)
% 3.04/0.99      | ~ l1_pre_topc(X0)
% 3.04/0.99      | ~ l1_pre_topc(X1)
% 3.04/0.99      | k6_tmap_1(X1,sK0(X1,X2,X0)) != X0
% 3.04/0.99      | k8_tmap_1(X1,X2) = X0
% 3.04/0.99      | sK4 != X2
% 3.04/0.99      | sK3 != X1 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_274]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1356,plain,
% 3.04/0.99      ( ~ v1_pre_topc(X0)
% 3.04/0.99      | ~ v2_pre_topc(X0)
% 3.04/0.99      | ~ v2_pre_topc(sK3)
% 3.04/0.99      | v2_struct_0(sK3)
% 3.04/0.99      | ~ l1_pre_topc(X0)
% 3.04/0.99      | ~ l1_pre_topc(sK3)
% 3.04/0.99      | k6_tmap_1(sK3,sK0(sK3,sK4,X0)) != X0
% 3.04/0.99      | k8_tmap_1(sK3,sK4) = X0 ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_1355]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1360,plain,
% 3.04/0.99      ( ~ l1_pre_topc(X0)
% 3.04/0.99      | ~ v2_pre_topc(X0)
% 3.04/0.99      | ~ v1_pre_topc(X0)
% 3.04/0.99      | k6_tmap_1(sK3,sK0(sK3,sK4,X0)) != X0
% 3.04/0.99      | k8_tmap_1(sK3,sK4) = X0 ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_1356,c_45,c_44,c_43]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1361,plain,
% 3.04/0.99      ( ~ v1_pre_topc(X0)
% 3.04/0.99      | ~ v2_pre_topc(X0)
% 3.04/0.99      | ~ l1_pre_topc(X0)
% 3.04/0.99      | k6_tmap_1(sK3,sK0(sK3,sK4,X0)) != X0
% 3.04/0.99      | k8_tmap_1(sK3,sK4) = X0 ),
% 3.04/0.99      inference(renaming,[status(thm)],[c_1360]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1944,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.99      | ~ v2_pre_topc(X1)
% 3.04/0.99      | ~ l1_pre_topc(X1)
% 3.04/0.99      | k6_tmap_1(sK3,X0) != X1
% 3.04/0.99      | k6_tmap_1(sK3,sK0(sK3,sK4,X1)) != X1
% 3.04/0.99      | k8_tmap_1(sK3,sK4) = X1 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_1361,c_1869]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1945,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.99      | ~ v2_pre_topc(k6_tmap_1(sK3,X0))
% 3.04/0.99      | ~ l1_pre_topc(k6_tmap_1(sK3,X0))
% 3.04/0.99      | k6_tmap_1(sK3,sK0(sK3,sK4,k6_tmap_1(sK3,X0))) != k6_tmap_1(sK3,X0)
% 3.04/0.99      | k8_tmap_1(sK3,sK4) = k6_tmap_1(sK3,X0) ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_1944]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1949,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.99      | k6_tmap_1(sK3,sK0(sK3,sK4,k6_tmap_1(sK3,X0))) != k6_tmap_1(sK3,X0)
% 3.04/0.99      | k8_tmap_1(sK3,sK4) = k6_tmap_1(sK3,X0) ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_1945,c_44,c_43,c_1883,c_1901]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3042,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.99      | k6_tmap_1(sK3,sK0(sK3,sK4,k6_tmap_1(sK3,X0_57))) != k6_tmap_1(sK3,X0_57)
% 3.04/0.99      | k8_tmap_1(sK3,sK4) = k6_tmap_1(sK3,X0_57) ),
% 3.04/0.99      inference(subtyping,[status(esa)],[c_1949]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3640,plain,
% 3.04/0.99      ( k6_tmap_1(sK3,sK0(sK3,sK4,k6_tmap_1(sK3,X0_57))) != k6_tmap_1(sK3,X0_57)
% 3.04/0.99      | k8_tmap_1(sK3,sK4) = k6_tmap_1(sK3,X0_57)
% 3.04/0.99      | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_3042]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4928,plain,
% 3.04/0.99      ( k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4)
% 3.04/0.99      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_4857,c_3640]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_5009,plain,
% 3.04/0.99      ( k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4) ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_3643,c_48,c_1236,c_4928]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_26,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.04/0.99      | ~ v2_pre_topc(X1)
% 3.04/0.99      | v2_struct_0(X1)
% 3.04/0.99      | ~ l1_pre_topc(X1)
% 3.04/0.99      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
% 3.04/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1792,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.04/0.99      | ~ v2_pre_topc(X1)
% 3.04/0.99      | ~ l1_pre_topc(X1)
% 3.04/0.99      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1)
% 3.04/0.99      | sK3 != X1 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_45]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1793,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.99      | ~ v2_pre_topc(sK3)
% 3.04/0.99      | ~ l1_pre_topc(sK3)
% 3.04/0.99      | u1_struct_0(k6_tmap_1(sK3,X0)) = u1_struct_0(sK3) ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_1792]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1797,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.99      | u1_struct_0(k6_tmap_1(sK3,X0)) = u1_struct_0(sK3) ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_1793,c_44,c_43]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3048,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.99      | u1_struct_0(k6_tmap_1(sK3,X0_57)) = u1_struct_0(sK3) ),
% 3.04/0.99      inference(subtyping,[status(esa)],[c_1797]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3634,plain,
% 3.04/0.99      ( u1_struct_0(k6_tmap_1(sK3,X0_57)) = u1_struct_0(sK3)
% 3.04/0.99      | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_3048]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4096,plain,
% 3.04/0.99      ( u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))) = u1_struct_0(sK3) ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_3624,c_3634]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_5014,plain,
% 3.04/0.99      ( u1_struct_0(k8_tmap_1(sK3,sK4)) = u1_struct_0(sK3) ),
% 3.04/0.99      inference(demodulation,[status(thm)],[c_5009,c_4096]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4251,plain,
% 3.04/0.99      ( X0_57 != X1_57
% 3.04/0.99      | u1_struct_0(sK3) != X1_57
% 3.04/0.99      | u1_struct_0(sK3) = X0_57 ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_3070]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4533,plain,
% 3.04/0.99      ( X0_57 != u1_struct_0(sK3)
% 3.04/0.99      | u1_struct_0(sK3) = X0_57
% 3.04/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_4251]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4757,plain,
% 3.04/0.99      ( u1_struct_0(X0_56) != u1_struct_0(sK3)
% 3.04/0.99      | u1_struct_0(sK3) = u1_struct_0(X0_56)
% 3.04/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_4533]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_5327,plain,
% 3.04/0.99      ( u1_struct_0(k8_tmap_1(sK3,sK4)) != u1_struct_0(sK3)
% 3.04/0.99      | u1_struct_0(sK3) = u1_struct_0(k8_tmap_1(sK3,sK4))
% 3.04/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_4757]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_5445,plain,
% 3.04/0.99      ( v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))) = iProver_top
% 3.04/0.99      | k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4) ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_3646,c_46,c_48,c_154,c_157,c_1236,c_3092,c_3111,
% 3.04/0.99                 c_3168,c_3865,c_3871,c_3874,c_4169,c_5014,c_5327]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_5446,plain,
% 3.04/0.99      ( k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4)
% 3.04/0.99      | v1_xboole_0(u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4)))) = iProver_top ),
% 3.04/0.99      inference(renaming,[status(thm)],[c_5445]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_5449,plain,
% 3.04/0.99      ( k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4)
% 3.04/0.99      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4))) = iProver_top ),
% 3.04/0.99      inference(light_normalisation,[status(thm)],[c_5446,c_5009]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4059,plain,
% 3.04/0.99      ( X0_56 != X1_56
% 3.04/0.99      | k8_tmap_1(sK3,sK4) != X1_56
% 3.04/0.99      | k8_tmap_1(sK3,sK4) = X0_56 ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_3069]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4282,plain,
% 3.04/0.99      ( X0_56 != k8_tmap_1(sK3,sK4)
% 3.04/0.99      | k8_tmap_1(sK3,sK4) = X0_56
% 3.04/0.99      | k8_tmap_1(sK3,sK4) != k8_tmap_1(sK3,sK4) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_4059]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4590,plain,
% 3.04/0.99      ( k6_tmap_1(sK3,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4)
% 3.04/0.99      | k8_tmap_1(sK3,sK4) = k6_tmap_1(sK3,u1_struct_0(sK4))
% 3.04/0.99      | k8_tmap_1(sK3,sK4) != k8_tmap_1(sK3,sK4) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_4282]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4283,plain,
% 3.04/0.99      ( k8_tmap_1(sK3,sK4) = k8_tmap_1(sK3,sK4) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_3065]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3066,plain,( X0_57 = X0_57 ),theory(equality) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4020,plain,
% 3.04/0.99      ( k9_tmap_1(sK3,sK4) = k9_tmap_1(sK3,sK4) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_3066]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_27,plain,
% 3.04/0.99      ( ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
% 3.04/0.99      | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
% 3.04/0.99      | v3_pre_topc(X1,X0)
% 3.04/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.04/0.99      | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
% 3.04/0.99      | ~ v2_pre_topc(X0)
% 3.04/0.99      | ~ v1_funct_1(k7_tmap_1(X0,X1))
% 3.04/0.99      | v2_struct_0(X0)
% 3.04/0.99      | ~ l1_pre_topc(X0) ),
% 3.04/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_301,plain,
% 3.04/0.99      ( ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
% 3.04/0.99      | v3_pre_topc(X1,X0)
% 3.04/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.04/0.99      | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
% 3.04/0.99      | ~ v2_pre_topc(X0)
% 3.04/0.99      | ~ v1_funct_1(k7_tmap_1(X0,X1))
% 3.04/0.99      | v2_struct_0(X0)
% 3.04/0.99      | ~ l1_pre_topc(X0) ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_27,c_20]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_37,negated_conjecture,
% 3.04/0.99      ( v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4))
% 3.04/0.99      | v1_tsep_1(sK4,sK3) ),
% 3.04/0.99      inference(cnf_transformation,[],[f100]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_593,plain,
% 3.04/0.99      ( v3_pre_topc(X0,X1)
% 3.04/0.99      | v1_tsep_1(sK4,sK3)
% 3.04/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.04/0.99      | ~ m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
% 3.04/0.99      | ~ v2_pre_topc(X1)
% 3.04/0.99      | ~ v1_funct_1(k7_tmap_1(X1,X0))
% 3.04/0.99      | v2_struct_0(X1)
% 3.04/0.99      | ~ l1_pre_topc(X1)
% 3.04/0.99      | k7_tmap_1(X1,X0) != k9_tmap_1(sK3,sK4)
% 3.04/0.99      | k6_tmap_1(X1,X0) != k8_tmap_1(sK3,sK4)
% 3.04/0.99      | sK3 != X1 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_301,c_37]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_594,plain,
% 3.04/0.99      ( v3_pre_topc(X0,sK3)
% 3.04/0.99      | v1_tsep_1(sK4,sK3)
% 3.04/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.99      | ~ m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))))
% 3.04/0.99      | ~ v2_pre_topc(sK3)
% 3.04/0.99      | ~ v1_funct_1(k7_tmap_1(sK3,X0))
% 3.04/0.99      | v2_struct_0(sK3)
% 3.04/0.99      | ~ l1_pre_topc(sK3)
% 3.04/0.99      | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4)
% 3.04/0.99      | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4) ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_593]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_598,plain,
% 3.04/0.99      ( ~ m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))))
% 3.04/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.99      | v1_tsep_1(sK4,sK3)
% 3.04/0.99      | v3_pre_topc(X0,sK3)
% 3.04/0.99      | ~ v1_funct_1(k7_tmap_1(sK3,X0))
% 3.04/0.99      | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4)
% 3.04/0.99      | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4) ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_594,c_45,c_44,c_43]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_599,plain,
% 3.04/0.99      ( v3_pre_topc(X0,sK3)
% 3.04/0.99      | v1_tsep_1(sK4,sK3)
% 3.04/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.99      | ~ m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))))
% 3.04/0.99      | ~ v1_funct_1(k7_tmap_1(sK3,X0))
% 3.04/0.99      | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4)
% 3.04/0.99      | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4) ),
% 3.04/0.99      inference(renaming,[status(thm)],[c_598]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_12,plain,
% 3.04/0.99      ( ~ v3_pre_topc(sK2(X0,X1),X0)
% 3.04/0.99      | v1_tsep_1(X1,X0)
% 3.04/0.99      | ~ m1_pre_topc(X1,X0)
% 3.04/0.99      | ~ l1_pre_topc(X0) ),
% 3.04/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1159,plain,
% 3.04/0.99      ( ~ v3_pre_topc(sK2(X0,X1),X0)
% 3.04/0.99      | v1_tsep_1(X1,X0)
% 3.04/0.99      | ~ l1_pre_topc(X0)
% 3.04/0.99      | sK4 != X1
% 3.04/0.99      | sK3 != X0 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_274]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1160,plain,
% 3.04/0.99      ( ~ v3_pre_topc(sK2(sK3,sK4),sK3)
% 3.04/0.99      | v1_tsep_1(sK4,sK3)
% 3.04/0.99      | ~ l1_pre_topc(sK3) ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_1159]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1162,plain,
% 3.04/0.99      ( v1_tsep_1(sK4,sK3) | ~ v3_pre_topc(sK2(sK3,sK4),sK3) ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_1160,c_43]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1163,plain,
% 3.04/0.99      ( ~ v3_pre_topc(sK2(sK3,sK4),sK3) | v1_tsep_1(sK4,sK3) ),
% 3.04/0.99      inference(renaming,[status(thm)],[c_1162]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1512,plain,
% 3.04/0.99      ( v1_tsep_1(sK4,sK3)
% 3.04/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.99      | ~ m1_subset_1(k7_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,X0)))))
% 3.04/0.99      | ~ v1_funct_1(k7_tmap_1(sK3,X0))
% 3.04/0.99      | sK2(sK3,sK4) != X0
% 3.04/0.99      | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4)
% 3.04/0.99      | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
% 3.04/0.99      | sK3 != sK3 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_599,c_1163]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1513,plain,
% 3.04/0.99      ( v1_tsep_1(sK4,sK3)
% 3.04/0.99      | ~ m1_subset_1(sK2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.99      | ~ m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4))))))
% 3.04/0.99      | ~ v1_funct_1(k7_tmap_1(sK3,sK2(sK3,sK4)))
% 3.04/0.99      | k7_tmap_1(sK3,sK2(sK3,sK4)) != k9_tmap_1(sK3,sK4)
% 3.04/0.99      | k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4) ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_1512]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_14,plain,
% 3.04/0.99      ( v1_tsep_1(X0,X1)
% 3.04/0.99      | ~ m1_pre_topc(X0,X1)
% 3.04/0.99      | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.04/0.99      | ~ l1_pre_topc(X1) ),
% 3.04/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1273,plain,
% 3.04/0.99      ( v1_tsep_1(X0,X1)
% 3.04/0.99      | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.04/0.99      | ~ l1_pre_topc(X1)
% 3.04/0.99      | sK4 != X0
% 3.04/0.99      | sK3 != X1 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_274]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1274,plain,
% 3.04/0.99      ( v1_tsep_1(sK4,sK3)
% 3.04/0.99      | m1_subset_1(sK2(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.99      | ~ l1_pre_topc(sK3) ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_1273]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1515,plain,
% 3.04/0.99      ( v1_tsep_1(sK4,sK3)
% 3.04/0.99      | ~ m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4))))))
% 3.04/0.99      | ~ v1_funct_1(k7_tmap_1(sK3,sK2(sK3,sK4)))
% 3.04/0.99      | k7_tmap_1(sK3,sK2(sK3,sK4)) != k9_tmap_1(sK3,sK4)
% 3.04/0.99      | k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4) ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_1513,c_43,c_1274]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2314,plain,
% 3.04/0.99      ( v1_tsep_1(sK4,sK3)
% 3.04/0.99      | ~ m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4))))))
% 3.04/0.99      | k7_tmap_1(sK3,sK2(sK3,sK4)) != k9_tmap_1(sK3,sK4)
% 3.04/0.99      | k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4) ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_1250,c_1515]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3036,plain,
% 3.04/0.99      ( v1_tsep_1(sK4,sK3)
% 3.04/0.99      | ~ m1_subset_1(k7_tmap_1(sK3,sK2(sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,sK2(sK3,sK4))))))
% 3.04/0.99      | k7_tmap_1(sK3,sK2(sK3,sK4)) != k9_tmap_1(sK3,sK4)
% 3.04/0.99      | k6_tmap_1(sK3,sK2(sK3,sK4)) != k8_tmap_1(sK3,sK4) ),
% 3.04/0.99      inference(subtyping,[status(esa)],[c_2314]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1151,plain,
% 3.04/0.99      ( v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_1149,c_45,c_44,c_43]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_29,plain,
% 3.04/0.99      ( v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
% 3.04/0.99      | ~ v3_pre_topc(X1,X0)
% 3.04/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.04/0.99      | ~ v2_pre_topc(X0)
% 3.04/0.99      | v2_struct_0(X0)
% 3.04/0.99      | ~ l1_pre_topc(X0) ),
% 3.04/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_33,negated_conjecture,
% 3.04/0.99      ( ~ v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4))
% 3.04/0.99      | ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 3.04/0.99      | ~ v1_tsep_1(sK4,sK3)
% 3.04/0.99      | ~ m1_pre_topc(sK4,sK3)
% 3.04/0.99      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 3.04/0.99      | ~ v1_funct_1(k9_tmap_1(sK3,sK4)) ),
% 3.04/0.99      inference(cnf_transformation,[],[f104]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_279,plain,
% 3.04/0.99      ( ~ v1_tsep_1(sK4,sK3)
% 3.04/0.99      | ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 3.04/0.99      | ~ v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4))
% 3.04/0.99      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 3.04/0.99      | ~ v1_funct_1(k9_tmap_1(sK3,sK4)) ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_33,c_42]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_280,negated_conjecture,
% 3.04/0.99      ( ~ v5_pre_topc(k9_tmap_1(sK3,sK4),sK3,k8_tmap_1(sK3,sK4))
% 3.04/0.99      | ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 3.04/0.99      | ~ v1_tsep_1(sK4,sK3)
% 3.04/0.99      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 3.04/0.99      | ~ v1_funct_1(k9_tmap_1(sK3,sK4)) ),
% 3.04/0.99      inference(renaming,[status(thm)],[c_279]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_557,plain,
% 3.04/0.99      ( ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 3.04/0.99      | ~ v3_pre_topc(X0,X1)
% 3.04/0.99      | ~ v1_tsep_1(sK4,sK3)
% 3.04/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.04/0.99      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 3.04/0.99      | ~ v2_pre_topc(X1)
% 3.04/0.99      | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
% 3.04/0.99      | v2_struct_0(X1)
% 3.04/0.99      | ~ l1_pre_topc(X1)
% 3.04/0.99      | k7_tmap_1(X1,X0) != k9_tmap_1(sK3,sK4)
% 3.04/0.99      | k6_tmap_1(X1,X0) != k8_tmap_1(sK3,sK4)
% 3.04/0.99      | sK3 != X1 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_29,c_280]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_558,plain,
% 3.04/0.99      ( ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 3.04/0.99      | ~ v3_pre_topc(X0,sK3)
% 3.04/0.99      | ~ v1_tsep_1(sK4,sK3)
% 3.04/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.99      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 3.04/0.99      | ~ v2_pre_topc(sK3)
% 3.04/0.99      | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
% 3.04/0.99      | v2_struct_0(sK3)
% 3.04/0.99      | ~ l1_pre_topc(sK3)
% 3.04/0.99      | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4)
% 3.04/0.99      | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4) ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_557]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_562,plain,
% 3.04/0.99      ( ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 3.04/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.99      | ~ v1_tsep_1(sK4,sK3)
% 3.04/0.99      | ~ v3_pre_topc(X0,sK3)
% 3.04/0.99      | ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 3.04/0.99      | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
% 3.04/0.99      | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4)
% 3.04/0.99      | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4) ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_558,c_45,c_44,c_43]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_563,plain,
% 3.04/0.99      ( ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 3.04/0.99      | ~ v3_pre_topc(X0,sK3)
% 3.04/0.99      | ~ v1_tsep_1(sK4,sK3)
% 3.04/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.99      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 3.04/0.99      | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
% 3.04/0.99      | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4)
% 3.04/0.99      | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4) ),
% 3.04/0.99      inference(renaming,[status(thm)],[c_562]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1438,plain,
% 3.04/0.99      ( ~ v3_pre_topc(X0,sK3)
% 3.04/0.99      | ~ v1_tsep_1(sK4,sK3)
% 3.04/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.99      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 3.04/0.99      | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
% 3.04/0.99      | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4)
% 3.04/0.99      | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4) ),
% 3.04/0.99      inference(backward_subsumption_resolution,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_1151,c_563]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1463,plain,
% 3.04/0.99      ( ~ v3_pre_topc(X0,sK3)
% 3.04/0.99      | ~ v1_tsep_1(sK4,sK3)
% 3.04/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.99      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 3.04/0.99      | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4)
% 3.04/0.99      | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4) ),
% 3.04/0.99      inference(backward_subsumption_resolution,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_1250,c_1438]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1469,plain,
% 3.04/0.99      ( ~ v3_pre_topc(X0,sK3)
% 3.04/0.99      | ~ v1_tsep_1(sK4,sK3)
% 3.04/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.99      | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4)
% 3.04/0.99      | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4) ),
% 3.04/0.99      inference(backward_subsumption_resolution,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_1263,c_1463]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_15,plain,
% 3.04/0.99      ( v3_pre_topc(u1_struct_0(X0),X1)
% 3.04/0.99      | ~ v1_tsep_1(X0,X1)
% 3.04/0.99      | ~ m1_pre_topc(X0,X1)
% 3.04/0.99      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.04/0.99      | ~ l1_pre_topc(X1) ),
% 3.04/0.99      inference(cnf_transformation,[],[f110]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_319,plain,
% 3.04/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.04/0.99      | ~ v1_tsep_1(X0,X1)
% 3.04/0.99      | v3_pre_topc(u1_struct_0(X0),X1)
% 3.04/0.99      | ~ l1_pre_topc(X1) ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_15,c_32]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_320,plain,
% 3.04/0.99      ( v3_pre_topc(u1_struct_0(X0),X1)
% 3.04/0.99      | ~ v1_tsep_1(X0,X1)
% 3.04/0.99      | ~ m1_pre_topc(X0,X1)
% 3.04/0.99      | ~ l1_pre_topc(X1) ),
% 3.04/0.99      inference(renaming,[status(thm)],[c_319]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1220,plain,
% 3.04/0.99      ( v3_pre_topc(u1_struct_0(X0),X1)
% 3.04/0.99      | ~ v1_tsep_1(X0,X1)
% 3.04/0.99      | ~ l1_pre_topc(X1)
% 3.04/0.99      | sK4 != X0
% 3.04/0.99      | sK3 != X1 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_320,c_274]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1221,plain,
% 3.04/0.99      ( v3_pre_topc(u1_struct_0(sK4),sK3)
% 3.04/0.99      | ~ v1_tsep_1(sK4,sK3)
% 3.04/0.99      | ~ l1_pre_topc(sK3) ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_1220]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1223,plain,
% 3.04/0.99      ( ~ v1_tsep_1(sK4,sK3) | v3_pre_topc(u1_struct_0(sK4),sK3) ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_1221,c_43]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1224,plain,
% 3.04/0.99      ( v3_pre_topc(u1_struct_0(sK4),sK3) | ~ v1_tsep_1(sK4,sK3) ),
% 3.04/0.99      inference(renaming,[status(thm)],[c_1223]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1535,plain,
% 3.04/0.99      ( ~ v1_tsep_1(sK4,sK3)
% 3.04/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.99      | k7_tmap_1(sK3,X0) != k9_tmap_1(sK3,sK4)
% 3.04/0.99      | k6_tmap_1(sK3,X0) != k8_tmap_1(sK3,sK4)
% 3.04/0.99      | u1_struct_0(sK4) != X0
% 3.04/0.99      | sK3 != sK3 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_1469,c_1224]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1536,plain,
% 3.04/0.99      ( ~ v1_tsep_1(sK4,sK3)
% 3.04/0.99      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.99      | k7_tmap_1(sK3,u1_struct_0(sK4)) != k9_tmap_1(sK3,sK4)
% 3.04/0.99      | k6_tmap_1(sK3,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4) ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_1535]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1538,plain,
% 3.04/0.99      ( ~ v1_tsep_1(sK4,sK3)
% 3.04/0.99      | k7_tmap_1(sK3,u1_struct_0(sK4)) != k9_tmap_1(sK3,sK4)
% 3.04/0.99      | k6_tmap_1(sK3,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4) ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_1536,c_43,c_1235]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3051,plain,
% 3.04/0.99      ( ~ v1_tsep_1(sK4,sK3)
% 3.04/0.99      | k7_tmap_1(sK3,u1_struct_0(sK4)) != k9_tmap_1(sK3,sK4)
% 3.04/0.99      | k6_tmap_1(sK3,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4) ),
% 3.04/0.99      inference(subtyping,[status(esa)],[c_1538]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_13,plain,
% 3.04/0.99      ( v1_tsep_1(X0,X1)
% 3.04/0.99      | ~ m1_pre_topc(X0,X1)
% 3.04/0.99      | ~ l1_pre_topc(X1)
% 3.04/0.99      | sK2(X1,X0) = u1_struct_0(X0) ),
% 3.04/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1287,plain,
% 3.04/0.99      ( v1_tsep_1(X0,X1)
% 3.04/0.99      | ~ l1_pre_topc(X1)
% 3.04/0.99      | sK2(X1,X0) = u1_struct_0(X0)
% 3.04/0.99      | sK4 != X0
% 3.04/0.99      | sK3 != X1 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_274]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1288,plain,
% 3.04/0.99      ( v1_tsep_1(sK4,sK3)
% 3.04/0.99      | ~ l1_pre_topc(sK3)
% 3.04/0.99      | sK2(sK3,sK4) = u1_struct_0(sK4) ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_1287]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1290,plain,
% 3.04/0.99      ( v1_tsep_1(sK4,sK3) | sK2(sK3,sK4) = u1_struct_0(sK4) ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_1288,c_43]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3054,plain,
% 3.04/0.99      ( v1_tsep_1(sK4,sK3) | sK2(sK3,sK4) = u1_struct_0(sK4) ),
% 3.04/0.99      inference(subtyping,[status(esa)],[c_1290]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(contradiction,plain,
% 3.04/0.99      ( $false ),
% 3.04/0.99      inference(minisat,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_6891,c_6581,c_6121,c_6107,c_6106,c_6059,c_5449,c_5327,
% 3.04/0.99                 c_5014,c_4928,c_4590,c_4283,c_4169,c_4020,c_3036,c_3051,
% 3.04/0.99                 c_3054,c_3111,c_3092,c_1274,c_1236,c_157,c_154,c_48,
% 3.04/0.99                 c_43,c_46]) ).
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.04/0.99  
% 3.04/0.99  ------                               Statistics
% 3.04/0.99  
% 3.04/0.99  ------ General
% 3.04/0.99  
% 3.04/0.99  abstr_ref_over_cycles:                  0
% 3.04/0.99  abstr_ref_under_cycles:                 0
% 3.04/0.99  gc_basic_clause_elim:                   0
% 3.04/0.99  forced_gc_time:                         0
% 3.04/0.99  parsing_time:                           0.018
% 3.04/0.99  unif_index_cands_time:                  0.
% 3.04/0.99  unif_index_add_time:                    0.
% 3.04/0.99  orderings_time:                         0.
% 3.04/0.99  out_proof_time:                         0.017
% 3.04/0.99  total_time:                             0.241
% 3.04/0.99  num_of_symbols:                         67
% 3.04/0.99  num_of_terms:                           5188
% 3.04/0.99  
% 3.04/0.99  ------ Preprocessing
% 3.04/0.99  
% 3.04/0.99  num_of_splits:                          1
% 3.04/0.99  num_of_split_atoms:                     1
% 3.04/0.99  num_of_reused_defs:                     0
% 3.04/0.99  num_eq_ax_congr_red:                    18
% 3.04/0.99  num_of_sem_filtered_clauses:            6
% 3.04/0.99  num_of_subtypes:                        4
% 3.04/0.99  monotx_restored_types:                  0
% 3.04/0.99  sat_num_of_epr_types:                   0
% 3.04/0.99  sat_num_of_non_cyclic_types:            0
% 3.04/0.99  sat_guarded_non_collapsed_types:        1
% 3.04/0.99  num_pure_diseq_elim:                    0
% 3.04/0.99  simp_replaced_by:                       0
% 3.04/0.99  res_preprocessed:                       167
% 3.04/0.99  prep_upred:                             0
% 3.04/0.99  prep_unflattend:                        113
% 3.04/0.99  smt_new_axioms:                         0
% 3.04/0.99  pred_elim_cands:                        7
% 3.04/0.99  pred_elim:                              7
% 3.04/0.99  pred_elim_cl:                           13
% 3.04/0.99  pred_elim_cycles:                       21
% 3.04/0.99  merged_defs:                            0
% 3.04/0.99  merged_defs_ncl:                        0
% 3.04/0.99  bin_hyper_res:                          0
% 3.04/0.99  prep_cycles:                            4
% 3.04/0.99  pred_elim_time:                         0.079
% 3.04/0.99  splitting_time:                         0.
% 3.04/0.99  sem_filter_time:                        0.
% 3.04/0.99  monotx_time:                            0.
% 3.04/0.99  subtype_inf_time:                       0.
% 3.04/0.99  
% 3.04/0.99  ------ Problem properties
% 3.04/0.99  
% 3.04/0.99  clauses:                                27
% 3.04/0.99  conjectures:                            2
% 3.04/0.99  epr:                                    2
% 3.04/0.99  horn:                                   18
% 3.04/0.99  ground:                                 13
% 3.04/0.99  unary:                                  7
% 3.04/0.99  binary:                                 9
% 3.04/0.99  lits:                                   73
% 3.04/0.99  lits_eq:                                20
% 3.04/0.99  fd_pure:                                0
% 3.04/0.99  fd_pseudo:                              0
% 3.04/0.99  fd_cond:                                3
% 3.04/0.99  fd_pseudo_cond:                         0
% 3.04/0.99  ac_symbols:                             0
% 3.04/0.99  
% 3.04/0.99  ------ Propositional Solver
% 3.04/0.99  
% 3.04/0.99  prop_solver_calls:                      28
% 3.04/0.99  prop_fast_solver_calls:                 2038
% 3.04/0.99  smt_solver_calls:                       0
% 3.04/0.99  smt_fast_solver_calls:                  0
% 3.04/0.99  prop_num_of_clauses:                    1686
% 3.04/0.99  prop_preprocess_simplified:             6438
% 3.04/0.99  prop_fo_subsumed:                       117
% 3.04/0.99  prop_solver_time:                       0.
% 3.04/0.99  smt_solver_time:                        0.
% 3.04/0.99  smt_fast_solver_time:                   0.
% 3.04/0.99  prop_fast_solver_time:                  0.
% 3.04/0.99  prop_unsat_core_time:                   0.
% 3.04/0.99  
% 3.04/0.99  ------ QBF
% 3.04/0.99  
% 3.04/0.99  qbf_q_res:                              0
% 3.04/0.99  qbf_num_tautologies:                    0
% 3.04/0.99  qbf_prep_cycles:                        0
% 3.04/0.99  
% 3.04/0.99  ------ BMC1
% 3.04/0.99  
% 3.04/0.99  bmc1_current_bound:                     -1
% 3.04/0.99  bmc1_last_solved_bound:                 -1
% 3.04/0.99  bmc1_unsat_core_size:                   -1
% 3.04/0.99  bmc1_unsat_core_parents_size:           -1
% 3.04/0.99  bmc1_merge_next_fun:                    0
% 3.04/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.04/0.99  
% 3.04/0.99  ------ Instantiation
% 3.04/0.99  
% 3.04/0.99  inst_num_of_clauses:                    479
% 3.04/0.99  inst_num_in_passive:                    107
% 3.04/0.99  inst_num_in_active:                     296
% 3.04/0.99  inst_num_in_unprocessed:                75
% 3.04/0.99  inst_num_of_loops:                      329
% 3.04/0.99  inst_num_of_learning_restarts:          0
% 3.04/0.99  inst_num_moves_active_passive:          28
% 3.04/0.99  inst_lit_activity:                      0
% 3.04/0.99  inst_lit_activity_moves:                0
% 3.04/0.99  inst_num_tautologies:                   0
% 3.04/0.99  inst_num_prop_implied:                  0
% 3.04/0.99  inst_num_existing_simplified:           0
% 3.04/0.99  inst_num_eq_res_simplified:             0
% 3.04/0.99  inst_num_child_elim:                    0
% 3.04/0.99  inst_num_of_dismatching_blockings:      165
% 3.04/0.99  inst_num_of_non_proper_insts:           527
% 3.04/0.99  inst_num_of_duplicates:                 0
% 3.04/0.99  inst_inst_num_from_inst_to_res:         0
% 3.04/0.99  inst_dismatching_checking_time:         0.
% 3.04/0.99  
% 3.04/0.99  ------ Resolution
% 3.04/0.99  
% 3.04/0.99  res_num_of_clauses:                     0
% 3.04/0.99  res_num_in_passive:                     0
% 3.04/0.99  res_num_in_active:                      0
% 3.04/0.99  res_num_of_loops:                       171
% 3.04/0.99  res_forward_subset_subsumed:            140
% 3.04/0.99  res_backward_subset_subsumed:           5
% 3.04/0.99  res_forward_subsumed:                   1
% 3.04/0.99  res_backward_subsumed:                  3
% 3.04/0.99  res_forward_subsumption_resolution:     14
% 3.04/0.99  res_backward_subsumption_resolution:    6
% 3.04/0.99  res_clause_to_clause_subsumption:       335
% 3.04/0.99  res_orphan_elimination:                 0
% 3.04/0.99  res_tautology_del:                      124
% 3.04/0.99  res_num_eq_res_simplified:              0
% 3.04/0.99  res_num_sel_changes:                    0
% 3.04/0.99  res_moves_from_active_to_pass:          0
% 3.04/0.99  
% 3.04/0.99  ------ Superposition
% 3.04/0.99  
% 3.04/0.99  sup_time_total:                         0.
% 3.04/0.99  sup_time_generating:                    0.
% 3.04/0.99  sup_time_sim_full:                      0.
% 3.04/0.99  sup_time_sim_immed:                     0.
% 3.04/0.99  
% 3.04/0.99  sup_num_of_clauses:                     51
% 3.04/0.99  sup_num_in_active:                      38
% 3.04/0.99  sup_num_in_passive:                     13
% 3.04/0.99  sup_num_of_loops:                       64
% 3.04/0.99  sup_fw_superposition:                   28
% 3.04/0.99  sup_bw_superposition:                   30
% 3.04/0.99  sup_immediate_simplified:               21
% 3.04/0.99  sup_given_eliminated:                   0
% 3.04/0.99  comparisons_done:                       0
% 3.04/0.99  comparisons_avoided:                    24
% 3.04/0.99  
% 3.04/0.99  ------ Simplifications
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  sim_fw_subset_subsumed:                 16
% 3.04/0.99  sim_bw_subset_subsumed:                 4
% 3.04/0.99  sim_fw_subsumed:                        2
% 3.04/0.99  sim_bw_subsumed:                        0
% 3.04/0.99  sim_fw_subsumption_res:                 0
% 3.04/0.99  sim_bw_subsumption_res:                 0
% 3.04/0.99  sim_tautology_del:                      0
% 3.04/0.99  sim_eq_tautology_del:                   8
% 3.04/0.99  sim_eq_res_simp:                        2
% 3.04/0.99  sim_fw_demodulated:                     0
% 3.04/0.99  sim_bw_demodulated:                     24
% 3.04/0.99  sim_light_normalised:                   6
% 3.04/0.99  sim_joinable_taut:                      0
% 3.04/0.99  sim_joinable_simp:                      0
% 3.04/0.99  sim_ac_normalised:                      0
% 3.04/0.99  sim_smt_subsumption:                    0
% 3.04/0.99  
%------------------------------------------------------------------------------
