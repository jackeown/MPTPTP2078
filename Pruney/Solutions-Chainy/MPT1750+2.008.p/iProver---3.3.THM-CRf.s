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
% DateTime   : Thu Dec  3 12:22:23 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :  173 (1066 expanded)
%              Number of clauses        :   97 ( 279 expanded)
%              Number of leaves         :   19 ( 320 expanded)
%              Depth                    :   28
%              Number of atoms          :  696 (8522 expanded)
%              Number of equality atoms :  163 (1000 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                 => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                   => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X1)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                      & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                      & v1_funct_1(X3) )
                   => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                     => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2))
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2))
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2))
          & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(X3) )
     => ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),sK3,k2_tmap_1(X1,X0,sK3,X2))
        & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2))
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X3) )
          & m1_pre_topc(X2,X1)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(sK2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,sK2))
            & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
            & v1_funct_1(X3) )
        & m1_pre_topc(sK2,X1)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2))
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(sK1,X0,X3,X2))
                & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
                & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X0))
                & v1_funct_1(X3) )
            & m1_pre_topc(X2,sK1)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2))
                    & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                & m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(sK0),u1_struct_0(X2),u1_struct_0(sK0),X3,k2_tmap_1(X1,sK0,X3,X2))
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))
    & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    & v1_funct_1(sK3)
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f39,f47,f46,f45,f44])).

fof(f79,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f48])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f22])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f77,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f60,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f69,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f71,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f78,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f48])).

fof(f80,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f48])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f62,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f61,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f76,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f74,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f13,axiom,(
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

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      | X4 != X5
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f85,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_funct_2(X0,X1,X2,X3,X5,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X5,X0,X1)
      | ~ v1_funct_1(X5)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(equality_resolution,[],[f67])).

fof(f81,plain,(
    ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f48])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f72,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f73,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f70,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f82,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f50])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1325,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_5,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_9,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_356,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_5,c_9])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_360,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_356,c_9,c_5,c_4])).

cnf(c_361,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_360])).

cnf(c_417,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_6,c_361])).

cnf(c_421,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_417,c_9,c_6,c_5,c_4])).

cnf(c_422,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_421])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_747,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_422,c_24])).

cnf(c_748,plain,
    ( ~ v1_funct_2(sK3,X0,X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_xboole_0(X1)
    | k1_relat_1(sK3) = X0 ),
    inference(unflattening,[status(thm)],[c_747])).

cnf(c_11,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_14,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_338,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_11,c_14])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_581,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_338,c_32])).

cnf(c_582,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_581])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_584,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_582,c_30])).

cnf(c_844,plain,
    ( ~ v1_funct_2(sK3,X0,X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | u1_struct_0(sK0) != X1
    | k1_relat_1(sK3) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_748,c_584])).

cnf(c_845,plain,
    ( ~ v1_funct_2(sK3,X0,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK0))))
    | k1_relat_1(sK3) = X0 ),
    inference(unflattening,[status(thm)],[c_844])).

cnf(c_1315,plain,
    ( k1_relat_1(sK3) = X0
    | v1_funct_2(sK3,X0,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_845])).

cnf(c_1708,plain,
    ( u1_struct_0(sK1) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1325,c_1315])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_42,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2014,plain,
    ( u1_struct_0(sK1) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1708,c_42])).

cnf(c_21,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2021,plain,
    ( g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(demodulation,[status(thm)],[c_2014,c_21])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1326,plain,
    ( X0 = X1
    | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2389,plain,
    ( g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
    | u1_struct_0(sK2) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2021,c_1326])).

cnf(c_13,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_12,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_25,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_449,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_25])).

cnf(c_450,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_449])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_452,plain,
    ( l1_pre_topc(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_450,c_27])).

cnf(c_612,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_452])).

cnf(c_613,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(unflattening,[status(thm)],[c_612])).

cnf(c_2390,plain,
    ( g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
    | u1_struct_0(sK2) = X0
    | m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2021,c_1326])).

cnf(c_2407,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
    | u1_struct_0(sK2) = X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2390])).

cnf(c_2577,plain,
    ( u1_struct_0(sK2) = X0
    | g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2389,c_613,c_2407])).

cnf(c_2578,plain,
    ( g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
    | u1_struct_0(sK2) = X0 ),
    inference(renaming,[status(thm)],[c_2577])).

cnf(c_2583,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK3) ),
    inference(equality_resolution,[status(thm)],[c_2578])).

cnf(c_17,plain,
    ( r1_funct_2(X0,X1,X2,X3,X4,X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ v1_funct_2(X4,X0,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_20,negated_conjecture,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_627,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X0,X3,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0)
    | k2_tmap_1(sK1,sK0,sK3,sK2) != X0
    | u1_struct_0(sK2) != X1
    | u1_struct_0(sK0) != X2
    | u1_struct_0(sK0) != X4
    | u1_struct_0(sK1) != X3
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_20])).

cnf(c_628,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
    | sK3 != k2_tmap_1(sK1,sK0,sK3,sK2) ),
    inference(unflattening,[status(thm)],[c_627])).

cnf(c_630,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
    | sK3 != k2_tmap_1(sK1,sK0,sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_628,c_30,c_582])).

cnf(c_631,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
    | sK3 != k2_tmap_1(sK1,sK0,sK3,sK2) ),
    inference(renaming,[status(thm)],[c_630])).

cnf(c_777,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_631])).

cnf(c_1318,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
    | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_777])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_765,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_24])).

cnf(c_766,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(unflattening,[status(thm)],[c_765])).

cnf(c_1319,plain,
    ( k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_766])).

cnf(c_1554,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1325,c_1319])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_460,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3)
    | sK2 != X3
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_25])).

cnf(c_461,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(X1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,X1,X0,sK2) ),
    inference(unflattening,[status(thm)],[c_460])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_28,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_465,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,X1,X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_461,c_29,c_28,c_27])).

cnf(c_466,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,X1,X0,sK2) ),
    inference(renaming,[status(thm)],[c_465])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_525,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,X1,X0,sK2)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_466,c_31])).

cnf(c_526,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,X0,sK2) ),
    inference(unflattening,[status(thm)],[c_525])).

cnf(c_530,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_526,c_32,c_30])).

cnf(c_726,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,X0,sK2)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_530,c_24])).

cnf(c_727,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,sK3,sK2) ),
    inference(unflattening,[status(thm)],[c_726])).

cnf(c_729,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_727,c_23,c_22])).

cnf(c_1557,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
    inference(demodulation,[status(thm)],[c_1554,c_729])).

cnf(c_2315,plain,
    ( k7_relat_1(sK3,u1_struct_0(sK2)) != sK3
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
    | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1318,c_1557,c_2014])).

cnf(c_2731,plain,
    ( k7_relat_1(sK3,k1_relat_1(sK3)) != sK3
    | v1_funct_2(k7_relat_1(sK3,k1_relat_1(sK3)),k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,k1_relat_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2583,c_2315])).

cnf(c_1462,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1512,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),X0)
    | ~ v1_relat_1(sK3)
    | k7_relat_1(sK3,X0) = sK3 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1658,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k7_relat_1(sK3,k1_relat_1(sK3)) = sK3 ),
    inference(instantiation,[status(thm)],[c_1512])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1659,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3352,plain,
    ( v1_funct_2(k7_relat_1(sK3,k1_relat_1(sK3)),k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,k1_relat_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2731,c_22,c_1462,c_1658,c_1659])).

cnf(c_1328,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1785,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1325,c_1328])).

cnf(c_1330,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1329,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1919,plain,
    ( k7_relat_1(X0,k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1330,c_1329])).

cnf(c_2575,plain,
    ( k7_relat_1(sK3,k1_relat_1(sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_1785,c_1919])).

cnf(c_3356,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3352,c_2575])).

cnf(c_2019,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2014,c_1325])).

cnf(c_1324,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2020,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2014,c_1324])).

cnf(c_3359,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3356,c_2019,c_2020])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:22:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.15/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/0.98  
% 2.15/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.15/0.98  
% 2.15/0.98  ------  iProver source info
% 2.15/0.98  
% 2.15/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.15/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.15/0.98  git: non_committed_changes: false
% 2.15/0.98  git: last_make_outside_of_git: false
% 2.15/0.98  
% 2.15/0.98  ------ 
% 2.15/0.98  
% 2.15/0.98  ------ Input Options
% 2.15/0.98  
% 2.15/0.98  --out_options                           all
% 2.15/0.98  --tptp_safe_out                         true
% 2.15/0.98  --problem_path                          ""
% 2.15/0.98  --include_path                          ""
% 2.15/0.98  --clausifier                            res/vclausify_rel
% 2.15/0.98  --clausifier_options                    --mode clausify
% 2.15/0.98  --stdin                                 false
% 2.15/0.98  --stats_out                             all
% 2.15/0.98  
% 2.15/0.98  ------ General Options
% 2.15/0.98  
% 2.15/0.98  --fof                                   false
% 2.15/0.98  --time_out_real                         305.
% 2.15/0.98  --time_out_virtual                      -1.
% 2.15/0.98  --symbol_type_check                     false
% 2.15/0.98  --clausify_out                          false
% 2.15/0.98  --sig_cnt_out                           false
% 2.15/0.98  --trig_cnt_out                          false
% 2.15/0.98  --trig_cnt_out_tolerance                1.
% 2.15/0.98  --trig_cnt_out_sk_spl                   false
% 2.15/0.98  --abstr_cl_out                          false
% 2.15/0.98  
% 2.15/0.98  ------ Global Options
% 2.15/0.98  
% 2.15/0.98  --schedule                              default
% 2.15/0.98  --add_important_lit                     false
% 2.15/0.98  --prop_solver_per_cl                    1000
% 2.15/0.98  --min_unsat_core                        false
% 2.15/0.98  --soft_assumptions                      false
% 2.15/0.98  --soft_lemma_size                       3
% 2.15/0.98  --prop_impl_unit_size                   0
% 2.15/0.98  --prop_impl_unit                        []
% 2.15/0.98  --share_sel_clauses                     true
% 2.15/0.98  --reset_solvers                         false
% 2.15/0.98  --bc_imp_inh                            [conj_cone]
% 2.15/0.98  --conj_cone_tolerance                   3.
% 2.15/0.98  --extra_neg_conj                        none
% 2.15/0.98  --large_theory_mode                     true
% 2.15/0.98  --prolific_symb_bound                   200
% 2.15/0.98  --lt_threshold                          2000
% 2.15/0.98  --clause_weak_htbl                      true
% 2.15/0.98  --gc_record_bc_elim                     false
% 2.15/0.99  
% 2.15/0.99  ------ Preprocessing Options
% 2.15/0.99  
% 2.15/0.99  --preprocessing_flag                    true
% 2.15/0.99  --time_out_prep_mult                    0.1
% 2.15/0.99  --splitting_mode                        input
% 2.15/0.99  --splitting_grd                         true
% 2.15/0.99  --splitting_cvd                         false
% 2.15/0.99  --splitting_cvd_svl                     false
% 2.15/0.99  --splitting_nvd                         32
% 2.15/0.99  --sub_typing                            true
% 2.15/0.99  --prep_gs_sim                           true
% 2.15/0.99  --prep_unflatten                        true
% 2.15/0.99  --prep_res_sim                          true
% 2.15/0.99  --prep_upred                            true
% 2.15/0.99  --prep_sem_filter                       exhaustive
% 2.15/0.99  --prep_sem_filter_out                   false
% 2.15/0.99  --pred_elim                             true
% 2.15/0.99  --res_sim_input                         true
% 2.15/0.99  --eq_ax_congr_red                       true
% 2.15/0.99  --pure_diseq_elim                       true
% 2.15/0.99  --brand_transform                       false
% 2.15/0.99  --non_eq_to_eq                          false
% 2.15/0.99  --prep_def_merge                        true
% 2.15/0.99  --prep_def_merge_prop_impl              false
% 2.15/0.99  --prep_def_merge_mbd                    true
% 2.15/0.99  --prep_def_merge_tr_red                 false
% 2.15/0.99  --prep_def_merge_tr_cl                  false
% 2.15/0.99  --smt_preprocessing                     true
% 2.15/0.99  --smt_ac_axioms                         fast
% 2.15/0.99  --preprocessed_out                      false
% 2.15/0.99  --preprocessed_stats                    false
% 2.15/0.99  
% 2.15/0.99  ------ Abstraction refinement Options
% 2.15/0.99  
% 2.15/0.99  --abstr_ref                             []
% 2.15/0.99  --abstr_ref_prep                        false
% 2.15/0.99  --abstr_ref_until_sat                   false
% 2.15/0.99  --abstr_ref_sig_restrict                funpre
% 2.15/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.15/0.99  --abstr_ref_under                       []
% 2.15/0.99  
% 2.15/0.99  ------ SAT Options
% 2.15/0.99  
% 2.15/0.99  --sat_mode                              false
% 2.15/0.99  --sat_fm_restart_options                ""
% 2.15/0.99  --sat_gr_def                            false
% 2.15/0.99  --sat_epr_types                         true
% 2.15/0.99  --sat_non_cyclic_types                  false
% 2.15/0.99  --sat_finite_models                     false
% 2.15/0.99  --sat_fm_lemmas                         false
% 2.15/0.99  --sat_fm_prep                           false
% 2.15/0.99  --sat_fm_uc_incr                        true
% 2.15/0.99  --sat_out_model                         small
% 2.15/0.99  --sat_out_clauses                       false
% 2.15/0.99  
% 2.15/0.99  ------ QBF Options
% 2.15/0.99  
% 2.15/0.99  --qbf_mode                              false
% 2.15/0.99  --qbf_elim_univ                         false
% 2.15/0.99  --qbf_dom_inst                          none
% 2.15/0.99  --qbf_dom_pre_inst                      false
% 2.15/0.99  --qbf_sk_in                             false
% 2.15/0.99  --qbf_pred_elim                         true
% 2.15/0.99  --qbf_split                             512
% 2.15/0.99  
% 2.15/0.99  ------ BMC1 Options
% 2.15/0.99  
% 2.15/0.99  --bmc1_incremental                      false
% 2.15/0.99  --bmc1_axioms                           reachable_all
% 2.15/0.99  --bmc1_min_bound                        0
% 2.15/0.99  --bmc1_max_bound                        -1
% 2.15/0.99  --bmc1_max_bound_default                -1
% 2.15/0.99  --bmc1_symbol_reachability              true
% 2.15/0.99  --bmc1_property_lemmas                  false
% 2.15/0.99  --bmc1_k_induction                      false
% 2.15/0.99  --bmc1_non_equiv_states                 false
% 2.15/0.99  --bmc1_deadlock                         false
% 2.15/0.99  --bmc1_ucm                              false
% 2.15/0.99  --bmc1_add_unsat_core                   none
% 2.15/0.99  --bmc1_unsat_core_children              false
% 2.15/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.15/0.99  --bmc1_out_stat                         full
% 2.15/0.99  --bmc1_ground_init                      false
% 2.15/0.99  --bmc1_pre_inst_next_state              false
% 2.15/0.99  --bmc1_pre_inst_state                   false
% 2.15/0.99  --bmc1_pre_inst_reach_state             false
% 2.15/0.99  --bmc1_out_unsat_core                   false
% 2.15/0.99  --bmc1_aig_witness_out                  false
% 2.15/0.99  --bmc1_verbose                          false
% 2.15/0.99  --bmc1_dump_clauses_tptp                false
% 2.15/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.15/0.99  --bmc1_dump_file                        -
% 2.15/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.15/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.15/0.99  --bmc1_ucm_extend_mode                  1
% 2.15/0.99  --bmc1_ucm_init_mode                    2
% 2.15/0.99  --bmc1_ucm_cone_mode                    none
% 2.15/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.15/0.99  --bmc1_ucm_relax_model                  4
% 2.15/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.15/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.15/0.99  --bmc1_ucm_layered_model                none
% 2.15/0.99  --bmc1_ucm_max_lemma_size               10
% 2.15/0.99  
% 2.15/0.99  ------ AIG Options
% 2.15/0.99  
% 2.15/0.99  --aig_mode                              false
% 2.15/0.99  
% 2.15/0.99  ------ Instantiation Options
% 2.15/0.99  
% 2.15/0.99  --instantiation_flag                    true
% 2.15/0.99  --inst_sos_flag                         false
% 2.15/0.99  --inst_sos_phase                        true
% 2.15/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.15/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.15/0.99  --inst_lit_sel_side                     num_symb
% 2.15/0.99  --inst_solver_per_active                1400
% 2.15/0.99  --inst_solver_calls_frac                1.
% 2.15/0.99  --inst_passive_queue_type               priority_queues
% 2.15/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.15/0.99  --inst_passive_queues_freq              [25;2]
% 2.15/0.99  --inst_dismatching                      true
% 2.15/0.99  --inst_eager_unprocessed_to_passive     true
% 2.15/0.99  --inst_prop_sim_given                   true
% 2.15/0.99  --inst_prop_sim_new                     false
% 2.15/0.99  --inst_subs_new                         false
% 2.15/0.99  --inst_eq_res_simp                      false
% 2.15/0.99  --inst_subs_given                       false
% 2.15/0.99  --inst_orphan_elimination               true
% 2.15/0.99  --inst_learning_loop_flag               true
% 2.15/0.99  --inst_learning_start                   3000
% 2.15/0.99  --inst_learning_factor                  2
% 2.15/0.99  --inst_start_prop_sim_after_learn       3
% 2.15/0.99  --inst_sel_renew                        solver
% 2.15/0.99  --inst_lit_activity_flag                true
% 2.15/0.99  --inst_restr_to_given                   false
% 2.15/0.99  --inst_activity_threshold               500
% 2.15/0.99  --inst_out_proof                        true
% 2.15/0.99  
% 2.15/0.99  ------ Resolution Options
% 2.15/0.99  
% 2.15/0.99  --resolution_flag                       true
% 2.15/0.99  --res_lit_sel                           adaptive
% 2.15/0.99  --res_lit_sel_side                      none
% 2.15/0.99  --res_ordering                          kbo
% 2.15/0.99  --res_to_prop_solver                    active
% 2.15/0.99  --res_prop_simpl_new                    false
% 2.15/0.99  --res_prop_simpl_given                  true
% 2.15/0.99  --res_passive_queue_type                priority_queues
% 2.15/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.15/0.99  --res_passive_queues_freq               [15;5]
% 2.15/0.99  --res_forward_subs                      full
% 2.15/0.99  --res_backward_subs                     full
% 2.15/0.99  --res_forward_subs_resolution           true
% 2.15/0.99  --res_backward_subs_resolution          true
% 2.15/0.99  --res_orphan_elimination                true
% 2.15/0.99  --res_time_limit                        2.
% 2.15/0.99  --res_out_proof                         true
% 2.15/0.99  
% 2.15/0.99  ------ Superposition Options
% 2.15/0.99  
% 2.15/0.99  --superposition_flag                    true
% 2.15/0.99  --sup_passive_queue_type                priority_queues
% 2.15/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.15/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.15/0.99  --demod_completeness_check              fast
% 2.15/0.99  --demod_use_ground                      true
% 2.15/0.99  --sup_to_prop_solver                    passive
% 2.15/0.99  --sup_prop_simpl_new                    true
% 2.15/0.99  --sup_prop_simpl_given                  true
% 2.15/0.99  --sup_fun_splitting                     false
% 2.15/0.99  --sup_smt_interval                      50000
% 2.15/0.99  
% 2.15/0.99  ------ Superposition Simplification Setup
% 2.15/0.99  
% 2.15/0.99  --sup_indices_passive                   []
% 2.15/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.15/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.15/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.15/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.15/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.15/0.99  --sup_full_bw                           [BwDemod]
% 2.15/0.99  --sup_immed_triv                        [TrivRules]
% 2.15/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.15/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.15/0.99  --sup_immed_bw_main                     []
% 2.15/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.15/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.15/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.15/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.15/0.99  
% 2.15/0.99  ------ Combination Options
% 2.15/0.99  
% 2.15/0.99  --comb_res_mult                         3
% 2.15/0.99  --comb_sup_mult                         2
% 2.15/0.99  --comb_inst_mult                        10
% 2.15/0.99  
% 2.15/0.99  ------ Debug Options
% 2.15/0.99  
% 2.15/0.99  --dbg_backtrace                         false
% 2.15/0.99  --dbg_dump_prop_clauses                 false
% 2.15/0.99  --dbg_dump_prop_clauses_file            -
% 2.15/0.99  --dbg_out_stat                          false
% 2.15/0.99  ------ Parsing...
% 2.15/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.15/0.99  
% 2.15/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 10 0s  sf_e  pe_s  pe_e 
% 2.15/0.99  
% 2.15/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.15/0.99  
% 2.15/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.15/0.99  ------ Proving...
% 2.15/0.99  ------ Problem Properties 
% 2.15/0.99  
% 2.15/0.99  
% 2.15/0.99  clauses                                 19
% 2.15/0.99  conjectures                             3
% 2.15/0.99  EPR                                     2
% 2.15/0.99  Horn                                    19
% 2.15/0.99  unary                                   8
% 2.15/0.99  binary                                  2
% 2.15/0.99  lits                                    41
% 2.15/0.99  lits eq                                 14
% 2.15/0.99  fd_pure                                 0
% 2.15/0.99  fd_pseudo                               0
% 2.15/0.99  fd_cond                                 3
% 2.15/0.99  fd_pseudo_cond                          3
% 2.15/0.99  AC symbols                              0
% 2.15/0.99  
% 2.15/0.99  ------ Schedule dynamic 5 is on 
% 2.15/0.99  
% 2.15/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.15/0.99  
% 2.15/0.99  
% 2.15/0.99  ------ 
% 2.15/0.99  Current options:
% 2.15/0.99  ------ 
% 2.15/0.99  
% 2.15/0.99  ------ Input Options
% 2.15/0.99  
% 2.15/0.99  --out_options                           all
% 2.15/0.99  --tptp_safe_out                         true
% 2.15/0.99  --problem_path                          ""
% 2.15/0.99  --include_path                          ""
% 2.15/0.99  --clausifier                            res/vclausify_rel
% 2.15/0.99  --clausifier_options                    --mode clausify
% 2.15/0.99  --stdin                                 false
% 2.15/0.99  --stats_out                             all
% 2.15/0.99  
% 2.15/0.99  ------ General Options
% 2.15/0.99  
% 2.15/0.99  --fof                                   false
% 2.15/0.99  --time_out_real                         305.
% 2.15/0.99  --time_out_virtual                      -1.
% 2.15/0.99  --symbol_type_check                     false
% 2.15/0.99  --clausify_out                          false
% 2.15/0.99  --sig_cnt_out                           false
% 2.15/0.99  --trig_cnt_out                          false
% 2.15/0.99  --trig_cnt_out_tolerance                1.
% 2.15/0.99  --trig_cnt_out_sk_spl                   false
% 2.15/0.99  --abstr_cl_out                          false
% 2.15/0.99  
% 2.15/0.99  ------ Global Options
% 2.15/0.99  
% 2.15/0.99  --schedule                              default
% 2.15/0.99  --add_important_lit                     false
% 2.15/0.99  --prop_solver_per_cl                    1000
% 2.15/0.99  --min_unsat_core                        false
% 2.15/0.99  --soft_assumptions                      false
% 2.15/0.99  --soft_lemma_size                       3
% 2.15/0.99  --prop_impl_unit_size                   0
% 2.15/0.99  --prop_impl_unit                        []
% 2.15/0.99  --share_sel_clauses                     true
% 2.15/0.99  --reset_solvers                         false
% 2.15/0.99  --bc_imp_inh                            [conj_cone]
% 2.15/0.99  --conj_cone_tolerance                   3.
% 2.15/0.99  --extra_neg_conj                        none
% 2.15/0.99  --large_theory_mode                     true
% 2.15/0.99  --prolific_symb_bound                   200
% 2.15/0.99  --lt_threshold                          2000
% 2.15/0.99  --clause_weak_htbl                      true
% 2.15/0.99  --gc_record_bc_elim                     false
% 2.15/0.99  
% 2.15/0.99  ------ Preprocessing Options
% 2.15/0.99  
% 2.15/0.99  --preprocessing_flag                    true
% 2.15/0.99  --time_out_prep_mult                    0.1
% 2.15/0.99  --splitting_mode                        input
% 2.15/0.99  --splitting_grd                         true
% 2.15/0.99  --splitting_cvd                         false
% 2.15/0.99  --splitting_cvd_svl                     false
% 2.15/0.99  --splitting_nvd                         32
% 2.15/0.99  --sub_typing                            true
% 2.15/0.99  --prep_gs_sim                           true
% 2.15/0.99  --prep_unflatten                        true
% 2.15/0.99  --prep_res_sim                          true
% 2.15/0.99  --prep_upred                            true
% 2.15/0.99  --prep_sem_filter                       exhaustive
% 2.15/0.99  --prep_sem_filter_out                   false
% 2.15/0.99  --pred_elim                             true
% 2.15/0.99  --res_sim_input                         true
% 2.15/0.99  --eq_ax_congr_red                       true
% 2.15/0.99  --pure_diseq_elim                       true
% 2.15/0.99  --brand_transform                       false
% 2.15/0.99  --non_eq_to_eq                          false
% 2.15/0.99  --prep_def_merge                        true
% 2.15/0.99  --prep_def_merge_prop_impl              false
% 2.15/0.99  --prep_def_merge_mbd                    true
% 2.15/0.99  --prep_def_merge_tr_red                 false
% 2.15/0.99  --prep_def_merge_tr_cl                  false
% 2.15/0.99  --smt_preprocessing                     true
% 2.15/0.99  --smt_ac_axioms                         fast
% 2.15/0.99  --preprocessed_out                      false
% 2.15/0.99  --preprocessed_stats                    false
% 2.15/0.99  
% 2.15/0.99  ------ Abstraction refinement Options
% 2.15/0.99  
% 2.15/0.99  --abstr_ref                             []
% 2.15/0.99  --abstr_ref_prep                        false
% 2.15/0.99  --abstr_ref_until_sat                   false
% 2.15/0.99  --abstr_ref_sig_restrict                funpre
% 2.15/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.15/0.99  --abstr_ref_under                       []
% 2.15/0.99  
% 2.15/0.99  ------ SAT Options
% 2.15/0.99  
% 2.15/0.99  --sat_mode                              false
% 2.15/0.99  --sat_fm_restart_options                ""
% 2.15/0.99  --sat_gr_def                            false
% 2.15/0.99  --sat_epr_types                         true
% 2.15/0.99  --sat_non_cyclic_types                  false
% 2.15/0.99  --sat_finite_models                     false
% 2.15/0.99  --sat_fm_lemmas                         false
% 2.15/0.99  --sat_fm_prep                           false
% 2.15/0.99  --sat_fm_uc_incr                        true
% 2.15/0.99  --sat_out_model                         small
% 2.15/0.99  --sat_out_clauses                       false
% 2.15/0.99  
% 2.15/0.99  ------ QBF Options
% 2.15/0.99  
% 2.15/0.99  --qbf_mode                              false
% 2.15/0.99  --qbf_elim_univ                         false
% 2.15/0.99  --qbf_dom_inst                          none
% 2.15/0.99  --qbf_dom_pre_inst                      false
% 2.15/0.99  --qbf_sk_in                             false
% 2.15/0.99  --qbf_pred_elim                         true
% 2.15/0.99  --qbf_split                             512
% 2.15/0.99  
% 2.15/0.99  ------ BMC1 Options
% 2.15/0.99  
% 2.15/0.99  --bmc1_incremental                      false
% 2.15/0.99  --bmc1_axioms                           reachable_all
% 2.15/0.99  --bmc1_min_bound                        0
% 2.15/0.99  --bmc1_max_bound                        -1
% 2.15/0.99  --bmc1_max_bound_default                -1
% 2.15/0.99  --bmc1_symbol_reachability              true
% 2.15/0.99  --bmc1_property_lemmas                  false
% 2.15/0.99  --bmc1_k_induction                      false
% 2.15/0.99  --bmc1_non_equiv_states                 false
% 2.15/0.99  --bmc1_deadlock                         false
% 2.15/0.99  --bmc1_ucm                              false
% 2.15/0.99  --bmc1_add_unsat_core                   none
% 2.15/0.99  --bmc1_unsat_core_children              false
% 2.15/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.15/0.99  --bmc1_out_stat                         full
% 2.15/0.99  --bmc1_ground_init                      false
% 2.15/0.99  --bmc1_pre_inst_next_state              false
% 2.15/0.99  --bmc1_pre_inst_state                   false
% 2.15/0.99  --bmc1_pre_inst_reach_state             false
% 2.15/0.99  --bmc1_out_unsat_core                   false
% 2.15/0.99  --bmc1_aig_witness_out                  false
% 2.15/0.99  --bmc1_verbose                          false
% 2.15/0.99  --bmc1_dump_clauses_tptp                false
% 2.15/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.15/0.99  --bmc1_dump_file                        -
% 2.15/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.15/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.15/0.99  --bmc1_ucm_extend_mode                  1
% 2.15/0.99  --bmc1_ucm_init_mode                    2
% 2.15/0.99  --bmc1_ucm_cone_mode                    none
% 2.15/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.15/0.99  --bmc1_ucm_relax_model                  4
% 2.15/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.15/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.15/0.99  --bmc1_ucm_layered_model                none
% 2.15/0.99  --bmc1_ucm_max_lemma_size               10
% 2.15/0.99  
% 2.15/0.99  ------ AIG Options
% 2.15/0.99  
% 2.15/0.99  --aig_mode                              false
% 2.15/0.99  
% 2.15/0.99  ------ Instantiation Options
% 2.15/0.99  
% 2.15/0.99  --instantiation_flag                    true
% 2.15/0.99  --inst_sos_flag                         false
% 2.15/0.99  --inst_sos_phase                        true
% 2.15/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.15/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.15/0.99  --inst_lit_sel_side                     none
% 2.15/0.99  --inst_solver_per_active                1400
% 2.15/0.99  --inst_solver_calls_frac                1.
% 2.15/0.99  --inst_passive_queue_type               priority_queues
% 2.15/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.15/0.99  --inst_passive_queues_freq              [25;2]
% 2.15/0.99  --inst_dismatching                      true
% 2.15/0.99  --inst_eager_unprocessed_to_passive     true
% 2.15/0.99  --inst_prop_sim_given                   true
% 2.15/0.99  --inst_prop_sim_new                     false
% 2.15/0.99  --inst_subs_new                         false
% 2.15/0.99  --inst_eq_res_simp                      false
% 2.15/0.99  --inst_subs_given                       false
% 2.15/0.99  --inst_orphan_elimination               true
% 2.15/0.99  --inst_learning_loop_flag               true
% 2.15/0.99  --inst_learning_start                   3000
% 2.15/0.99  --inst_learning_factor                  2
% 2.15/0.99  --inst_start_prop_sim_after_learn       3
% 2.15/0.99  --inst_sel_renew                        solver
% 2.15/0.99  --inst_lit_activity_flag                true
% 2.15/0.99  --inst_restr_to_given                   false
% 2.15/0.99  --inst_activity_threshold               500
% 2.15/0.99  --inst_out_proof                        true
% 2.15/0.99  
% 2.15/0.99  ------ Resolution Options
% 2.15/0.99  
% 2.15/0.99  --resolution_flag                       false
% 2.15/0.99  --res_lit_sel                           adaptive
% 2.15/0.99  --res_lit_sel_side                      none
% 2.15/0.99  --res_ordering                          kbo
% 2.15/0.99  --res_to_prop_solver                    active
% 2.15/0.99  --res_prop_simpl_new                    false
% 2.15/0.99  --res_prop_simpl_given                  true
% 2.15/0.99  --res_passive_queue_type                priority_queues
% 2.15/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.15/0.99  --res_passive_queues_freq               [15;5]
% 2.15/0.99  --res_forward_subs                      full
% 2.15/0.99  --res_backward_subs                     full
% 2.15/0.99  --res_forward_subs_resolution           true
% 2.15/0.99  --res_backward_subs_resolution          true
% 2.15/0.99  --res_orphan_elimination                true
% 2.15/0.99  --res_time_limit                        2.
% 2.15/0.99  --res_out_proof                         true
% 2.15/0.99  
% 2.15/0.99  ------ Superposition Options
% 2.15/0.99  
% 2.15/0.99  --superposition_flag                    true
% 2.15/0.99  --sup_passive_queue_type                priority_queues
% 2.15/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.15/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.15/0.99  --demod_completeness_check              fast
% 2.15/0.99  --demod_use_ground                      true
% 2.15/0.99  --sup_to_prop_solver                    passive
% 2.15/0.99  --sup_prop_simpl_new                    true
% 2.15/0.99  --sup_prop_simpl_given                  true
% 2.15/0.99  --sup_fun_splitting                     false
% 2.15/0.99  --sup_smt_interval                      50000
% 2.15/0.99  
% 2.15/0.99  ------ Superposition Simplification Setup
% 2.15/0.99  
% 2.15/0.99  --sup_indices_passive                   []
% 2.15/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.15/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.15/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.15/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.15/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.15/0.99  --sup_full_bw                           [BwDemod]
% 2.15/0.99  --sup_immed_triv                        [TrivRules]
% 2.15/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.15/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.15/0.99  --sup_immed_bw_main                     []
% 2.15/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.15/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.15/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.15/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.15/0.99  
% 2.15/0.99  ------ Combination Options
% 2.15/0.99  
% 2.15/0.99  --comb_res_mult                         3
% 2.15/0.99  --comb_sup_mult                         2
% 2.15/0.99  --comb_inst_mult                        10
% 2.15/0.99  
% 2.15/0.99  ------ Debug Options
% 2.15/0.99  
% 2.15/0.99  --dbg_backtrace                         false
% 2.15/0.99  --dbg_dump_prop_clauses                 false
% 2.15/0.99  --dbg_dump_prop_clauses_file            -
% 2.15/0.99  --dbg_out_stat                          false
% 2.15/0.99  
% 2.15/0.99  
% 2.15/0.99  
% 2.15/0.99  
% 2.15/0.99  ------ Proving...
% 2.15/0.99  
% 2.15/0.99  
% 2.15/0.99  % SZS status Theorem for theBenchmark.p
% 2.15/0.99  
% 2.15/0.99   Resolution empty clause
% 2.15/0.99  
% 2.15/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.15/0.99  
% 2.15/0.99  fof(f15,conjecture,(
% 2.15/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)))))))),
% 2.15/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.15/0.99  
% 2.15/0.99  fof(f16,negated_conjecture,(
% 2.15/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)))))))),
% 2.15/0.99    inference(negated_conjecture,[],[f15])).
% 2.15/0.99  
% 2.15/0.99  fof(f38,plain,(
% 2.15/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.15/0.99    inference(ennf_transformation,[],[f16])).
% 2.15/0.99  
% 2.15/0.99  fof(f39,plain,(
% 2.15/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.15/0.99    inference(flattening,[],[f38])).
% 2.15/0.99  
% 2.15/0.99  fof(f47,plain,(
% 2.15/0.99    ( ! [X2,X0,X1] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),sK3,k2_tmap_1(X1,X0,sK3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK3))) )),
% 2.15/0.99    introduced(choice_axiom,[])).
% 2.15/0.99  
% 2.15/0.99  fof(f46,plain,(
% 2.15/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(sK2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,sK2)) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(sK2,X1) & ~v2_struct_0(sK2))) )),
% 2.15/0.99    introduced(choice_axiom,[])).
% 2.15/0.99  
% 2.15/0.99  fof(f45,plain,(
% 2.15/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(sK1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(sK1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 2.15/0.99    introduced(choice_axiom,[])).
% 2.15/0.99  
% 2.15/0.99  fof(f44,plain,(
% 2.15/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(sK0),u1_struct_0(X2),u1_struct_0(sK0),X3,k2_tmap_1(X1,sK0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.15/0.99    introduced(choice_axiom,[])).
% 2.15/0.99  
% 2.15/0.99  fof(f48,plain,(
% 2.15/0.99    (((~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.15/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f39,f47,f46,f45,f44])).
% 2.15/0.99  
% 2.15/0.99  fof(f79,plain,(
% 2.15/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.15/0.99    inference(cnf_transformation,[],[f48])).
% 2.15/0.99  
% 2.15/0.99  fof(f5,axiom,(
% 2.15/0.99    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 2.15/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.15/0.99  
% 2.15/0.99  fof(f22,plain,(
% 2.15/0.99    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.15/0.99    inference(ennf_transformation,[],[f5])).
% 2.15/0.99  
% 2.15/0.99  fof(f23,plain,(
% 2.15/0.99    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.15/0.99    inference(flattening,[],[f22])).
% 2.15/0.99  
% 2.15/0.99  fof(f56,plain,(
% 2.15/0.99    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 2.15/0.99    inference(cnf_transformation,[],[f23])).
% 2.15/0.99  
% 2.15/0.99  fof(f4,axiom,(
% 2.15/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.15/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.15/0.99  
% 2.15/0.99  fof(f17,plain,(
% 2.15/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.15/0.99    inference(pure_predicate_removal,[],[f4])).
% 2.15/0.99  
% 2.15/0.99  fof(f21,plain,(
% 2.15/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.15/0.99    inference(ennf_transformation,[],[f17])).
% 2.15/0.99  
% 2.15/0.99  fof(f54,plain,(
% 2.15/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.15/0.99    inference(cnf_transformation,[],[f21])).
% 2.15/0.99  
% 2.15/0.99  fof(f6,axiom,(
% 2.15/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.15/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.15/0.99  
% 2.15/0.99  fof(f24,plain,(
% 2.15/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.15/0.99    inference(ennf_transformation,[],[f6])).
% 2.15/0.99  
% 2.15/0.99  fof(f25,plain,(
% 2.15/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.15/0.99    inference(flattening,[],[f24])).
% 2.15/0.99  
% 2.15/0.99  fof(f42,plain,(
% 2.15/0.99    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.15/0.99    inference(nnf_transformation,[],[f25])).
% 2.15/0.99  
% 2.15/0.99  fof(f57,plain,(
% 2.15/0.99    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.15/0.99    inference(cnf_transformation,[],[f42])).
% 2.15/0.99  
% 2.15/0.99  fof(f3,axiom,(
% 2.15/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.15/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.15/0.99  
% 2.15/0.99  fof(f20,plain,(
% 2.15/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.15/0.99    inference(ennf_transformation,[],[f3])).
% 2.15/0.99  
% 2.15/0.99  fof(f53,plain,(
% 2.15/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.15/0.99    inference(cnf_transformation,[],[f20])).
% 2.15/0.99  
% 2.15/0.99  fof(f77,plain,(
% 2.15/0.99    v1_funct_1(sK3)),
% 2.15/0.99    inference(cnf_transformation,[],[f48])).
% 2.15/0.99  
% 2.15/0.99  fof(f8,axiom,(
% 2.15/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.15/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.15/0.99  
% 2.15/0.99  fof(f28,plain,(
% 2.15/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.15/0.99    inference(ennf_transformation,[],[f8])).
% 2.15/0.99  
% 2.15/0.99  fof(f60,plain,(
% 2.15/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.15/0.99    inference(cnf_transformation,[],[f28])).
% 2.15/0.99  
% 2.15/0.99  fof(f11,axiom,(
% 2.15/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.15/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.15/0.99  
% 2.15/0.99  fof(f31,plain,(
% 2.15/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.15/0.99    inference(ennf_transformation,[],[f11])).
% 2.15/0.99  
% 2.15/0.99  fof(f32,plain,(
% 2.15/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.15/0.99    inference(flattening,[],[f31])).
% 2.15/0.99  
% 2.15/0.99  fof(f63,plain,(
% 2.15/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.15/0.99    inference(cnf_transformation,[],[f32])).
% 2.15/0.99  
% 2.15/0.99  fof(f69,plain,(
% 2.15/0.99    ~v2_struct_0(sK0)),
% 2.15/0.99    inference(cnf_transformation,[],[f48])).
% 2.15/0.99  
% 2.15/0.99  fof(f71,plain,(
% 2.15/0.99    l1_pre_topc(sK0)),
% 2.15/0.99    inference(cnf_transformation,[],[f48])).
% 2.15/0.99  
% 2.15/0.99  fof(f78,plain,(
% 2.15/0.99    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.15/0.99    inference(cnf_transformation,[],[f48])).
% 2.15/0.99  
% 2.15/0.99  fof(f80,plain,(
% 2.15/0.99    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 2.15/0.99    inference(cnf_transformation,[],[f48])).
% 2.15/0.99  
% 2.15/0.99  fof(f12,axiom,(
% 2.15/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 2.15/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.15/0.99  
% 2.15/0.99  fof(f33,plain,(
% 2.15/0.99    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.15/0.99    inference(ennf_transformation,[],[f12])).
% 2.15/0.99  
% 2.15/0.99  fof(f64,plain,(
% 2.15/0.99    ( ! [X2,X0,X3,X1] : (X0 = X2 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.15/0.99    inference(cnf_transformation,[],[f33])).
% 2.15/0.99  
% 2.15/0.99  fof(f10,axiom,(
% 2.15/0.99    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.15/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.15/0.99  
% 2.15/0.99  fof(f30,plain,(
% 2.15/0.99    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.15/0.99    inference(ennf_transformation,[],[f10])).
% 2.15/0.99  
% 2.15/0.99  fof(f62,plain,(
% 2.15/0.99    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 2.15/0.99    inference(cnf_transformation,[],[f30])).
% 2.15/0.99  
% 2.15/0.99  fof(f9,axiom,(
% 2.15/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.15/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.15/0.99  
% 2.15/0.99  fof(f29,plain,(
% 2.15/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.15/0.99    inference(ennf_transformation,[],[f9])).
% 2.15/0.99  
% 2.15/0.99  fof(f61,plain,(
% 2.15/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.15/0.99    inference(cnf_transformation,[],[f29])).
% 2.15/0.99  
% 2.15/0.99  fof(f76,plain,(
% 2.15/0.99    m1_pre_topc(sK2,sK1)),
% 2.15/0.99    inference(cnf_transformation,[],[f48])).
% 2.15/0.99  
% 2.15/0.99  fof(f74,plain,(
% 2.15/0.99    l1_pre_topc(sK1)),
% 2.15/0.99    inference(cnf_transformation,[],[f48])).
% 2.15/0.99  
% 2.15/0.99  fof(f13,axiom,(
% 2.15/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 2.15/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.15/0.99  
% 2.15/0.99  fof(f34,plain,(
% 2.15/0.99    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 2.15/0.99    inference(ennf_transformation,[],[f13])).
% 2.15/0.99  
% 2.15/0.99  fof(f35,plain,(
% 2.15/0.99    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 2.15/0.99    inference(flattening,[],[f34])).
% 2.15/0.99  
% 2.15/0.99  fof(f43,plain,(
% 2.15/0.99    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 2.15/0.99    inference(nnf_transformation,[],[f35])).
% 2.15/0.99  
% 2.15/0.99  fof(f67,plain,(
% 2.15/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 2.15/0.99    inference(cnf_transformation,[],[f43])).
% 2.15/0.99  
% 2.15/0.99  fof(f85,plain,(
% 2.15/0.99    ( ! [X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X5,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X5,X0,X1) | ~v1_funct_1(X5) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 2.15/0.99    inference(equality_resolution,[],[f67])).
% 2.15/0.99  
% 2.15/0.99  fof(f81,plain,(
% 2.15/0.99    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))),
% 2.15/0.99    inference(cnf_transformation,[],[f48])).
% 2.15/0.99  
% 2.15/0.99  fof(f7,axiom,(
% 2.15/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 2.15/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.15/0.99  
% 2.15/0.99  fof(f26,plain,(
% 2.15/0.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.15/0.99    inference(ennf_transformation,[],[f7])).
% 2.15/0.99  
% 2.15/0.99  fof(f27,plain,(
% 2.15/0.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.15/0.99    inference(flattening,[],[f26])).
% 2.15/0.99  
% 2.15/0.99  fof(f59,plain,(
% 2.15/0.99    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.15/0.99    inference(cnf_transformation,[],[f27])).
% 2.15/0.99  
% 2.15/0.99  fof(f14,axiom,(
% 2.15/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)))))),
% 2.15/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.15/0.99  
% 2.15/0.99  fof(f36,plain,(
% 2.15/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.15/0.99    inference(ennf_transformation,[],[f14])).
% 2.15/0.99  
% 2.15/0.99  fof(f37,plain,(
% 2.15/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.15/0.99    inference(flattening,[],[f36])).
% 2.15/0.99  
% 2.15/0.99  fof(f68,plain,(
% 2.15/0.99    ( ! [X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.15/0.99    inference(cnf_transformation,[],[f37])).
% 2.15/0.99  
% 2.15/0.99  fof(f72,plain,(
% 2.15/0.99    ~v2_struct_0(sK1)),
% 2.15/0.99    inference(cnf_transformation,[],[f48])).
% 2.15/0.99  
% 2.15/0.99  fof(f73,plain,(
% 2.15/0.99    v2_pre_topc(sK1)),
% 2.15/0.99    inference(cnf_transformation,[],[f48])).
% 2.15/0.99  
% 2.15/0.99  fof(f70,plain,(
% 2.15/0.99    v2_pre_topc(sK0)),
% 2.15/0.99    inference(cnf_transformation,[],[f48])).
% 2.15/0.99  
% 2.15/0.99  fof(f2,axiom,(
% 2.15/0.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 2.15/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.15/0.99  
% 2.15/0.99  fof(f18,plain,(
% 2.15/0.99    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.15/0.99    inference(ennf_transformation,[],[f2])).
% 2.15/0.99  
% 2.15/0.99  fof(f19,plain,(
% 2.15/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.15/0.99    inference(flattening,[],[f18])).
% 2.15/0.99  
% 2.15/0.99  fof(f52,plain,(
% 2.15/0.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.15/0.99    inference(cnf_transformation,[],[f19])).
% 2.15/0.99  
% 2.15/0.99  fof(f1,axiom,(
% 2.15/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.15/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.15/0.99  
% 2.15/0.99  fof(f40,plain,(
% 2.15/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.15/0.99    inference(nnf_transformation,[],[f1])).
% 2.15/0.99  
% 2.15/0.99  fof(f41,plain,(
% 2.15/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.15/0.99    inference(flattening,[],[f40])).
% 2.15/0.99  
% 2.15/0.99  fof(f50,plain,(
% 2.15/0.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.15/0.99    inference(cnf_transformation,[],[f41])).
% 2.15/0.99  
% 2.15/0.99  fof(f82,plain,(
% 2.15/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.15/0.99    inference(equality_resolution,[],[f50])).
% 2.15/0.99  
% 2.15/0.99  cnf(c_22,negated_conjecture,
% 2.15/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
% 2.15/0.99      inference(cnf_transformation,[],[f79]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_1325,plain,
% 2.15/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
% 2.15/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_6,plain,
% 2.15/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.15/0.99      | v1_partfun1(X0,X1)
% 2.15/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.15/0.99      | v1_xboole_0(X2)
% 2.15/0.99      | ~ v1_funct_1(X0) ),
% 2.15/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_5,plain,
% 2.15/0.99      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.15/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_9,plain,
% 2.15/0.99      ( ~ v1_partfun1(X0,X1)
% 2.15/0.99      | ~ v4_relat_1(X0,X1)
% 2.15/0.99      | ~ v1_relat_1(X0)
% 2.15/0.99      | k1_relat_1(X0) = X1 ),
% 2.15/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_356,plain,
% 2.15/0.99      ( ~ v1_partfun1(X0,X1)
% 2.15/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.15/0.99      | ~ v1_relat_1(X0)
% 2.15/0.99      | k1_relat_1(X0) = X1 ),
% 2.15/0.99      inference(resolution,[status(thm)],[c_5,c_9]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_4,plain,
% 2.15/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.15/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_360,plain,
% 2.15/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.15/0.99      | ~ v1_partfun1(X0,X1)
% 2.15/0.99      | k1_relat_1(X0) = X1 ),
% 2.15/0.99      inference(global_propositional_subsumption,
% 2.15/0.99                [status(thm)],
% 2.15/0.99                [c_356,c_9,c_5,c_4]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_361,plain,
% 2.15/0.99      ( ~ v1_partfun1(X0,X1)
% 2.15/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.15/0.99      | k1_relat_1(X0) = X1 ),
% 2.15/0.99      inference(renaming,[status(thm)],[c_360]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_417,plain,
% 2.15/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.15/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.15/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.15/0.99      | v1_xboole_0(X2)
% 2.15/0.99      | ~ v1_funct_1(X0)
% 2.15/0.99      | k1_relat_1(X0) = X1 ),
% 2.15/0.99      inference(resolution,[status(thm)],[c_6,c_361]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_421,plain,
% 2.15/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.15/0.99      | ~ v1_funct_2(X0,X1,X2)
% 2.15/0.99      | v1_xboole_0(X2)
% 2.15/0.99      | ~ v1_funct_1(X0)
% 2.15/0.99      | k1_relat_1(X0) = X1 ),
% 2.15/0.99      inference(global_propositional_subsumption,
% 2.15/0.99                [status(thm)],
% 2.15/0.99                [c_417,c_9,c_6,c_5,c_4]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_422,plain,
% 2.15/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.15/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.15/0.99      | v1_xboole_0(X2)
% 2.15/0.99      | ~ v1_funct_1(X0)
% 2.15/0.99      | k1_relat_1(X0) = X1 ),
% 2.15/0.99      inference(renaming,[status(thm)],[c_421]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_24,negated_conjecture,
% 2.15/0.99      ( v1_funct_1(sK3) ),
% 2.15/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_747,plain,
% 2.15/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.15/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.15/0.99      | v1_xboole_0(X2)
% 2.15/0.99      | k1_relat_1(X0) = X1
% 2.15/0.99      | sK3 != X0 ),
% 2.15/0.99      inference(resolution_lifted,[status(thm)],[c_422,c_24]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_748,plain,
% 2.15/0.99      ( ~ v1_funct_2(sK3,X0,X1)
% 2.15/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.15/0.99      | v1_xboole_0(X1)
% 2.15/0.99      | k1_relat_1(sK3) = X0 ),
% 2.15/0.99      inference(unflattening,[status(thm)],[c_747]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_11,plain,
% 2.15/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.15/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_14,plain,
% 2.15/0.99      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.15/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_338,plain,
% 2.15/0.99      ( v2_struct_0(X0) | ~ l1_pre_topc(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.15/0.99      inference(resolution,[status(thm)],[c_11,c_14]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_32,negated_conjecture,
% 2.15/0.99      ( ~ v2_struct_0(sK0) ),
% 2.15/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_581,plain,
% 2.15/0.99      ( ~ l1_pre_topc(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK0 != X0 ),
% 2.15/0.99      inference(resolution_lifted,[status(thm)],[c_338,c_32]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_582,plain,
% 2.15/0.99      ( ~ l1_pre_topc(sK0) | ~ v1_xboole_0(u1_struct_0(sK0)) ),
% 2.15/0.99      inference(unflattening,[status(thm)],[c_581]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_30,negated_conjecture,
% 2.15/0.99      ( l1_pre_topc(sK0) ),
% 2.15/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_584,plain,
% 2.15/0.99      ( ~ v1_xboole_0(u1_struct_0(sK0)) ),
% 2.15/0.99      inference(global_propositional_subsumption,[status(thm)],[c_582,c_30]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_844,plain,
% 2.15/0.99      ( ~ v1_funct_2(sK3,X0,X1)
% 2.15/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.15/0.99      | u1_struct_0(sK0) != X1
% 2.15/0.99      | k1_relat_1(sK3) = X0 ),
% 2.15/0.99      inference(resolution_lifted,[status(thm)],[c_748,c_584]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_845,plain,
% 2.15/0.99      ( ~ v1_funct_2(sK3,X0,u1_struct_0(sK0))
% 2.15/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK0))))
% 2.15/0.99      | k1_relat_1(sK3) = X0 ),
% 2.15/0.99      inference(unflattening,[status(thm)],[c_844]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_1315,plain,
% 2.15/0.99      ( k1_relat_1(sK3) = X0
% 2.15/0.99      | v1_funct_2(sK3,X0,u1_struct_0(sK0)) != iProver_top
% 2.15/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK0)))) != iProver_top ),
% 2.15/0.99      inference(predicate_to_equality,[status(thm)],[c_845]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_1708,plain,
% 2.15/0.99      ( u1_struct_0(sK1) = k1_relat_1(sK3)
% 2.15/0.99      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top ),
% 2.15/0.99      inference(superposition,[status(thm)],[c_1325,c_1315]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_23,negated_conjecture,
% 2.15/0.99      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
% 2.15/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_42,plain,
% 2.15/0.99      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top ),
% 2.15/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_2014,plain,
% 2.15/0.99      ( u1_struct_0(sK1) = k1_relat_1(sK3) ),
% 2.15/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1708,c_42]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_21,negated_conjecture,
% 2.15/0.99      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 2.15/0.99      inference(cnf_transformation,[],[f80]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_2021,plain,
% 2.15/0.99      ( g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 2.15/0.99      inference(demodulation,[status(thm)],[c_2014,c_21]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_16,plain,
% 2.15/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.15/0.99      | X2 = X1
% 2.15/0.99      | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
% 2.15/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_1326,plain,
% 2.15/0.99      ( X0 = X1
% 2.15/0.99      | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
% 2.15/0.99      | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
% 2.15/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_2389,plain,
% 2.15/0.99      ( g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
% 2.15/0.99      | u1_struct_0(sK2) = X0
% 2.15/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.15/0.99      inference(superposition,[status(thm)],[c_2021,c_1326]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_13,plain,
% 2.15/0.99      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.15/0.99      | ~ l1_pre_topc(X0) ),
% 2.15/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_12,plain,
% 2.15/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.15/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_25,negated_conjecture,
% 2.15/0.99      ( m1_pre_topc(sK2,sK1) ),
% 2.15/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_449,plain,
% 2.15/0.99      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK2 != X1 | sK1 != X0 ),
% 2.15/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_25]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_450,plain,
% 2.15/0.99      ( l1_pre_topc(sK2) | ~ l1_pre_topc(sK1) ),
% 2.15/0.99      inference(unflattening,[status(thm)],[c_449]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_27,negated_conjecture,
% 2.15/0.99      ( l1_pre_topc(sK1) ),
% 2.15/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_452,plain,
% 2.15/0.99      ( l1_pre_topc(sK2) ),
% 2.15/0.99      inference(global_propositional_subsumption,[status(thm)],[c_450,c_27]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_612,plain,
% 2.15/0.99      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.15/0.99      | sK2 != X0 ),
% 2.15/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_452]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_613,plain,
% 2.15/0.99      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
% 2.15/0.99      inference(unflattening,[status(thm)],[c_612]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_2390,plain,
% 2.15/0.99      ( g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
% 2.15/0.99      | u1_struct_0(sK2) = X0
% 2.15/0.99      | m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
% 2.15/0.99      inference(superposition,[status(thm)],[c_2021,c_1326]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_2407,plain,
% 2.15/0.99      ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 2.15/0.99      | g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
% 2.15/0.99      | u1_struct_0(sK2) = X0 ),
% 2.15/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2390]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_2577,plain,
% 2.15/0.99      ( u1_struct_0(sK2) = X0
% 2.15/0.99      | g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1) ),
% 2.15/0.99      inference(global_propositional_subsumption,
% 2.15/0.99                [status(thm)],
% 2.15/0.99                [c_2389,c_613,c_2407]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_2578,plain,
% 2.15/0.99      ( g1_pre_topc(k1_relat_1(sK3),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
% 2.15/0.99      | u1_struct_0(sK2) = X0 ),
% 2.15/0.99      inference(renaming,[status(thm)],[c_2577]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_2583,plain,
% 2.15/0.99      ( u1_struct_0(sK2) = k1_relat_1(sK3) ),
% 2.15/0.99      inference(equality_resolution,[status(thm)],[c_2578]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_17,plain,
% 2.15/0.99      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
% 2.15/0.99      | ~ v1_funct_2(X4,X2,X3)
% 2.15/0.99      | ~ v1_funct_2(X4,X0,X1)
% 2.15/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.15/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.15/0.99      | v1_xboole_0(X1)
% 2.15/0.99      | v1_xboole_0(X3)
% 2.15/0.99      | ~ v1_funct_1(X4) ),
% 2.15/0.99      inference(cnf_transformation,[],[f85]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_20,negated_conjecture,
% 2.15/0.99      ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
% 2.15/0.99      inference(cnf_transformation,[],[f81]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_627,plain,
% 2.15/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.15/0.99      | ~ v1_funct_2(X0,X3,X4)
% 2.15/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.15/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 2.15/0.99      | v1_xboole_0(X4)
% 2.15/0.99      | v1_xboole_0(X2)
% 2.15/0.99      | ~ v1_funct_1(X0)
% 2.15/0.99      | k2_tmap_1(sK1,sK0,sK3,sK2) != X0
% 2.15/0.99      | u1_struct_0(sK2) != X1
% 2.15/0.99      | u1_struct_0(sK0) != X2
% 2.15/0.99      | u1_struct_0(sK0) != X4
% 2.15/0.99      | u1_struct_0(sK1) != X3
% 2.15/0.99      | sK3 != X0 ),
% 2.15/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_20]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_628,plain,
% 2.15/0.99      ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
% 2.15/0.99      | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 2.15/0.99      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
% 2.15/0.99      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.15/0.99      | v1_xboole_0(u1_struct_0(sK0))
% 2.15/0.99      | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
% 2.15/0.99      | sK3 != k2_tmap_1(sK1,sK0,sK3,sK2) ),
% 2.15/0.99      inference(unflattening,[status(thm)],[c_627]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_630,plain,
% 2.15/0.99      ( ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.15/0.99      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
% 2.15/0.99      | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 2.15/0.99      | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
% 2.15/0.99      | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
% 2.15/0.99      | sK3 != k2_tmap_1(sK1,sK0,sK3,sK2) ),
% 2.15/0.99      inference(global_propositional_subsumption,
% 2.15/0.99                [status(thm)],
% 2.15/0.99                [c_628,c_30,c_582]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_631,plain,
% 2.15/0.99      ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
% 2.15/0.99      | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 2.15/0.99      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
% 2.15/0.99      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.15/0.99      | ~ v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
% 2.15/0.99      | sK3 != k2_tmap_1(sK1,sK0,sK3,sK2) ),
% 2.15/0.99      inference(renaming,[status(thm)],[c_630]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_777,plain,
% 2.15/0.99      ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
% 2.15/0.99      | ~ v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 2.15/0.99      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
% 2.15/0.99      | ~ m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.15/0.99      | k2_tmap_1(sK1,sK0,sK3,sK2) != sK3 ),
% 2.15/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_631]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_1318,plain,
% 2.15/0.99      ( k2_tmap_1(sK1,sK0,sK3,sK2) != sK3
% 2.15/0.99      | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
% 2.15/0.99      | v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 2.15/0.99      | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
% 2.15/0.99      | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
% 2.15/0.99      inference(predicate_to_equality,[status(thm)],[c_777]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_10,plain,
% 2.15/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.15/0.99      | ~ v1_funct_1(X0)
% 2.15/0.99      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 2.15/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_765,plain,
% 2.15/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.15/0.99      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
% 2.15/0.99      | sK3 != X0 ),
% 2.15/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_24]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_766,plain,
% 2.15/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.15/0.99      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 2.15/0.99      inference(unflattening,[status(thm)],[c_765]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_1319,plain,
% 2.15/0.99      ( k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)
% 2.15/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.15/0.99      inference(predicate_to_equality,[status(thm)],[c_766]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_1554,plain,
% 2.15/0.99      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k7_relat_1(sK3,X0) ),
% 2.15/0.99      inference(superposition,[status(thm)],[c_1325,c_1319]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_19,plain,
% 2.15/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.15/0.99      | ~ m1_pre_topc(X3,X1)
% 2.15/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.15/0.99      | ~ v2_pre_topc(X2)
% 2.15/0.99      | ~ v2_pre_topc(X1)
% 2.15/0.99      | v2_struct_0(X1)
% 2.15/0.99      | v2_struct_0(X2)
% 2.15/0.99      | ~ l1_pre_topc(X1)
% 2.15/0.99      | ~ l1_pre_topc(X2)
% 2.15/0.99      | ~ v1_funct_1(X0)
% 2.15/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 2.15/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_460,plain,
% 2.15/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.15/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.15/0.99      | ~ v2_pre_topc(X1)
% 2.15/0.99      | ~ v2_pre_topc(X2)
% 2.15/0.99      | v2_struct_0(X1)
% 2.15/0.99      | v2_struct_0(X2)
% 2.15/0.99      | ~ l1_pre_topc(X1)
% 2.15/0.99      | ~ l1_pre_topc(X2)
% 2.15/0.99      | ~ v1_funct_1(X0)
% 2.15/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3)
% 2.15/0.99      | sK2 != X3
% 2.15/0.99      | sK1 != X1 ),
% 2.15/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_25]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_461,plain,
% 2.15/0.99      ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
% 2.15/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 2.15/0.99      | ~ v2_pre_topc(X1)
% 2.15/0.99      | ~ v2_pre_topc(sK1)
% 2.15/0.99      | v2_struct_0(X1)
% 2.15/0.99      | v2_struct_0(sK1)
% 2.15/0.99      | ~ l1_pre_topc(X1)
% 2.15/0.99      | ~ l1_pre_topc(sK1)
% 2.15/0.99      | ~ v1_funct_1(X0)
% 2.15/0.99      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,X1,X0,sK2) ),
% 2.15/0.99      inference(unflattening,[status(thm)],[c_460]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_29,negated_conjecture,
% 2.15/0.99      ( ~ v2_struct_0(sK1) ),
% 2.15/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_28,negated_conjecture,
% 2.15/0.99      ( v2_pre_topc(sK1) ),
% 2.15/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_465,plain,
% 2.15/0.99      ( ~ l1_pre_topc(X1)
% 2.15/0.99      | ~ v2_pre_topc(X1)
% 2.15/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 2.15/0.99      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
% 2.15/0.99      | v2_struct_0(X1)
% 2.15/0.99      | ~ v1_funct_1(X0)
% 2.15/0.99      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,X1,X0,sK2) ),
% 2.15/0.99      inference(global_propositional_subsumption,
% 2.15/0.99                [status(thm)],
% 2.15/0.99                [c_461,c_29,c_28,c_27]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_466,plain,
% 2.15/0.99      ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
% 2.15/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 2.15/0.99      | ~ v2_pre_topc(X1)
% 2.15/0.99      | v2_struct_0(X1)
% 2.15/0.99      | ~ l1_pre_topc(X1)
% 2.15/0.99      | ~ v1_funct_1(X0)
% 2.15/0.99      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,X1,X0,sK2) ),
% 2.15/0.99      inference(renaming,[status(thm)],[c_465]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_31,negated_conjecture,
% 2.15/0.99      ( v2_pre_topc(sK0) ),
% 2.15/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_525,plain,
% 2.15/0.99      ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
% 2.15/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 2.15/0.99      | v2_struct_0(X1)
% 2.15/0.99      | ~ l1_pre_topc(X1)
% 2.15/0.99      | ~ v1_funct_1(X0)
% 2.15/0.99      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,X1,X0,sK2)
% 2.15/0.99      | sK0 != X1 ),
% 2.15/0.99      inference(resolution_lifted,[status(thm)],[c_466,c_31]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_526,plain,
% 2.15/0.99      ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
% 2.15/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.15/0.99      | v2_struct_0(sK0)
% 2.15/0.99      | ~ l1_pre_topc(sK0)
% 2.15/0.99      | ~ v1_funct_1(X0)
% 2.15/0.99      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,X0,sK2) ),
% 2.15/0.99      inference(unflattening,[status(thm)],[c_525]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_530,plain,
% 2.15/0.99      ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
% 2.15/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.15/0.99      | ~ v1_funct_1(X0)
% 2.15/0.99      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,X0,sK2) ),
% 2.15/0.99      inference(global_propositional_subsumption,
% 2.15/0.99                [status(thm)],
% 2.15/0.99                [c_526,c_32,c_30]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_726,plain,
% 2.15/0.99      ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
% 2.15/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.15/0.99      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,X0,sK2)
% 2.15/0.99      | sK3 != X0 ),
% 2.15/0.99      inference(resolution_lifted,[status(thm)],[c_530,c_24]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_727,plain,
% 2.15/0.99      ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
% 2.15/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.15/0.99      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,sK3,sK2) ),
% 2.15/0.99      inference(unflattening,[status(thm)],[c_726]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_729,plain,
% 2.15/0.99      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,sK3,sK2) ),
% 2.15/0.99      inference(global_propositional_subsumption,
% 2.15/0.99                [status(thm)],
% 2.15/0.99                [c_727,c_23,c_22]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_1557,plain,
% 2.15/0.99      ( k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
% 2.15/0.99      inference(demodulation,[status(thm)],[c_1554,c_729]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_2315,plain,
% 2.15/0.99      ( k7_relat_1(sK3,u1_struct_0(sK2)) != sK3
% 2.15/0.99      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
% 2.15/0.99      | v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top
% 2.15/0.99      | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) != iProver_top
% 2.15/0.99      | m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) != iProver_top ),
% 2.15/0.99      inference(light_normalisation,[status(thm)],[c_1318,c_1557,c_2014]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_2731,plain,
% 2.15/0.99      ( k7_relat_1(sK3,k1_relat_1(sK3)) != sK3
% 2.15/0.99      | v1_funct_2(k7_relat_1(sK3,k1_relat_1(sK3)),k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top
% 2.15/0.99      | m1_subset_1(k7_relat_1(sK3,k1_relat_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) != iProver_top ),
% 2.15/0.99      inference(demodulation,[status(thm)],[c_2583,c_2315]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_1462,plain,
% 2.15/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.15/0.99      | v1_relat_1(sK3) ),
% 2.15/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_3,plain,
% 2.15/0.99      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 2.15/0.99      | ~ v1_relat_1(X0)
% 2.15/0.99      | k7_relat_1(X0,X1) = X0 ),
% 2.15/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_1512,plain,
% 2.15/0.99      ( ~ r1_tarski(k1_relat_1(sK3),X0)
% 2.15/0.99      | ~ v1_relat_1(sK3)
% 2.15/0.99      | k7_relat_1(sK3,X0) = sK3 ),
% 2.15/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_1658,plain,
% 2.15/0.99      ( ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3))
% 2.15/0.99      | ~ v1_relat_1(sK3)
% 2.15/0.99      | k7_relat_1(sK3,k1_relat_1(sK3)) = sK3 ),
% 2.15/0.99      inference(instantiation,[status(thm)],[c_1512]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_1,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f82]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_1659,plain,
% 2.15/0.99      ( r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) ),
% 2.15/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_3352,plain,
% 2.15/0.99      ( v1_funct_2(k7_relat_1(sK3,k1_relat_1(sK3)),k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top
% 2.15/0.99      | m1_subset_1(k7_relat_1(sK3,k1_relat_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) != iProver_top ),
% 2.15/0.99      inference(global_propositional_subsumption,
% 2.15/0.99                [status(thm)],
% 2.15/0.99                [c_2731,c_22,c_1462,c_1658,c_1659]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_1328,plain,
% 2.15/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.15/0.99      | v1_relat_1(X0) = iProver_top ),
% 2.15/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_1785,plain,
% 2.15/0.99      ( v1_relat_1(sK3) = iProver_top ),
% 2.15/0.99      inference(superposition,[status(thm)],[c_1325,c_1328]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_1330,plain,
% 2.15/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 2.15/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_1329,plain,
% 2.15/0.99      ( k7_relat_1(X0,X1) = X0
% 2.15/0.99      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 2.15/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.15/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_1919,plain,
% 2.15/0.99      ( k7_relat_1(X0,k1_relat_1(X0)) = X0 | v1_relat_1(X0) != iProver_top ),
% 2.15/0.99      inference(superposition,[status(thm)],[c_1330,c_1329]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_2575,plain,
% 2.15/0.99      ( k7_relat_1(sK3,k1_relat_1(sK3)) = sK3 ),
% 2.15/0.99      inference(superposition,[status(thm)],[c_1785,c_1919]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_3356,plain,
% 2.15/0.99      ( v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0)) != iProver_top
% 2.15/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) != iProver_top ),
% 2.15/0.99      inference(light_normalisation,[status(thm)],[c_3352,c_2575]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_2019,plain,
% 2.15/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) = iProver_top ),
% 2.15/0.99      inference(demodulation,[status(thm)],[c_2014,c_1325]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_1324,plain,
% 2.15/0.99      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top ),
% 2.15/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_2020,plain,
% 2.15/0.99      ( v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0)) = iProver_top ),
% 2.15/0.99      inference(demodulation,[status(thm)],[c_2014,c_1324]) ).
% 2.15/0.99  
% 2.15/0.99  cnf(c_3359,plain,
% 2.15/0.99      ( $false ),
% 2.15/0.99      inference(forward_subsumption_resolution,
% 2.15/0.99                [status(thm)],
% 2.15/0.99                [c_3356,c_2019,c_2020]) ).
% 2.15/0.99  
% 2.15/0.99  
% 2.15/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.15/0.99  
% 2.15/0.99  ------                               Statistics
% 2.15/0.99  
% 2.15/0.99  ------ General
% 2.15/0.99  
% 2.15/0.99  abstr_ref_over_cycles:                  0
% 2.15/0.99  abstr_ref_under_cycles:                 0
% 2.15/0.99  gc_basic_clause_elim:                   0
% 2.15/0.99  forced_gc_time:                         0
% 2.15/0.99  parsing_time:                           0.009
% 2.15/0.99  unif_index_cands_time:                  0.
% 2.15/0.99  unif_index_add_time:                    0.
% 2.15/0.99  orderings_time:                         0.
% 2.15/0.99  out_proof_time:                         0.01
% 2.15/0.99  total_time:                             0.148
% 2.15/0.99  num_of_symbols:                         58
% 2.15/0.99  num_of_terms:                           4066
% 2.15/0.99  
% 2.15/0.99  ------ Preprocessing
% 2.15/0.99  
% 2.15/0.99  num_of_splits:                          0
% 2.15/0.99  num_of_split_atoms:                     0
% 2.15/0.99  num_of_reused_defs:                     0
% 2.15/0.99  num_eq_ax_congr_red:                    15
% 2.15/0.99  num_of_sem_filtered_clauses:            1
% 2.15/0.99  num_of_subtypes:                        0
% 2.15/0.99  monotx_restored_types:                  0
% 2.15/0.99  sat_num_of_epr_types:                   0
% 2.15/0.99  sat_num_of_non_cyclic_types:            0
% 2.15/0.99  sat_guarded_non_collapsed_types:        0
% 2.15/0.99  num_pure_diseq_elim:                    0
% 2.15/0.99  simp_replaced_by:                       0
% 2.15/0.99  res_preprocessed:                       117
% 2.15/0.99  prep_upred:                             0
% 2.15/0.99  prep_unflattend:                        37
% 2.15/0.99  smt_new_axioms:                         0
% 2.15/0.99  pred_elim_cands:                        4
% 2.15/0.99  pred_elim:                              10
% 2.15/0.99  pred_elim_cl:                           12
% 2.15/0.99  pred_elim_cycles:                       14
% 2.15/0.99  merged_defs:                            0
% 2.15/0.99  merged_defs_ncl:                        0
% 2.15/0.99  bin_hyper_res:                          0
% 2.15/0.99  prep_cycles:                            4
% 2.15/0.99  pred_elim_time:                         0.019
% 2.15/0.99  splitting_time:                         0.
% 2.15/0.99  sem_filter_time:                        0.
% 2.15/0.99  monotx_time:                            0.
% 2.15/0.99  subtype_inf_time:                       0.
% 2.15/0.99  
% 2.15/0.99  ------ Problem properties
% 2.15/0.99  
% 2.15/0.99  clauses:                                19
% 2.15/0.99  conjectures:                            3
% 2.15/0.99  epr:                                    2
% 2.15/0.99  horn:                                   19
% 2.15/0.99  ground:                                 9
% 2.15/0.99  unary:                                  8
% 2.15/0.99  binary:                                 2
% 2.15/0.99  lits:                                   41
% 2.15/0.99  lits_eq:                                14
% 2.15/0.99  fd_pure:                                0
% 2.15/0.99  fd_pseudo:                              0
% 2.15/0.99  fd_cond:                                3
% 2.15/0.99  fd_pseudo_cond:                         3
% 2.15/0.99  ac_symbols:                             0
% 2.15/0.99  
% 2.15/0.99  ------ Propositional Solver
% 2.15/0.99  
% 2.15/0.99  prop_solver_calls:                      26
% 2.15/0.99  prop_fast_solver_calls:                 814
% 2.15/0.99  smt_solver_calls:                       0
% 2.15/0.99  smt_fast_solver_calls:                  0
% 2.15/0.99  prop_num_of_clauses:                    1275
% 2.15/0.99  prop_preprocess_simplified:             4519
% 2.15/0.99  prop_fo_subsumed:                       21
% 2.15/0.99  prop_solver_time:                       0.
% 2.15/0.99  smt_solver_time:                        0.
% 2.15/0.99  smt_fast_solver_time:                   0.
% 2.15/0.99  prop_fast_solver_time:                  0.
% 2.15/0.99  prop_unsat_core_time:                   0.
% 2.15/0.99  
% 2.15/0.99  ------ QBF
% 2.15/0.99  
% 2.15/0.99  qbf_q_res:                              0
% 2.15/0.99  qbf_num_tautologies:                    0
% 2.15/0.99  qbf_prep_cycles:                        0
% 2.15/0.99  
% 2.15/0.99  ------ BMC1
% 2.15/0.99  
% 2.15/0.99  bmc1_current_bound:                     -1
% 2.15/0.99  bmc1_last_solved_bound:                 -1
% 2.15/0.99  bmc1_unsat_core_size:                   -1
% 2.15/0.99  bmc1_unsat_core_parents_size:           -1
% 2.15/0.99  bmc1_merge_next_fun:                    0
% 2.15/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.15/0.99  
% 2.15/0.99  ------ Instantiation
% 2.15/0.99  
% 2.15/0.99  inst_num_of_clauses:                    373
% 2.15/0.99  inst_num_in_passive:                    117
% 2.15/0.99  inst_num_in_active:                     184
% 2.15/0.99  inst_num_in_unprocessed:                72
% 2.15/0.99  inst_num_of_loops:                      190
% 2.15/0.99  inst_num_of_learning_restarts:          0
% 2.15/0.99  inst_num_moves_active_passive:          4
% 2.15/0.99  inst_lit_activity:                      0
% 2.15/0.99  inst_lit_activity_moves:                0
% 2.15/0.99  inst_num_tautologies:                   0
% 2.15/0.99  inst_num_prop_implied:                  0
% 2.15/0.99  inst_num_existing_simplified:           0
% 2.15/0.99  inst_num_eq_res_simplified:             0
% 2.15/0.99  inst_num_child_elim:                    0
% 2.15/0.99  inst_num_of_dismatching_blockings:      136
% 2.15/0.99  inst_num_of_non_proper_insts:           376
% 2.15/0.99  inst_num_of_duplicates:                 0
% 2.15/0.99  inst_inst_num_from_inst_to_res:         0
% 2.15/0.99  inst_dismatching_checking_time:         0.
% 2.15/0.99  
% 2.15/0.99  ------ Resolution
% 2.15/0.99  
% 2.15/0.99  res_num_of_clauses:                     0
% 2.15/0.99  res_num_in_passive:                     0
% 2.15/0.99  res_num_in_active:                      0
% 2.15/0.99  res_num_of_loops:                       121
% 2.15/0.99  res_forward_subset_subsumed:            39
% 2.15/0.99  res_backward_subset_subsumed:           0
% 2.15/0.99  res_forward_subsumed:                   0
% 2.15/0.99  res_backward_subsumed:                  0
% 2.15/0.99  res_forward_subsumption_resolution:     1
% 2.15/0.99  res_backward_subsumption_resolution:    0
% 2.15/0.99  res_clause_to_clause_subsumption:       68
% 2.15/0.99  res_orphan_elimination:                 0
% 2.15/0.99  res_tautology_del:                      28
% 2.15/0.99  res_num_eq_res_simplified:              0
% 2.15/0.99  res_num_sel_changes:                    0
% 2.15/0.99  res_moves_from_active_to_pass:          0
% 2.15/0.99  
% 2.15/0.99  ------ Superposition
% 2.15/0.99  
% 2.15/0.99  sup_time_total:                         0.
% 2.15/0.99  sup_time_generating:                    0.
% 2.15/0.99  sup_time_sim_full:                      0.
% 2.15/0.99  sup_time_sim_immed:                     0.
% 2.15/0.99  
% 2.15/0.99  sup_num_of_clauses:                     30
% 2.15/0.99  sup_num_in_active:                      23
% 2.15/0.99  sup_num_in_passive:                     7
% 2.15/0.99  sup_num_of_loops:                       37
% 2.15/0.99  sup_fw_superposition:                   12
% 2.15/0.99  sup_bw_superposition:                   7
% 2.15/0.99  sup_immediate_simplified:               2
% 2.15/0.99  sup_given_eliminated:                   2
% 2.15/0.99  comparisons_done:                       0
% 2.15/0.99  comparisons_avoided:                    0
% 2.15/0.99  
% 2.15/0.99  ------ Simplifications
% 2.15/0.99  
% 2.15/0.99  
% 2.15/0.99  sim_fw_subset_subsumed:                 2
% 2.15/0.99  sim_bw_subset_subsumed:                 2
% 2.15/0.99  sim_fw_subsumed:                        0
% 2.15/0.99  sim_bw_subsumed:                        0
% 2.15/0.99  sim_fw_subsumption_res:                 2
% 2.15/0.99  sim_bw_subsumption_res:                 0
% 2.15/0.99  sim_tautology_del:                      0
% 2.15/0.99  sim_eq_tautology_del:                   9
% 2.15/0.99  sim_eq_res_simp:                        0
% 2.15/0.99  sim_fw_demodulated:                     0
% 2.15/0.99  sim_bw_demodulated:                     14
% 2.15/0.99  sim_light_normalised:                   6
% 2.15/0.99  sim_joinable_taut:                      0
% 2.15/0.99  sim_joinable_simp:                      0
% 2.15/0.99  sim_ac_normalised:                      0
% 2.15/0.99  sim_smt_subsumption:                    0
% 2.15/0.99  
%------------------------------------------------------------------------------
