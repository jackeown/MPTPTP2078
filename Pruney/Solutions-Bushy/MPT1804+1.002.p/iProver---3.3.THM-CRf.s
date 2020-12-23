%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1804+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:30 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 722 expanded)
%              Number of clauses        :  101 ( 215 expanded)
%              Number of leaves         :   14 ( 192 expanded)
%              Depth                    :   25
%              Number of atoms          : 1007 (6376 expanded)
%              Number of equality atoms :  134 ( 206 expanded)
%              Maximal formula depth    :   21 (   7 average)
%              Maximal clause size      :   24 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( l1_struct_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(X2)
        & l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f12,conjecture,(
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
               => ( m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))))
                  & v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1))
                  & v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))
                  & v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
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
                 => ( m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))))
                    & v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1))
                    & v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))
                    & v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))))
                | ~ v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1))
                | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))
                | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)) )
              & r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))))
                | ~ v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1))
                | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))
                | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)) )
              & r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))))
            | ~ v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1))
            | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))
            | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)) )
          & r1_tsep_1(X1,X2)
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ( ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(X0,X1)))))
          | ~ v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),sK3),sK3,k8_tmap_1(X0,X1))
          | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(X0,X1)))
          | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),sK3)) )
        & r1_tsep_1(X1,sK3)
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))))
                | ~ v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1))
                | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))
                | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)) )
              & r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ( ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,sK2)))))
              | ~ v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),X2),X2,k8_tmap_1(X0,sK2))
              | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,sK2)))
              | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),X2)) )
            & r1_tsep_1(sK2,X2)
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))))
                  | ~ v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1))
                  | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))
                  | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)) )
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
              ( ( ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,X1),k9_tmap_1(sK1,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK1,X1)))))
                | ~ v5_pre_topc(k2_tmap_1(sK1,k8_tmap_1(sK1,X1),k9_tmap_1(sK1,X1),X2),X2,k8_tmap_1(sK1,X1))
                | ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,X1),k9_tmap_1(sK1,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK1,X1)))
                | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,X1),k9_tmap_1(sK1,X1),X2)) )
              & r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,sK1)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ( ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK1,sK2)))))
      | ~ v5_pre_topc(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3),sK3,k8_tmap_1(sK1,sK2))
      | ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK1,sK2)))
      | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)) )
    & r1_tsep_1(sK2,sK3)
    & m1_pre_topc(sK3,sK1)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f37,f44,f43,f42])).

fof(f74,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | ~ v5_pre_topc(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3),sK3,k8_tmap_1(sK1,sK2))
    | ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)) ),
    inference(cnf_transformation,[],[f45])).

fof(f11,axiom,(
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
             => ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => r1_tmap_1(X1,X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X1,X0)
                  | ? [X3] :
                      ( ~ r1_tmap_1(X1,X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X1)) ) )
                & ( ! [X3] :
                      ( r1_tmap_1(X1,X0,X2,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                  | ~ v5_pre_topc(X2,X1,X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X1,X0)
                  | ? [X3] :
                      ( ~ r1_tmap_1(X1,X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X1)) ) )
                & ( ! [X4] :
                      ( r1_tmap_1(X1,X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ v5_pre_topc(X2,X1,X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tmap_1(X1,X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_tmap_1(X1,X0,X2,sK0(X0,X1,X2))
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X1,X0)
                  | ( ~ r1_tmap_1(X1,X0,X2,sK0(X0,X1,X2))
                    & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X1)) ) )
                & ( ! [X4] :
                      ( r1_tmap_1(X1,X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ v5_pre_topc(X2,X1,X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X1,X0)
      | ~ r1_tmap_1(X1,X0,X2,sK0(X0,X1,X2))
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

fof(f10,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | ~ r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | ~ r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f73,plain,(
    r1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f69,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f71,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f59,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f54,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1))
        & ~ v2_struct_0(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k8_tmap_1(X0,X1))
        & ~ v2_struct_0(k8_tmap_1(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k8_tmap_1(X0,X1))
        & ~ v2_struct_0(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k8_tmap_1(X0,X1))
        & ~ v2_struct_0(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f66,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f67,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f68,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f70,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f72,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X1,X0)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X1))
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

fof(f61,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f58,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k9_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_697,plain,
    ( ~ v1_funct_2(X0_50,u1_struct_0(X0_52),u1_struct_0(X1_52))
    | v1_funct_2(k2_tmap_1(X0_52,X1_52,X0_50,X2_52),u1_struct_0(X2_52),u1_struct_0(X1_52))
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | ~ l1_struct_0(X2_52)
    | ~ l1_struct_0(X1_52)
    | ~ l1_struct_0(X0_52)
    | ~ v1_funct_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1209,plain,
    ( v1_funct_2(X0_50,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
    | v1_funct_2(k2_tmap_1(X0_52,X1_52,X0_50,X2_52),u1_struct_0(X2_52),u1_struct_0(X1_52)) = iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
    | l1_struct_0(X0_52) != iProver_top
    | l1_struct_0(X2_52) != iProver_top
    | l1_struct_0(X1_52) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_697])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_698,plain,
    ( ~ v1_funct_2(X0_50,u1_struct_0(X0_52),u1_struct_0(X1_52))
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | m1_subset_1(k2_tmap_1(X0_52,X1_52,X0_50,X2_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52))))
    | ~ l1_struct_0(X2_52)
    | ~ l1_struct_0(X1_52)
    | ~ l1_struct_0(X0_52)
    | ~ v1_funct_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1208,plain,
    ( v1_funct_2(X0_50,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
    | m1_subset_1(k2_tmap_1(X0_52,X1_52,X0_50,X2_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52)))) = iProver_top
    | l1_struct_0(X0_52) != iProver_top
    | l1_struct_0(X2_52) != iProver_top
    | l1_struct_0(X1_52) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_698])).

cnf(c_20,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3),sK3,k8_tmap_1(sK1,sK2))
    | ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_17,plain,
    ( ~ r1_tmap_1(X0,X1,X2,sK0(X1,X0,X2))
    | v5_pre_topc(X2,X0,X1)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_16,plain,
    ( r1_tmap_1(X0,k8_tmap_1(X1,X2),k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X0),X3)
    | ~ r1_tsep_1(X2,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_21,negated_conjecture,
    ( r1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_312,plain,
    ( r1_tmap_1(X0,k8_tmap_1(X1,X2),k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X0),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | sK3 != X0
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_21])).

cnf(c_313,plain,
    ( r1_tmap_1(sK3,k8_tmap_1(X0,sK2),k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),sK3),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK3,X0)
    | ~ m1_pre_topc(sK2,X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_312])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_317,plain,
    ( r1_tmap_1(sK3,k8_tmap_1(X0,sK2),k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),sK3),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK3,X0)
    | ~ m1_pre_topc(sK2,X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_313,c_25,c_23])).

cnf(c_355,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK3,X4)
    | ~ m1_pre_topc(sK2,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X4)
    | k2_tmap_1(X4,k8_tmap_1(X4,sK2),k9_tmap_1(X4,sK2),sK3) != X0
    | sK0(X2,X1,X0) != X3
    | k8_tmap_1(X4,sK2) != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_317])).

cnf(c_356,plain,
    ( v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),sK3),sK3,k8_tmap_1(X0,sK2))
    | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(X0,sK2)))
    | ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(X0,sK2)))))
    | ~ m1_subset_1(sK0(k8_tmap_1(X0,sK2),sK3,k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),sK3)),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK3,X0)
    | ~ m1_pre_topc(sK2,X0)
    | v2_struct_0(X0)
    | v2_struct_0(k8_tmap_1(X0,sK2))
    | v2_struct_0(sK3)
    | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),sK3))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(k8_tmap_1(X0,sK2))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(k8_tmap_1(X0,sK2))
    | ~ v2_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_355])).

cnf(c_360,plain,
    ( v2_struct_0(k8_tmap_1(X0,sK2))
    | v2_struct_0(X0)
    | ~ m1_pre_topc(sK2,X0)
    | ~ m1_pre_topc(sK3,X0)
    | ~ m1_subset_1(sK0(k8_tmap_1(X0,sK2),sK3,k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),sK3)),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(X0,sK2)))))
    | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(X0,sK2)))
    | v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),sK3),sK3,k8_tmap_1(X0,sK2))
    | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),sK3))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(k8_tmap_1(X0,sK2))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(k8_tmap_1(X0,sK2))
    | ~ v2_pre_topc(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_356,c_23])).

cnf(c_361,plain,
    ( v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),sK3),sK3,k8_tmap_1(X0,sK2))
    | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(X0,sK2)))
    | ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(X0,sK2)))))
    | ~ m1_subset_1(sK0(k8_tmap_1(X0,sK2),sK3,k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),sK3)),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK3,X0)
    | ~ m1_pre_topc(sK2,X0)
    | v2_struct_0(X0)
    | v2_struct_0(k8_tmap_1(X0,sK2))
    | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),sK3))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(k8_tmap_1(X0,sK2))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(k8_tmap_1(X0,sK2))
    | ~ v2_pre_topc(sK3) ),
    inference(renaming,[status(thm)],[c_360])).

cnf(c_0,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_13,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(k8_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_396,plain,
    ( v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),sK3),sK3,k8_tmap_1(X0,sK2))
    | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(X0,sK2)))
    | ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(X0,sK2)))))
    | ~ m1_subset_1(sK0(k8_tmap_1(X0,sK2),sK3,k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),sK3)),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK3,X0)
    | ~ m1_pre_topc(sK2,X0)
    | v2_struct_0(X0)
    | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),sK3))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_361,c_0,c_8,c_13,c_7,c_15])).

cnf(c_453,plain,
    ( ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(X0,sK2)))
    | ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(X0,sK2)))))
    | ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | ~ m1_subset_1(sK0(k8_tmap_1(X0,sK2),sK3,k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),sK3)),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK3,X0)
    | ~ m1_pre_topc(sK2,X0)
    | v2_struct_0(X0)
    | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),sK3))
    | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
    | k8_tmap_1(X0,sK2) != k8_tmap_1(sK1,sK2)
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_396])).

cnf(c_537,plain,
    ( ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(X0,sK2)))
    | ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(X0,sK2)))))
    | ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | ~ m1_subset_1(sK0(k8_tmap_1(X0,sK2),sK3,k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),sK3)),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK3,X0)
    | ~ m1_pre_topc(sK2,X0)
    | v2_struct_0(X0)
    | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),sK3))
    | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | k2_tmap_1(X0,k8_tmap_1(X0,sK2),k9_tmap_1(X0,sK2),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)
    | k8_tmap_1(X0,sK2) != k8_tmap_1(sK1,sK2) ),
    inference(equality_resolution_simp,[status(thm)],[c_453])).

cnf(c_679,plain,
    ( ~ v1_funct_2(k2_tmap_1(X0_52,k8_tmap_1(X0_52,sK2),k9_tmap_1(X0_52,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(X0_52,sK2)))
    | ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k2_tmap_1(X0_52,k8_tmap_1(X0_52,sK2),k9_tmap_1(X0_52,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(X0_52,sK2)))))
    | ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | ~ m1_subset_1(sK0(k8_tmap_1(X0_52,sK2),sK3,k2_tmap_1(X0_52,k8_tmap_1(X0_52,sK2),k9_tmap_1(X0_52,sK2),sK3)),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK3,X0_52)
    | ~ m1_pre_topc(sK2,X0_52)
    | v2_struct_0(X0_52)
    | ~ v1_funct_1(k2_tmap_1(X0_52,k8_tmap_1(X0_52,sK2),k9_tmap_1(X0_52,sK2),sK3))
    | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3))
    | ~ l1_pre_topc(X0_52)
    | ~ v2_pre_topc(X0_52)
    | k8_tmap_1(X0_52,sK2) != k8_tmap_1(sK1,sK2)
    | k2_tmap_1(X0_52,k8_tmap_1(X0_52,sK2),k9_tmap_1(X0_52,sK2),sK3) != k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3) ),
    inference(subtyping,[status(esa)],[c_537])).

cnf(c_704,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_679])).

cnf(c_1227,plain,
    ( v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK1,sK2))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK1,sK2))))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_704])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_29,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_30,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_31,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_24,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_33,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_22,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_35,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_18,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK0(X2,X1,X0),u1_struct_0(X1))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_421,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | m1_subset_1(sK0(X2,X1,X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3) != X0
    | k8_tmap_1(sK1,sK2) != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_20])).

cnf(c_422,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | m1_subset_1(sK0(k8_tmap_1(sK1,sK2),sK3,k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)),u1_struct_0(sK3))
    | v2_struct_0(k8_tmap_1(sK1,sK2))
    | v2_struct_0(sK3)
    | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3))
    | ~ l1_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ v2_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_421])).

cnf(c_408,plain,
    ( v5_pre_topc(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3),sK3,k8_tmap_1(sK1,sK2))
    | ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | ~ m1_subset_1(sK0(k8_tmap_1(sK1,sK2),sK3,k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK1)
    | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_396])).

cnf(c_424,plain,
    ( v2_struct_0(k8_tmap_1(sK1,sK2))
    | ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3))
    | ~ l1_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ v2_pre_topc(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_422,c_28,c_27,c_26,c_24,c_23,c_22,c_20,c_408])).

cnf(c_425,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | v2_struct_0(k8_tmap_1(sK1,sK2))
    | ~ v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3))
    | ~ l1_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ v2_pre_topc(sK3) ),
    inference(renaming,[status(thm)],[c_424])).

cnf(c_426,plain,
    ( v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK1,sK2))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK1,sK2))))) != iProver_top
    | v2_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)) != iProver_top
    | l1_pre_topc(k8_tmap_1(sK1,sK2)) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(k8_tmap_1(sK1,sK2)) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_425])).

cnf(c_689,plain,
    ( ~ m1_pre_topc(X0_52,X1_52)
    | ~ l1_pre_topc(X1_52)
    | l1_pre_topc(X0_52) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1506,plain,
    ( ~ m1_pre_topc(sK3,X0_52)
    | ~ l1_pre_topc(X0_52)
    | l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_689])).

cnf(c_1507,plain,
    ( m1_pre_topc(sK3,X0_52) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1506])).

cnf(c_1509,plain,
    ( m1_pre_topc(sK3,sK1) != iProver_top
    | l1_pre_topc(sK3) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1507])).

cnf(c_688,plain,
    ( ~ m1_pre_topc(X0_52,X1_52)
    | v2_struct_0(X1_52)
    | ~ v2_struct_0(k8_tmap_1(X1_52,X0_52))
    | ~ l1_pre_topc(X1_52)
    | ~ v2_pre_topc(X1_52) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1519,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ v2_struct_0(k8_tmap_1(sK1,sK2))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_688])).

cnf(c_1520,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(k8_tmap_1(sK1,sK2)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1519])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_694,plain,
    ( ~ m1_pre_topc(X0_52,X1_52)
    | v2_struct_0(X1_52)
    | ~ l1_pre_topc(X1_52)
    | ~ v2_pre_topc(X1_52)
    | v2_pre_topc(k8_tmap_1(X1_52,X0_52)) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1535,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_694])).

cnf(c_1536,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(k8_tmap_1(sK1,sK2)) = iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1535])).

cnf(c_695,plain,
    ( ~ m1_pre_topc(X0_52,X1_52)
    | v2_struct_0(X1_52)
    | ~ l1_pre_topc(X1_52)
    | l1_pre_topc(k8_tmap_1(X1_52,X0_52))
    | ~ v2_pre_topc(X1_52) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1541,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK1)
    | l1_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_695])).

cnf(c_1542,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK1,sK2)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1541])).

cnf(c_687,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1219,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_687])).

cnf(c_702,plain,
    ( ~ m1_pre_topc(X0_52,X1_52)
    | ~ l1_pre_topc(X1_52)
    | ~ v2_pre_topc(X1_52)
    | v2_pre_topc(X0_52) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1204,plain,
    ( m1_pre_topc(X0_52,X1_52) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(X0_52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_702])).

cnf(c_1621,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK3) = iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1219,c_1204])).

cnf(c_2152,plain,
    ( v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK1,sK2))))) != iProver_top
    | v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK1,sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1227,c_29,c_30,c_31,c_33,c_35,c_426,c_1509,c_1520,c_1536,c_1542,c_1621])).

cnf(c_2153,plain,
    ( v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK1,sK2))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK1,sK2))))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2152])).

cnf(c_2584,plain,
    ( v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK1,sK2))) != iProver_top
    | v1_funct_2(k9_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2))) != iProver_top
    | m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2))))) != iProver_top
    | l1_struct_0(k8_tmap_1(sK1,sK2)) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)) != iProver_top
    | v1_funct_1(k9_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1208,c_2153])).

cnf(c_12,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_57,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_59,plain,
    ( l1_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_57])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v1_funct_1(k9_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_691,plain,
    ( ~ m1_pre_topc(X0_52,X1_52)
    | v2_struct_0(X1_52)
    | v1_funct_1(k9_tmap_1(X1_52,X0_52))
    | ~ l1_pre_topc(X1_52)
    | ~ v2_pre_topc(X1_52) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1529,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK1)
    | v1_funct_1(k9_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_691])).

cnf(c_1530,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v1_funct_1(k9_tmap_1(sK1,sK2)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1529])).

cnf(c_10,plain,
    ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_692,plain,
    ( v1_funct_2(k9_tmap_1(X0_52,X1_52),u1_struct_0(X0_52),u1_struct_0(k8_tmap_1(X0_52,X1_52)))
    | ~ m1_pre_topc(X1_52,X0_52)
    | v2_struct_0(X0_52)
    | ~ l1_pre_topc(X0_52)
    | ~ v2_pre_topc(X0_52) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1561,plain,
    ( v1_funct_2(k9_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_692])).

cnf(c_1562,plain,
    ( v1_funct_2(k9_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2))) = iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1561])).

cnf(c_9,plain,
    ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_693,plain,
    ( m1_subset_1(k9_tmap_1(X0_52,X1_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(k8_tmap_1(X0_52,X1_52)))))
    | ~ m1_pre_topc(X1_52,X0_52)
    | v2_struct_0(X0_52)
    | ~ l1_pre_topc(X0_52)
    | ~ v2_pre_topc(X0_52) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1567,plain,
    ( m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_693])).

cnf(c_1568,plain,
    ( m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2))))) = iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1567])).

cnf(c_1217,plain,
    ( m1_pre_topc(X0_52,X1_52) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X0_52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_689])).

cnf(c_1707,plain,
    ( l1_pre_topc(sK3) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1219,c_1217])).

cnf(c_1849,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1707,c_31,c_35,c_1509])).

cnf(c_690,plain,
    ( l1_struct_0(X0_52)
    | ~ l1_pre_topc(X0_52) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1216,plain,
    ( l1_struct_0(X0_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_690])).

cnf(c_1854,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1849,c_1216])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tmap_1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_696,plain,
    ( ~ v1_funct_2(X0_50,u1_struct_0(X0_52),u1_struct_0(X1_52))
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | ~ l1_struct_0(X2_52)
    | ~ l1_struct_0(X1_52)
    | ~ l1_struct_0(X0_52)
    | ~ v1_funct_1(X0_50)
    | v1_funct_1(k2_tmap_1(X0_52,X1_52,X0_50,X2_52)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1645,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK1,sK2),u1_struct_0(X0_52),u1_struct_0(X1_52))
    | ~ m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | ~ l1_struct_0(X2_52)
    | ~ l1_struct_0(X1_52)
    | ~ l1_struct_0(X0_52)
    | v1_funct_1(k2_tmap_1(X0_52,X1_52,k9_tmap_1(sK1,sK2),X2_52))
    | ~ v1_funct_1(k9_tmap_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_696])).

cnf(c_1893,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | ~ l1_struct_0(X0_52)
    | ~ l1_struct_0(k8_tmap_1(sK1,sK2))
    | ~ l1_struct_0(sK1)
    | v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),X0_52))
    | ~ v1_funct_1(k9_tmap_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1645])).

cnf(c_2107,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))
    | ~ m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2)))))
    | ~ l1_struct_0(k8_tmap_1(sK1,sK2))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK1)
    | v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3))
    | ~ v1_funct_1(k9_tmap_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1893])).

cnf(c_2108,plain,
    ( v1_funct_2(k9_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2))) != iProver_top
    | m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2))))) != iProver_top
    | l1_struct_0(k8_tmap_1(sK1,sK2)) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3)) = iProver_top
    | v1_funct_1(k9_tmap_1(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2107])).

cnf(c_2309,plain,
    ( l1_struct_0(k8_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(k8_tmap_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_690])).

cnf(c_2310,plain,
    ( l1_struct_0(k8_tmap_1(sK1,sK2)) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2309])).

cnf(c_2683,plain,
    ( v1_funct_2(k2_tmap_1(sK1,k8_tmap_1(sK1,sK2),k9_tmap_1(sK1,sK2),sK3),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK1,sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2584,c_29,c_30,c_31,c_33,c_59,c_1530,c_1542,c_1562,c_1568,c_1854,c_2108,c_2310])).

cnf(c_2688,plain,
    ( v1_funct_2(k9_tmap_1(sK1,sK2),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2))) != iProver_top
    | m1_subset_1(k9_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK1,sK2))))) != iProver_top
    | l1_struct_0(k8_tmap_1(sK1,sK2)) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | v1_funct_1(k9_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1209,c_2683])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2688,c_2310,c_1854,c_1568,c_1562,c_1542,c_1530,c_59,c_33,c_31,c_30,c_29])).


%------------------------------------------------------------------------------
