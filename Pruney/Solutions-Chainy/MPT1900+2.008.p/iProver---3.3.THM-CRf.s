%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:52 EST 2020

% Result     : Theorem 4.16s
% Output     : CNFRefutation 4.16s
% Verified   : 
% Statistics : Number of formulae       :  284 (2184 expanded)
%              Number of clauses        :  155 ( 605 expanded)
%              Number of leaves         :   41 ( 642 expanded)
%              Depth                    :   22
%              Number of atoms          : 1020 (13620 expanded)
%              Number of equality atoms :  286 ( 786 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f65])).

fof(f67,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f66,f67])).

fof(f99,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f62,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f61])).

fof(f63,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f62,f63])).

fof(f96,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f29,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => v5_pre_topc(X2,X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => v5_pre_topc(X2,X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f29])).

fof(f59,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_pre_topc(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f60,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_pre_topc(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f59])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v5_pre_topc(X2,X0,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ~ v5_pre_topc(sK8,X0,X1)
        & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK8,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f93,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_pre_topc(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
     => ( ? [X2] :
            ( ~ v5_pre_topc(X2,X0,sK7)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK7))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK7))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK7)
        & v2_pre_topc(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f92,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v5_pre_topc(X2,X0,X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_pre_topc(X2,sK6,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK6),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK6)
      & v1_tdlat_3(sK6)
      & v2_pre_topc(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f95,plain,
    ( ~ v5_pre_topc(sK8,sK6,sK7)
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    & v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))
    & v1_funct_1(sK8)
    & l1_pre_topc(sK7)
    & v2_pre_topc(sK7)
    & l1_pre_topc(sK6)
    & v1_tdlat_3(sK6)
    & v2_pre_topc(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f60,f94,f93,f92])).

fof(f156,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) ),
    inference(cnf_transformation,[],[f95])).

fof(f25,axiom,(
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
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f51])).

fof(f80,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f52])).

fof(f81,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f80])).

fof(f82,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK3(X0,X1,X2))))
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f83,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK3(X0,X1,X2))))
                    & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f81,f82])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f149,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f95])).

fof(f151,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f95])).

fof(f152,plain,(
    v2_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f95])).

fof(f153,plain,(
    l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f95])).

fof(f154,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f95])).

fof(f155,plain,(
    v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f95])).

fof(f157,plain,(
    ~ v5_pre_topc(sK8,sK6,sK7) ),
    inference(cnf_transformation,[],[f95])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f110,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f150,plain,(
    v1_tdlat_3(sK6) ),
    inference(cnf_transformation,[],[f95])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f101,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f126,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v2_struct_0(X0) )
     => v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f44,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f127,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f22,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f128,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f27,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f56,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f55])).

fof(f84,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f56])).

fof(f85,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f84])).

fof(f86,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK4(X0),X0)
        & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f87,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK4(X0),X0)
            & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f85,f86])).

fof(f143,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( k1_xboole_0 = k2_struct_0(X1)
                 => k1_xboole_0 = k2_struct_0(X0) )
               => ( v5_pre_topc(X2,X0,X1)
                <=> ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( v3_pre_topc(X3,X1)
                       => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f49])).

fof(f76,plain,(
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
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f50])).

fof(f77,plain,(
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
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f76])).

fof(f78,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v3_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0)
        & v3_pre_topc(sK2(X0,X1,X2),X1)
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0)
                    & v3_pre_topc(sK2(X0,X1,X2),X1)
                    & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v3_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f77,f78])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0)
      | k1_xboole_0 = k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f117,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f102,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f69])).

fof(f105,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK3(X0,X1,X2))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f97,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f98,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v5_relat_1(k1_xboole_0,X1)
      & v4_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : v4_relat_1(k1_xboole_0,X0) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f74,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(rectify,[],[f31])).

fof(f114,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f74])).

fof(f12,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f115,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f19,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f125,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f158,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f115,f125])).

fof(f18,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f123,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f71])).

fof(f108,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f72])).

fof(f161,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f108])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f113,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f121,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f129,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f28,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f58,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f57])).

fof(f88,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f58])).

fof(f89,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f88])).

fof(f90,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK5(X0),X0)
        & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f91,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ( ~ v4_pre_topc(sK5(X0),X0)
            & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f89,f90])).

fof(f146,plain,(
    ! [X2,X0] :
      ( v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f109,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_2282,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2284,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4304,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2282,c_2284])).

cnf(c_53,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) ),
    inference(cnf_transformation,[],[f156])).

cnf(c_2237,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_53])).

cnf(c_43,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK3(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f140])).

cnf(c_2247,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v5_pre_topc(X0,X1,X2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(sK3(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_7909,plain,
    ( v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
    | v5_pre_topc(sK8,sK6,sK7) = iProver_top
    | m1_subset_1(sK3(sK6,sK7,sK8),k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top
    | v1_funct_1(sK8) != iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2237,c_2247])).

cnf(c_60,negated_conjecture,
    ( v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f149])).

cnf(c_61,plain,
    ( v2_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_60])).

cnf(c_58,negated_conjecture,
    ( l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f151])).

cnf(c_63,plain,
    ( l1_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_58])).

cnf(c_57,negated_conjecture,
    ( v2_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f152])).

cnf(c_64,plain,
    ( v2_pre_topc(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_57])).

cnf(c_56,negated_conjecture,
    ( l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f153])).

cnf(c_65,plain,
    ( l1_pre_topc(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_56])).

cnf(c_55,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f154])).

cnf(c_66,plain,
    ( v1_funct_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_55])).

cnf(c_54,negated_conjecture,
    ( v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f155])).

cnf(c_67,plain,
    ( v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_68,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_53])).

cnf(c_52,negated_conjecture,
    ( ~ v5_pre_topc(sK8,sK6,sK7) ),
    inference(cnf_transformation,[],[f157])).

cnf(c_69,plain,
    ( v5_pre_topc(sK8,sK6,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_3055,plain,
    ( ~ v1_funct_2(sK8,u1_struct_0(X0),u1_struct_0(X1))
    | v5_pre_topc(sK8,X0,X1)
    | m1_subset_1(sK3(X0,X1,sK8),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(sK8)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_43])).

cnf(c_3386,plain,
    ( ~ v1_funct_2(sK8,u1_struct_0(X0),u1_struct_0(sK7))
    | v5_pre_topc(sK8,X0,sK7)
    | m1_subset_1(sK3(X0,sK7,sK8),k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK7))))
    | ~ v1_funct_1(sK8)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK7)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK7) ),
    inference(instantiation,[status(thm)],[c_3055])).

cnf(c_3537,plain,
    ( ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))
    | v5_pre_topc(sK8,sK6,sK7)
    | m1_subset_1(sK3(sK6,sK7,sK8),k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | ~ v1_funct_1(sK8)
    | ~ v2_pre_topc(sK7)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK7)
    | ~ l1_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_3386])).

cnf(c_3538,plain,
    ( v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
    | v5_pre_topc(sK8,sK6,sK7) = iProver_top
    | m1_subset_1(sK3(sK6,sK7,sK8),k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) != iProver_top
    | v1_funct_1(sK8) != iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3537])).

cnf(c_8535,plain,
    ( m1_subset_1(sK3(sK6,sK7,sK8),k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7909,c_61,c_63,c_64,c_65,c_66,c_67,c_68,c_69,c_3538])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_2274,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_8540,plain,
    ( r1_tarski(sK3(sK6,sK7,sK8),u1_struct_0(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8535,c_2274])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_2270,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_8009,plain,
    ( v1_xboole_0(u1_struct_0(sK7)) != iProver_top
    | v1_xboole_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2237,c_2270])).

cnf(c_59,negated_conjecture,
    ( v1_tdlat_3(sK6) ),
    inference(cnf_transformation,[],[f150])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_194,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_29,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_2855,plain,
    ( ~ l1_pre_topc(sK7)
    | l1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_2856,plain,
    ( l1_pre_topc(sK7) != iProver_top
    | l1_struct_0(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2855])).

cnf(c_30,plain,
    ( ~ v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_3177,plain,
    ( ~ v2_struct_0(sK7)
    | ~ l1_struct_0(sK7)
    | v1_xboole_0(u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_3178,plain,
    ( v2_struct_0(sK7) != iProver_top
    | l1_struct_0(sK7) != iProver_top
    | v1_xboole_0(u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3177])).

cnf(c_31,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0)) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_3176,plain,
    ( v2_struct_0(sK7)
    | ~ l1_struct_0(sK7)
    | ~ v1_xboole_0(k2_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_3180,plain,
    ( v2_struct_0(sK7) = iProver_top
    | l1_struct_0(sK7) != iProver_top
    | v1_xboole_0(k2_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3176])).

cnf(c_983,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_3554,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_struct_0(sK7))
    | k2_struct_0(sK7) != X0 ),
    inference(instantiation,[status(thm)],[c_983])).

cnf(c_3555,plain,
    ( k2_struct_0(sK7) != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3554])).

cnf(c_3557,plain,
    ( k2_struct_0(sK7) != k1_xboole_0
    | v1_xboole_0(k2_struct_0(sK7)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3555])).

cnf(c_48,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f143])).

cnf(c_2957,plain,
    ( v3_pre_topc(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v1_tdlat_3(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_48])).

cnf(c_3305,plain,
    ( v3_pre_topc(k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,X0),sK6)
    | ~ m1_subset_1(k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,X0),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v1_tdlat_3(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_2957])).

cnf(c_3772,plain,
    ( v3_pre_topc(k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,sK2(sK6,sK7,sK8)),sK6)
    | ~ m1_subset_1(k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,sK2(sK6,sK7,sK8)),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v1_tdlat_3(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_3305])).

cnf(c_35,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK2(X1,X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f137])).

cnf(c_3773,plain,
    ( ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))
    | v5_pre_topc(sK8,sK6,sK7)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,sK2(sK6,sK7,sK8)),sK6)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | ~ v1_funct_1(sK8)
    | ~ l1_pre_topc(sK7)
    | ~ l1_pre_topc(sK6)
    | k2_struct_0(sK7) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_5312,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK7))
    | v1_xboole_0(sK8) ),
    inference(resolution,[status(thm)],[c_20,c_53])).

cnf(c_5313,plain,
    ( v1_xboole_0(u1_struct_0(sK7)) != iProver_top
    | v1_xboole_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5312])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_2975,plain,
    ( m1_subset_1(k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,X0),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_5500,plain,
    ( m1_subset_1(k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,sK2(sK6,sK7,sK8)),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) ),
    inference(instantiation,[status(thm)],[c_2975])).

cnf(c_8406,plain,
    ( v1_xboole_0(sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8009,c_60,c_59,c_58,c_56,c_65,c_55,c_54,c_53,c_52,c_194,c_2856,c_3178,c_3180,c_3557,c_3772,c_3773,c_5313,c_5500])).

cnf(c_6,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_2279,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_8411,plain,
    ( sK8 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8406,c_2279])).

cnf(c_9117,plain,
    ( r1_tarski(sK3(sK6,sK7,k1_xboole_0),u1_struct_0(sK7)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8540,c_8411])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_2278,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_9121,plain,
    ( sK3(sK6,sK7,k1_xboole_0) = u1_struct_0(sK7)
    | r1_tarski(u1_struct_0(sK7),sK3(sK6,sK7,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9117,c_2278])).

cnf(c_13877,plain,
    ( sK3(sK6,sK7,k1_xboole_0) = u1_struct_0(sK7)
    | v1_xboole_0(u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4304,c_9121])).

cnf(c_14184,plain,
    ( sK3(sK6,sK7,k1_xboole_0) = u1_struct_0(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13877,c_60,c_59,c_58,c_56,c_65,c_55,c_54,c_53,c_52,c_194,c_2856,c_3178,c_3180,c_3557,c_3772,c_3773,c_5500])).

cnf(c_42,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK3(X1,X2,X0))),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X2,sK3(X1,X2,X0))))
    | ~ v1_funct_1(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f141])).

cnf(c_2248,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v5_pre_topc(X0,X1,X2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK3(X1,X2,X0))),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X2,sK3(X1,X2,X0)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_14222,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
    | v5_pre_topc(k1_xboole_0,sK6,sK7) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) != iProver_top
    | r1_tarski(k2_pre_topc(sK6,k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),k1_xboole_0,u1_struct_0(sK7))),k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),k1_xboole_0,k2_pre_topc(sK7,u1_struct_0(sK7)))) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_14184,c_2248])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_2285,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_2267,plain,
    ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_6405,plain,
    ( k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,u1_struct_0(sK7)) = k1_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8) ),
    inference(superposition,[status(thm)],[c_2237,c_2267])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_2268,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4795,plain,
    ( k1_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8) = k1_relat_1(sK8) ),
    inference(superposition,[status(thm)],[c_2237,c_2268])).

cnf(c_6417,plain,
    ( k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,u1_struct_0(sK7)) = k1_relat_1(sK8) ),
    inference(light_normalisation,[status(thm)],[c_6405,c_4795])).

cnf(c_2269,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_6815,plain,
    ( m1_subset_1(k1_relat_1(sK8),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6417,c_2269])).

cnf(c_6823,plain,
    ( m1_subset_1(k1_relat_1(sK8),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6815,c_68])).

cnf(c_6828,plain,
    ( r1_tarski(k1_relat_1(sK8),u1_struct_0(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6823,c_2274])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_2281,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6945,plain,
    ( r2_hidden(X0,u1_struct_0(sK6)) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6828,c_2281])).

cnf(c_6962,plain,
    ( r2_hidden(sK0(k1_relat_1(sK8)),u1_struct_0(sK6)) = iProver_top
    | v1_xboole_0(k1_relat_1(sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2285,c_6945])).

cnf(c_8705,plain,
    ( r2_hidden(sK0(k1_relat_1(k1_xboole_0)),u1_struct_0(sK6)) = iProver_top
    | v1_xboole_0(k1_relat_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8411,c_6962])).

cnf(c_18,plain,
    ( v4_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_164,plain,
    ( v4_relat_1(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_166,plain,
    ( v4_relat_1(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_164])).

cnf(c_19,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f158])).

cnf(c_28,plain,
    ( v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_2262,plain,
    ( v1_partfun1(k6_partfun1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3192,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_19,c_2262])).

cnf(c_10,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f161])).

cnf(c_17,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_2272,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3320,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_2272])).

cnf(c_26,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f121])).

cnf(c_8987,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(k1_relat_1(X0)) ),
    inference(resolution,[status(thm)],[c_26,c_983])).

cnf(c_8992,plain,
    ( v1_partfun1(X0,X1) != iProver_top
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(k1_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8987])).

cnf(c_8994,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0) != iProver_top
    | v4_relat_1(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_relat_1(k1_xboole_0)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8992])).

cnf(c_11741,plain,
    ( v1_xboole_0(k1_relat_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8705,c_166,c_194,c_3192,c_3320,c_8994])).

cnf(c_11746,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11741,c_2279])).

cnf(c_8711,plain,
    ( k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),k1_xboole_0,u1_struct_0(sK7)) = k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_8411,c_6417])).

cnf(c_12698,plain,
    ( k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),k1_xboole_0,u1_struct_0(sK7)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11746,c_8711])).

cnf(c_8710,plain,
    ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8411,c_6823])).

cnf(c_33,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f129])).

cnf(c_2257,plain,
    ( k2_pre_topc(X0,X1) = X1
    | v4_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_10905,plain,
    ( k2_pre_topc(sK6,k1_relat_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0)
    | v4_pre_topc(k1_relat_1(k1_xboole_0),sK6) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_8710,c_2257])).

cnf(c_13880,plain,
    ( v4_pre_topc(k1_relat_1(k1_xboole_0),sK6) != iProver_top
    | k2_pre_topc(sK6,k1_relat_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10905,c_63])).

cnf(c_13881,plain,
    ( k2_pre_topc(sK6,k1_relat_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0)
    | v4_pre_topc(k1_relat_1(k1_xboole_0),sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_13880])).

cnf(c_13884,plain,
    ( k2_pre_topc(sK6,k1_xboole_0) = k1_xboole_0
    | v4_pre_topc(k1_xboole_0,sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13881,c_11746])).

cnf(c_51,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f146])).

cnf(c_2962,plain,
    ( v4_pre_topc(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v1_tdlat_3(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_51])).

cnf(c_2964,plain,
    ( v4_pre_topc(k1_xboole_0,sK6)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v1_tdlat_3(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_2962])).

cnf(c_13,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_3297,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_3721,plain,
    ( ~ v4_pre_topc(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ l1_pre_topc(sK6)
    | k2_pre_topc(sK6,X0) = X0 ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_3723,plain,
    ( ~ v4_pre_topc(k1_xboole_0,sK6)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ l1_pre_topc(sK6)
    | k2_pre_topc(sK6,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3721])).

cnf(c_13888,plain,
    ( k2_pre_topc(sK6,k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13884,c_60,c_59,c_58,c_2964,c_3297,c_3723])).

cnf(c_14224,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
    | v5_pre_topc(k1_xboole_0,sK6,sK7) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) != iProver_top
    | r1_tarski(k1_xboole_0,k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),k1_xboole_0,k2_pre_topc(sK7,u1_struct_0(sK7)))) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14222,c_12698,c_13888])).

cnf(c_3275,plain,
    ( ~ v1_xboole_0(sK8)
    | k1_xboole_0 = sK8 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3556,plain,
    ( v1_xboole_0(k2_struct_0(sK7))
    | ~ v1_xboole_0(k1_xboole_0)
    | k2_struct_0(sK7) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3554])).

cnf(c_981,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3945,plain,
    ( u1_struct_0(sK6) = u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_981])).

cnf(c_1002,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_3593,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k1_xboole_0)
    | ~ v1_xboole_0(X0) ),
    inference(resolution,[status(thm)],[c_6,c_1002])).

cnf(c_4199,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ v1_xboole_0(sK8) ),
    inference(resolution,[status(thm)],[c_3593,c_55])).

cnf(c_4200,plain,
    ( v1_funct_1(k1_xboole_0) = iProver_top
    | v1_xboole_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4199])).

cnf(c_4599,plain,
    ( u1_struct_0(sK7) = u1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_981])).

cnf(c_1001,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_3026,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))
    | X2 != u1_struct_0(sK7)
    | X1 != u1_struct_0(sK6)
    | X0 != sK8 ),
    inference(instantiation,[status(thm)],[c_1001])).

cnf(c_4598,plain,
    ( v1_funct_2(X0,X1,u1_struct_0(sK7))
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))
    | X1 != u1_struct_0(sK6)
    | X0 != sK8
    | u1_struct_0(sK7) != u1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_3026])).

cnf(c_5653,plain,
    ( v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))
    | X0 != sK8
    | u1_struct_0(sK7) != u1_struct_0(sK7)
    | u1_struct_0(sK6) != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_4598])).

cnf(c_5654,plain,
    ( X0 != sK8
    | u1_struct_0(sK7) != u1_struct_0(sK7)
    | u1_struct_0(sK6) != u1_struct_0(sK6)
    | v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(sK7)) = iProver_top
    | v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5653])).

cnf(c_5656,plain,
    ( u1_struct_0(sK7) != u1_struct_0(sK7)
    | u1_struct_0(sK6) != u1_struct_0(sK6)
    | k1_xboole_0 != sK8
    | v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
    | v1_funct_2(k1_xboole_0,u1_struct_0(sK6),u1_struct_0(sK7)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5654])).

cnf(c_2238,plain,
    ( v5_pre_topc(sK8,sK6,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_8722,plain,
    ( v5_pre_topc(k1_xboole_0,sK6,sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8411,c_2238])).

cnf(c_988,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_9199,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_988,c_981])).

cnf(c_12032,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k1_xboole_0,X1)
    | ~ v1_xboole_0(X0) ),
    inference(resolution,[status(thm)],[c_9199,c_6])).

cnf(c_12302,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | ~ v1_xboole_0(sK8) ),
    inference(resolution,[status(thm)],[c_12032,c_53])).

cnf(c_12303,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) = iProver_top
    | v1_xboole_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12302])).

cnf(c_15589,plain,
    ( r1_tarski(k1_xboole_0,k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),k1_xboole_0,k2_pre_topc(sK7,u1_struct_0(sK7)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14224,c_60,c_61,c_59,c_58,c_63,c_64,c_56,c_65,c_55,c_54,c_67,c_53,c_52,c_5,c_194,c_2855,c_2856,c_3177,c_3178,c_3176,c_3180,c_3275,c_3556,c_3557,c_3772,c_3773,c_3945,c_4200,c_4599,c_5312,c_5313,c_5500,c_5656,c_8722,c_12303])).

cnf(c_2276,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3876,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2276,c_2274])).

cnf(c_15594,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_15589,c_3876])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:20:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 4.16/1.06  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.16/1.06  
% 4.16/1.06  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.16/1.06  
% 4.16/1.06  ------  iProver source info
% 4.16/1.06  
% 4.16/1.06  git: date: 2020-06-30 10:37:57 +0100
% 4.16/1.06  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.16/1.06  git: non_committed_changes: false
% 4.16/1.06  git: last_make_outside_of_git: false
% 4.16/1.06  
% 4.16/1.06  ------ 
% 4.16/1.06  ------ Parsing...
% 4.16/1.06  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.16/1.06  
% 4.16/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 4.16/1.06  
% 4.16/1.06  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.16/1.06  
% 4.16/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.16/1.06  ------ Proving...
% 4.16/1.06  ------ Problem Properties 
% 4.16/1.06  
% 4.16/1.06  
% 4.16/1.06  clauses                                 60
% 4.16/1.06  conjectures                             9
% 4.16/1.06  EPR                                     16
% 4.16/1.06  Horn                                    48
% 4.16/1.06  unary                                   19
% 4.16/1.06  binary                                  12
% 4.16/1.06  lits                                    205
% 4.16/1.06  lits eq                                 22
% 4.16/1.06  fd_pure                                 0
% 4.16/1.06  fd_pseudo                               0
% 4.16/1.06  fd_cond                                 2
% 4.16/1.06  fd_pseudo_cond                          2
% 4.16/1.06  AC symbols                              0
% 4.16/1.06  
% 4.16/1.06  ------ Input Options Time Limit: Unbounded
% 4.16/1.06  
% 4.16/1.06  
% 4.16/1.06  ------ 
% 4.16/1.06  Current options:
% 4.16/1.06  ------ 
% 4.16/1.06  
% 4.16/1.06  
% 4.16/1.06  
% 4.16/1.06  
% 4.16/1.06  ------ Proving...
% 4.16/1.06  
% 4.16/1.06  
% 4.16/1.06  % SZS status Theorem for theBenchmark.p
% 4.16/1.06  
% 4.16/1.06   Resolution empty clause
% 4.16/1.06  
% 4.16/1.06  % SZS output start CNFRefutation for theBenchmark.p
% 4.16/1.06  
% 4.16/1.06  fof(f2,axiom,(
% 4.16/1.06    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 4.16/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.16/1.06  
% 4.16/1.06  fof(f32,plain,(
% 4.16/1.06    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 4.16/1.06    inference(ennf_transformation,[],[f2])).
% 4.16/1.06  
% 4.16/1.06  fof(f65,plain,(
% 4.16/1.06    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 4.16/1.06    inference(nnf_transformation,[],[f32])).
% 4.16/1.06  
% 4.16/1.06  fof(f66,plain,(
% 4.16/1.06    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 4.16/1.06    inference(rectify,[],[f65])).
% 4.16/1.06  
% 4.16/1.06  fof(f67,plain,(
% 4.16/1.06    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 4.16/1.06    introduced(choice_axiom,[])).
% 4.16/1.06  
% 4.16/1.06  fof(f68,plain,(
% 4.16/1.06    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 4.16/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f66,f67])).
% 4.16/1.06  
% 4.16/1.06  fof(f99,plain,(
% 4.16/1.06    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 4.16/1.06    inference(cnf_transformation,[],[f68])).
% 4.16/1.06  
% 4.16/1.06  fof(f1,axiom,(
% 4.16/1.06    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 4.16/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.16/1.06  
% 4.16/1.06  fof(f61,plain,(
% 4.16/1.06    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 4.16/1.06    inference(nnf_transformation,[],[f1])).
% 4.16/1.06  
% 4.16/1.06  fof(f62,plain,(
% 4.16/1.06    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 4.16/1.06    inference(rectify,[],[f61])).
% 4.16/1.06  
% 4.16/1.06  fof(f63,plain,(
% 4.16/1.06    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 4.16/1.06    introduced(choice_axiom,[])).
% 4.16/1.06  
% 4.16/1.06  fof(f64,plain,(
% 4.16/1.06    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 4.16/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f62,f63])).
% 4.16/1.06  
% 4.16/1.06  fof(f96,plain,(
% 4.16/1.06    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 4.16/1.06    inference(cnf_transformation,[],[f64])).
% 4.16/1.06  
% 4.16/1.06  fof(f29,conjecture,(
% 4.16/1.06    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => v5_pre_topc(X2,X0,X1))))),
% 4.16/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.16/1.06  
% 4.16/1.06  fof(f30,negated_conjecture,(
% 4.16/1.06    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => v5_pre_topc(X2,X0,X1))))),
% 4.16/1.06    inference(negated_conjecture,[],[f29])).
% 4.16/1.06  
% 4.16/1.06  fof(f59,plain,(
% 4.16/1.06    ? [X0] : (? [X1] : (? [X2] : (~v5_pre_topc(X2,X0,X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0)))),
% 4.16/1.06    inference(ennf_transformation,[],[f30])).
% 4.16/1.06  
% 4.16/1.06  fof(f60,plain,(
% 4.16/1.06    ? [X0] : (? [X1] : (? [X2] : (~v5_pre_topc(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0))),
% 4.16/1.06    inference(flattening,[],[f59])).
% 4.16/1.06  
% 4.16/1.06  fof(f94,plain,(
% 4.16/1.06    ( ! [X0,X1] : (? [X2] : (~v5_pre_topc(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~v5_pre_topc(sK8,X0,X1) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK8,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK8))) )),
% 4.16/1.06    introduced(choice_axiom,[])).
% 4.16/1.06  
% 4.16/1.06  fof(f93,plain,(
% 4.16/1.06    ( ! [X0] : (? [X1] : (? [X2] : (~v5_pre_topc(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (~v5_pre_topc(X2,X0,sK7) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK7)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK7)) & v1_funct_1(X2)) & l1_pre_topc(sK7) & v2_pre_topc(sK7))) )),
% 4.16/1.06    introduced(choice_axiom,[])).
% 4.16/1.06  
% 4.16/1.06  fof(f92,plain,(
% 4.16/1.06    ? [X0] : (? [X1] : (? [X2] : (~v5_pre_topc(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v5_pre_topc(X2,sK6,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK6),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK6) & v1_tdlat_3(sK6) & v2_pre_topc(sK6))),
% 4.16/1.06    introduced(choice_axiom,[])).
% 4.16/1.06  
% 4.16/1.06  fof(f95,plain,(
% 4.16/1.06    ((~v5_pre_topc(sK8,sK6,sK7) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) & v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) & v1_funct_1(sK8)) & l1_pre_topc(sK7) & v2_pre_topc(sK7)) & l1_pre_topc(sK6) & v1_tdlat_3(sK6) & v2_pre_topc(sK6)),
% 4.16/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f60,f94,f93,f92])).
% 4.16/1.06  
% 4.16/1.06  fof(f156,plain,(
% 4.16/1.06    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))),
% 4.16/1.06    inference(cnf_transformation,[],[f95])).
% 4.16/1.06  
% 4.16/1.06  fof(f25,axiom,(
% 4.16/1.06    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))))))))),
% 4.16/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.16/1.06  
% 4.16/1.06  fof(f51,plain,(
% 4.16/1.06    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 4.16/1.06    inference(ennf_transformation,[],[f25])).
% 4.16/1.06  
% 4.16/1.06  fof(f52,plain,(
% 4.16/1.06    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.16/1.06    inference(flattening,[],[f51])).
% 4.16/1.06  
% 4.16/1.06  fof(f80,plain,(
% 4.16/1.06    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.16/1.06    inference(nnf_transformation,[],[f52])).
% 4.16/1.06  
% 4.16/1.06  fof(f81,plain,(
% 4.16/1.06    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.16/1.06    inference(rectify,[],[f80])).
% 4.16/1.06  
% 4.16/1.06  fof(f82,plain,(
% 4.16/1.06    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK3(X0,X1,X2)))) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 4.16/1.06    introduced(choice_axiom,[])).
% 4.16/1.06  
% 4.16/1.06  fof(f83,plain,(
% 4.16/1.06    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK3(X0,X1,X2)))) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.16/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f81,f82])).
% 4.16/1.06  
% 4.16/1.06  fof(f140,plain,(
% 4.16/1.06    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.16/1.06    inference(cnf_transformation,[],[f83])).
% 4.16/1.06  
% 4.16/1.06  fof(f149,plain,(
% 4.16/1.06    v2_pre_topc(sK6)),
% 4.16/1.06    inference(cnf_transformation,[],[f95])).
% 4.16/1.06  
% 4.16/1.06  fof(f151,plain,(
% 4.16/1.06    l1_pre_topc(sK6)),
% 4.16/1.06    inference(cnf_transformation,[],[f95])).
% 4.16/1.06  
% 4.16/1.06  fof(f152,plain,(
% 4.16/1.06    v2_pre_topc(sK7)),
% 4.16/1.06    inference(cnf_transformation,[],[f95])).
% 4.16/1.06  
% 4.16/1.06  fof(f153,plain,(
% 4.16/1.06    l1_pre_topc(sK7)),
% 4.16/1.06    inference(cnf_transformation,[],[f95])).
% 4.16/1.06  
% 4.16/1.06  fof(f154,plain,(
% 4.16/1.06    v1_funct_1(sK8)),
% 4.16/1.06    inference(cnf_transformation,[],[f95])).
% 4.16/1.06  
% 4.16/1.06  fof(f155,plain,(
% 4.16/1.06    v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))),
% 4.16/1.06    inference(cnf_transformation,[],[f95])).
% 4.16/1.06  
% 4.16/1.06  fof(f157,plain,(
% 4.16/1.06    ~v5_pre_topc(sK8,sK6,sK7)),
% 4.16/1.06    inference(cnf_transformation,[],[f95])).
% 4.16/1.06  
% 4.16/1.06  fof(f8,axiom,(
% 4.16/1.06    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 4.16/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.16/1.06  
% 4.16/1.06  fof(f73,plain,(
% 4.16/1.06    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 4.16/1.06    inference(nnf_transformation,[],[f8])).
% 4.16/1.06  
% 4.16/1.06  fof(f110,plain,(
% 4.16/1.06    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 4.16/1.06    inference(cnf_transformation,[],[f73])).
% 4.16/1.06  
% 4.16/1.06  fof(f13,axiom,(
% 4.16/1.06    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 4.16/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.16/1.06  
% 4.16/1.06  fof(f36,plain,(
% 4.16/1.06    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 4.16/1.06    inference(ennf_transformation,[],[f13])).
% 4.16/1.06  
% 4.16/1.06  fof(f116,plain,(
% 4.16/1.06    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 4.16/1.06    inference(cnf_transformation,[],[f36])).
% 4.16/1.06  
% 4.16/1.06  fof(f150,plain,(
% 4.16/1.06    v1_tdlat_3(sK6)),
% 4.16/1.06    inference(cnf_transformation,[],[f95])).
% 4.16/1.06  
% 4.16/1.06  fof(f3,axiom,(
% 4.16/1.06    v1_xboole_0(k1_xboole_0)),
% 4.16/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.16/1.06  
% 4.16/1.06  fof(f101,plain,(
% 4.16/1.06    v1_xboole_0(k1_xboole_0)),
% 4.16/1.06    inference(cnf_transformation,[],[f3])).
% 4.16/1.06  
% 4.16/1.06  fof(f20,axiom,(
% 4.16/1.06    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 4.16/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.16/1.06  
% 4.16/1.06  fof(f42,plain,(
% 4.16/1.06    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 4.16/1.06    inference(ennf_transformation,[],[f20])).
% 4.16/1.06  
% 4.16/1.06  fof(f126,plain,(
% 4.16/1.06    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 4.16/1.06    inference(cnf_transformation,[],[f42])).
% 4.16/1.06  
% 4.16/1.06  fof(f21,axiom,(
% 4.16/1.06    ! [X0] : ((l1_struct_0(X0) & v2_struct_0(X0)) => v1_xboole_0(u1_struct_0(X0)))),
% 4.16/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.16/1.06  
% 4.16/1.06  fof(f43,plain,(
% 4.16/1.06    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v2_struct_0(X0)))),
% 4.16/1.06    inference(ennf_transformation,[],[f21])).
% 4.16/1.06  
% 4.16/1.06  fof(f44,plain,(
% 4.16/1.06    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0))),
% 4.16/1.06    inference(flattening,[],[f43])).
% 4.16/1.06  
% 4.16/1.06  fof(f127,plain,(
% 4.16/1.06    ( ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0)) )),
% 4.16/1.06    inference(cnf_transformation,[],[f44])).
% 4.16/1.06  
% 4.16/1.06  fof(f22,axiom,(
% 4.16/1.06    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 4.16/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.16/1.06  
% 4.16/1.06  fof(f45,plain,(
% 4.16/1.06    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 4.16/1.06    inference(ennf_transformation,[],[f22])).
% 4.16/1.06  
% 4.16/1.06  fof(f46,plain,(
% 4.16/1.06    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 4.16/1.06    inference(flattening,[],[f45])).
% 4.16/1.06  
% 4.16/1.06  fof(f128,plain,(
% 4.16/1.06    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 4.16/1.06    inference(cnf_transformation,[],[f46])).
% 4.16/1.06  
% 4.16/1.06  fof(f27,axiom,(
% 4.16/1.06    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v3_pre_topc(X1,X0))))),
% 4.16/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.16/1.06  
% 4.16/1.06  fof(f55,plain,(
% 4.16/1.06    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 4.16/1.06    inference(ennf_transformation,[],[f27])).
% 4.16/1.06  
% 4.16/1.06  fof(f56,plain,(
% 4.16/1.06    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.16/1.06    inference(flattening,[],[f55])).
% 4.16/1.06  
% 4.16/1.06  fof(f84,plain,(
% 4.16/1.06    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.16/1.06    inference(nnf_transformation,[],[f56])).
% 4.16/1.06  
% 4.16/1.06  fof(f85,plain,(
% 4.16/1.06    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.16/1.06    inference(rectify,[],[f84])).
% 4.16/1.06  
% 4.16/1.06  fof(f86,plain,(
% 4.16/1.06    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK4(X0),X0) & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 4.16/1.06    introduced(choice_axiom,[])).
% 4.16/1.06  
% 4.16/1.06  fof(f87,plain,(
% 4.16/1.06    ! [X0] : (((v1_tdlat_3(X0) | (~v3_pre_topc(sK4(X0),X0) & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.16/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f85,f86])).
% 4.16/1.06  
% 4.16/1.06  fof(f143,plain,(
% 4.16/1.06    ( ! [X2,X0] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.16/1.06    inference(cnf_transformation,[],[f87])).
% 4.16/1.06  
% 4.16/1.06  fof(f24,axiom,(
% 4.16/1.06    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v3_pre_topc(X3,X1) => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0))))))))),
% 4.16/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.16/1.06  
% 4.16/1.06  fof(f49,plain,(
% 4.16/1.06    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 4.16/1.06    inference(ennf_transformation,[],[f24])).
% 4.16/1.06  
% 4.16/1.06  fof(f50,plain,(
% 4.16/1.06    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 4.16/1.06    inference(flattening,[],[f49])).
% 4.16/1.06  
% 4.16/1.06  fof(f76,plain,(
% 4.16/1.06    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 4.16/1.06    inference(nnf_transformation,[],[f50])).
% 4.16/1.06  
% 4.16/1.06  fof(f77,plain,(
% 4.16/1.06    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 4.16/1.06    inference(rectify,[],[f76])).
% 4.16/1.06  
% 4.16/1.06  fof(f78,plain,(
% 4.16/1.06    ! [X2,X1,X0] : (? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0) & v3_pre_topc(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 4.16/1.06    introduced(choice_axiom,[])).
% 4.16/1.06  
% 4.16/1.06  fof(f79,plain,(
% 4.16/1.06    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0) & v3_pre_topc(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 4.16/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f77,f78])).
% 4.16/1.06  
% 4.16/1.06  fof(f137,plain,(
% 4.16/1.06    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | ~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0) | k1_xboole_0 = k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 4.16/1.06    inference(cnf_transformation,[],[f79])).
% 4.16/1.06  
% 4.16/1.06  fof(f14,axiom,(
% 4.16/1.06    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)))),
% 4.16/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.16/1.06  
% 4.16/1.06  fof(f37,plain,(
% 4.16/1.06    ! [X0,X1,X2,X3] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.16/1.06    inference(ennf_transformation,[],[f14])).
% 4.16/1.06  
% 4.16/1.06  fof(f117,plain,(
% 4.16/1.06    ( ! [X2,X0,X3,X1] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.16/1.06    inference(cnf_transformation,[],[f37])).
% 4.16/1.06  
% 4.16/1.06  fof(f4,axiom,(
% 4.16/1.06    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 4.16/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.16/1.06  
% 4.16/1.06  fof(f33,plain,(
% 4.16/1.06    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 4.16/1.06    inference(ennf_transformation,[],[f4])).
% 4.16/1.06  
% 4.16/1.06  fof(f102,plain,(
% 4.16/1.06    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 4.16/1.06    inference(cnf_transformation,[],[f33])).
% 4.16/1.06  
% 4.16/1.06  fof(f5,axiom,(
% 4.16/1.06    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.16/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.16/1.06  
% 4.16/1.06  fof(f69,plain,(
% 4.16/1.06    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.16/1.06    inference(nnf_transformation,[],[f5])).
% 4.16/1.06  
% 4.16/1.06  fof(f70,plain,(
% 4.16/1.06    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.16/1.06    inference(flattening,[],[f69])).
% 4.16/1.06  
% 4.16/1.06  fof(f105,plain,(
% 4.16/1.06    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 4.16/1.06    inference(cnf_transformation,[],[f70])).
% 4.16/1.06  
% 4.16/1.06  fof(f141,plain,(
% 4.16/1.06    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | ~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK3(X0,X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.16/1.06    inference(cnf_transformation,[],[f83])).
% 4.16/1.06  
% 4.16/1.06  fof(f97,plain,(
% 4.16/1.06    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 4.16/1.06    inference(cnf_transformation,[],[f64])).
% 4.16/1.06  
% 4.16/1.06  fof(f16,axiom,(
% 4.16/1.06    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 4.16/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.16/1.06  
% 4.16/1.06  fof(f39,plain,(
% 4.16/1.06    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.16/1.06    inference(ennf_transformation,[],[f16])).
% 4.16/1.06  
% 4.16/1.06  fof(f120,plain,(
% 4.16/1.06    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.16/1.06    inference(cnf_transformation,[],[f39])).
% 4.16/1.06  
% 4.16/1.06  fof(f15,axiom,(
% 4.16/1.06    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 4.16/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.16/1.06  
% 4.16/1.06  fof(f38,plain,(
% 4.16/1.06    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.16/1.06    inference(ennf_transformation,[],[f15])).
% 4.16/1.06  
% 4.16/1.06  fof(f118,plain,(
% 4.16/1.06    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.16/1.06    inference(cnf_transformation,[],[f38])).
% 4.16/1.06  
% 4.16/1.06  fof(f98,plain,(
% 4.16/1.06    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 4.16/1.06    inference(cnf_transformation,[],[f68])).
% 4.16/1.06  
% 4.16/1.06  fof(f11,axiom,(
% 4.16/1.06    ! [X0,X1] : (v5_relat_1(k1_xboole_0,X1) & v4_relat_1(k1_xboole_0,X0))),
% 4.16/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.16/1.06  
% 4.16/1.06  fof(f31,plain,(
% 4.16/1.06    ! [X0,X1] : v4_relat_1(k1_xboole_0,X0)),
% 4.16/1.06    inference(pure_predicate_removal,[],[f11])).
% 4.16/1.06  
% 4.16/1.06  fof(f74,plain,(
% 4.16/1.06    ! [X0] : v4_relat_1(k1_xboole_0,X0)),
% 4.16/1.06    inference(rectify,[],[f31])).
% 4.16/1.06  
% 4.16/1.06  fof(f114,plain,(
% 4.16/1.06    ( ! [X0] : (v4_relat_1(k1_xboole_0,X0)) )),
% 4.16/1.06    inference(cnf_transformation,[],[f74])).
% 4.16/1.06  
% 4.16/1.06  fof(f12,axiom,(
% 4.16/1.06    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 4.16/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.16/1.06  
% 4.16/1.06  fof(f115,plain,(
% 4.16/1.06    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 4.16/1.06    inference(cnf_transformation,[],[f12])).
% 4.16/1.06  
% 4.16/1.06  fof(f19,axiom,(
% 4.16/1.06    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 4.16/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.16/1.06  
% 4.16/1.06  fof(f125,plain,(
% 4.16/1.06    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 4.16/1.06    inference(cnf_transformation,[],[f19])).
% 4.16/1.06  
% 4.16/1.06  fof(f158,plain,(
% 4.16/1.06    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 4.16/1.06    inference(definition_unfolding,[],[f115,f125])).
% 4.16/1.06  
% 4.16/1.06  fof(f18,axiom,(
% 4.16/1.06    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 4.16/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.16/1.06  
% 4.16/1.06  fof(f123,plain,(
% 4.16/1.06    ( ! [X0] : (v1_partfun1(k6_partfun1(X0),X0)) )),
% 4.16/1.06    inference(cnf_transformation,[],[f18])).
% 4.16/1.06  
% 4.16/1.06  fof(f6,axiom,(
% 4.16/1.06    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 4.16/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.16/1.06  
% 4.16/1.06  fof(f71,plain,(
% 4.16/1.06    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 4.16/1.06    inference(nnf_transformation,[],[f6])).
% 4.16/1.06  
% 4.16/1.06  fof(f72,plain,(
% 4.16/1.06    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 4.16/1.06    inference(flattening,[],[f71])).
% 4.16/1.06  
% 4.16/1.06  fof(f108,plain,(
% 4.16/1.06    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 4.16/1.06    inference(cnf_transformation,[],[f72])).
% 4.16/1.06  
% 4.16/1.06  fof(f161,plain,(
% 4.16/1.06    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 4.16/1.06    inference(equality_resolution,[],[f108])).
% 4.16/1.06  
% 4.16/1.06  fof(f10,axiom,(
% 4.16/1.06    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 4.16/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.16/1.06  
% 4.16/1.06  fof(f113,plain,(
% 4.16/1.06    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 4.16/1.06    inference(cnf_transformation,[],[f10])).
% 4.16/1.06  
% 4.16/1.06  fof(f17,axiom,(
% 4.16/1.06    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 4.16/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.16/1.06  
% 4.16/1.06  fof(f40,plain,(
% 4.16/1.06    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 4.16/1.06    inference(ennf_transformation,[],[f17])).
% 4.16/1.06  
% 4.16/1.06  fof(f41,plain,(
% 4.16/1.06    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 4.16/1.06    inference(flattening,[],[f40])).
% 4.16/1.06  
% 4.16/1.06  fof(f75,plain,(
% 4.16/1.06    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 4.16/1.06    inference(nnf_transformation,[],[f41])).
% 4.16/1.06  
% 4.16/1.06  fof(f121,plain,(
% 4.16/1.06    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 4.16/1.06    inference(cnf_transformation,[],[f75])).
% 4.16/1.06  
% 4.16/1.06  fof(f23,axiom,(
% 4.16/1.06    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 4.16/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.16/1.06  
% 4.16/1.06  fof(f47,plain,(
% 4.16/1.06    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.16/1.06    inference(ennf_transformation,[],[f23])).
% 4.16/1.06  
% 4.16/1.06  fof(f48,plain,(
% 4.16/1.06    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.16/1.06    inference(flattening,[],[f47])).
% 4.16/1.06  
% 4.16/1.06  fof(f129,plain,(
% 4.16/1.06    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.16/1.06    inference(cnf_transformation,[],[f48])).
% 4.16/1.06  
% 4.16/1.06  fof(f28,axiom,(
% 4.16/1.06    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v4_pre_topc(X1,X0))))),
% 4.16/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.16/1.06  
% 4.16/1.06  fof(f57,plain,(
% 4.16/1.06    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 4.16/1.06    inference(ennf_transformation,[],[f28])).
% 4.16/1.06  
% 4.16/1.06  fof(f58,plain,(
% 4.16/1.06    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.16/1.06    inference(flattening,[],[f57])).
% 4.16/1.06  
% 4.16/1.06  fof(f88,plain,(
% 4.16/1.06    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.16/1.06    inference(nnf_transformation,[],[f58])).
% 4.16/1.06  
% 4.16/1.06  fof(f89,plain,(
% 4.16/1.06    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.16/1.06    inference(rectify,[],[f88])).
% 4.16/1.06  
% 4.16/1.06  fof(f90,plain,(
% 4.16/1.06    ! [X0] : (? [X1] : (~v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v4_pre_topc(sK5(X0),X0) & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 4.16/1.06    introduced(choice_axiom,[])).
% 4.16/1.06  
% 4.16/1.06  fof(f91,plain,(
% 4.16/1.06    ! [X0] : (((v1_tdlat_3(X0) | (~v4_pre_topc(sK5(X0),X0) & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.16/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f89,f90])).
% 4.16/1.06  
% 4.16/1.06  fof(f146,plain,(
% 4.16/1.06    ( ! [X2,X0] : (v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.16/1.06    inference(cnf_transformation,[],[f91])).
% 4.16/1.06  
% 4.16/1.06  fof(f7,axiom,(
% 4.16/1.06    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 4.16/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.16/1.06  
% 4.16/1.06  fof(f109,plain,(
% 4.16/1.06    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 4.16/1.06    inference(cnf_transformation,[],[f7])).
% 4.16/1.06  
% 4.16/1.06  cnf(c_3,plain,
% 4.16/1.06      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 4.16/1.06      inference(cnf_transformation,[],[f99]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_2282,plain,
% 4.16/1.06      ( r1_tarski(X0,X1) = iProver_top
% 4.16/1.06      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 4.16/1.06      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_1,plain,
% 4.16/1.06      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 4.16/1.06      inference(cnf_transformation,[],[f96]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_2284,plain,
% 4.16/1.06      ( r2_hidden(X0,X1) != iProver_top | v1_xboole_0(X1) != iProver_top ),
% 4.16/1.06      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_4304,plain,
% 4.16/1.06      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 4.16/1.06      inference(superposition,[status(thm)],[c_2282,c_2284]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_53,negated_conjecture,
% 4.16/1.06      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) ),
% 4.16/1.06      inference(cnf_transformation,[],[f156]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_2237,plain,
% 4.16/1.06      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) = iProver_top ),
% 4.16/1.06      inference(predicate_to_equality,[status(thm)],[c_53]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_43,plain,
% 4.16/1.06      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 4.16/1.06      | v5_pre_topc(X0,X1,X2)
% 4.16/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 4.16/1.06      | m1_subset_1(sK3(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
% 4.16/1.06      | ~ v1_funct_1(X0)
% 4.16/1.06      | ~ v2_pre_topc(X1)
% 4.16/1.06      | ~ v2_pre_topc(X2)
% 4.16/1.06      | ~ l1_pre_topc(X1)
% 4.16/1.06      | ~ l1_pre_topc(X2) ),
% 4.16/1.06      inference(cnf_transformation,[],[f140]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_2247,plain,
% 4.16/1.06      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 4.16/1.06      | v5_pre_topc(X0,X1,X2) = iProver_top
% 4.16/1.06      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 4.16/1.06      | m1_subset_1(sK3(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2))) = iProver_top
% 4.16/1.06      | v1_funct_1(X0) != iProver_top
% 4.16/1.06      | v2_pre_topc(X1) != iProver_top
% 4.16/1.06      | v2_pre_topc(X2) != iProver_top
% 4.16/1.06      | l1_pre_topc(X1) != iProver_top
% 4.16/1.06      | l1_pre_topc(X2) != iProver_top ),
% 4.16/1.06      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_7909,plain,
% 4.16/1.06      ( v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
% 4.16/1.06      | v5_pre_topc(sK8,sK6,sK7) = iProver_top
% 4.16/1.06      | m1_subset_1(sK3(sK6,sK7,sK8),k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top
% 4.16/1.06      | v1_funct_1(sK8) != iProver_top
% 4.16/1.06      | v2_pre_topc(sK7) != iProver_top
% 4.16/1.06      | v2_pre_topc(sK6) != iProver_top
% 4.16/1.06      | l1_pre_topc(sK7) != iProver_top
% 4.16/1.06      | l1_pre_topc(sK6) != iProver_top ),
% 4.16/1.06      inference(superposition,[status(thm)],[c_2237,c_2247]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_60,negated_conjecture,
% 4.16/1.06      ( v2_pre_topc(sK6) ),
% 4.16/1.06      inference(cnf_transformation,[],[f149]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_61,plain,
% 4.16/1.06      ( v2_pre_topc(sK6) = iProver_top ),
% 4.16/1.06      inference(predicate_to_equality,[status(thm)],[c_60]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_58,negated_conjecture,
% 4.16/1.06      ( l1_pre_topc(sK6) ),
% 4.16/1.06      inference(cnf_transformation,[],[f151]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_63,plain,
% 4.16/1.06      ( l1_pre_topc(sK6) = iProver_top ),
% 4.16/1.06      inference(predicate_to_equality,[status(thm)],[c_58]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_57,negated_conjecture,
% 4.16/1.06      ( v2_pre_topc(sK7) ),
% 4.16/1.06      inference(cnf_transformation,[],[f152]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_64,plain,
% 4.16/1.06      ( v2_pre_topc(sK7) = iProver_top ),
% 4.16/1.06      inference(predicate_to_equality,[status(thm)],[c_57]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_56,negated_conjecture,
% 4.16/1.06      ( l1_pre_topc(sK7) ),
% 4.16/1.06      inference(cnf_transformation,[],[f153]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_65,plain,
% 4.16/1.06      ( l1_pre_topc(sK7) = iProver_top ),
% 4.16/1.06      inference(predicate_to_equality,[status(thm)],[c_56]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_55,negated_conjecture,
% 4.16/1.06      ( v1_funct_1(sK8) ),
% 4.16/1.06      inference(cnf_transformation,[],[f154]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_66,plain,
% 4.16/1.06      ( v1_funct_1(sK8) = iProver_top ),
% 4.16/1.06      inference(predicate_to_equality,[status(thm)],[c_55]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_54,negated_conjecture,
% 4.16/1.06      ( v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) ),
% 4.16/1.06      inference(cnf_transformation,[],[f155]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_67,plain,
% 4.16/1.06      ( v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) = iProver_top ),
% 4.16/1.06      inference(predicate_to_equality,[status(thm)],[c_54]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_68,plain,
% 4.16/1.06      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) = iProver_top ),
% 4.16/1.06      inference(predicate_to_equality,[status(thm)],[c_53]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_52,negated_conjecture,
% 4.16/1.06      ( ~ v5_pre_topc(sK8,sK6,sK7) ),
% 4.16/1.06      inference(cnf_transformation,[],[f157]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_69,plain,
% 4.16/1.06      ( v5_pre_topc(sK8,sK6,sK7) != iProver_top ),
% 4.16/1.06      inference(predicate_to_equality,[status(thm)],[c_52]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_3055,plain,
% 4.16/1.06      ( ~ v1_funct_2(sK8,u1_struct_0(X0),u1_struct_0(X1))
% 4.16/1.06      | v5_pre_topc(sK8,X0,X1)
% 4.16/1.06      | m1_subset_1(sK3(X0,X1,sK8),k1_zfmisc_1(u1_struct_0(X1)))
% 4.16/1.06      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 4.16/1.06      | ~ v1_funct_1(sK8)
% 4.16/1.06      | ~ v2_pre_topc(X0)
% 4.16/1.06      | ~ v2_pre_topc(X1)
% 4.16/1.06      | ~ l1_pre_topc(X0)
% 4.16/1.06      | ~ l1_pre_topc(X1) ),
% 4.16/1.06      inference(instantiation,[status(thm)],[c_43]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_3386,plain,
% 4.16/1.06      ( ~ v1_funct_2(sK8,u1_struct_0(X0),u1_struct_0(sK7))
% 4.16/1.06      | v5_pre_topc(sK8,X0,sK7)
% 4.16/1.06      | m1_subset_1(sK3(X0,sK7,sK8),k1_zfmisc_1(u1_struct_0(sK7)))
% 4.16/1.06      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK7))))
% 4.16/1.06      | ~ v1_funct_1(sK8)
% 4.16/1.06      | ~ v2_pre_topc(X0)
% 4.16/1.06      | ~ v2_pre_topc(sK7)
% 4.16/1.06      | ~ l1_pre_topc(X0)
% 4.16/1.06      | ~ l1_pre_topc(sK7) ),
% 4.16/1.06      inference(instantiation,[status(thm)],[c_3055]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_3537,plain,
% 4.16/1.06      ( ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))
% 4.16/1.06      | v5_pre_topc(sK8,sK6,sK7)
% 4.16/1.06      | m1_subset_1(sK3(sK6,sK7,sK8),k1_zfmisc_1(u1_struct_0(sK7)))
% 4.16/1.06      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
% 4.16/1.06      | ~ v1_funct_1(sK8)
% 4.16/1.06      | ~ v2_pre_topc(sK7)
% 4.16/1.06      | ~ v2_pre_topc(sK6)
% 4.16/1.06      | ~ l1_pre_topc(sK7)
% 4.16/1.06      | ~ l1_pre_topc(sK6) ),
% 4.16/1.06      inference(instantiation,[status(thm)],[c_3386]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_3538,plain,
% 4.16/1.06      ( v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
% 4.16/1.06      | v5_pre_topc(sK8,sK6,sK7) = iProver_top
% 4.16/1.06      | m1_subset_1(sK3(sK6,sK7,sK8),k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top
% 4.16/1.06      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) != iProver_top
% 4.16/1.06      | v1_funct_1(sK8) != iProver_top
% 4.16/1.06      | v2_pre_topc(sK7) != iProver_top
% 4.16/1.06      | v2_pre_topc(sK6) != iProver_top
% 4.16/1.06      | l1_pre_topc(sK7) != iProver_top
% 4.16/1.06      | l1_pre_topc(sK6) != iProver_top ),
% 4.16/1.06      inference(predicate_to_equality,[status(thm)],[c_3537]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_8535,plain,
% 4.16/1.06      ( m1_subset_1(sK3(sK6,sK7,sK8),k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
% 4.16/1.06      inference(global_propositional_subsumption,
% 4.16/1.06                [status(thm)],
% 4.16/1.06                [c_7909,c_61,c_63,c_64,c_65,c_66,c_67,c_68,c_69,c_3538]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_15,plain,
% 4.16/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 4.16/1.06      inference(cnf_transformation,[],[f110]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_2274,plain,
% 4.16/1.06      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 4.16/1.06      | r1_tarski(X0,X1) = iProver_top ),
% 4.16/1.06      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_8540,plain,
% 4.16/1.06      ( r1_tarski(sK3(sK6,sK7,sK8),u1_struct_0(sK7)) = iProver_top ),
% 4.16/1.06      inference(superposition,[status(thm)],[c_8535,c_2274]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_20,plain,
% 4.16/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.16/1.06      | ~ v1_xboole_0(X2)
% 4.16/1.06      | v1_xboole_0(X0) ),
% 4.16/1.06      inference(cnf_transformation,[],[f116]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_2270,plain,
% 4.16/1.06      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 4.16/1.06      | v1_xboole_0(X2) != iProver_top
% 4.16/1.06      | v1_xboole_0(X0) = iProver_top ),
% 4.16/1.06      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_8009,plain,
% 4.16/1.06      ( v1_xboole_0(u1_struct_0(sK7)) != iProver_top
% 4.16/1.06      | v1_xboole_0(sK8) = iProver_top ),
% 4.16/1.06      inference(superposition,[status(thm)],[c_2237,c_2270]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_59,negated_conjecture,
% 4.16/1.06      ( v1_tdlat_3(sK6) ),
% 4.16/1.06      inference(cnf_transformation,[],[f150]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_5,plain,
% 4.16/1.06      ( v1_xboole_0(k1_xboole_0) ),
% 4.16/1.06      inference(cnf_transformation,[],[f101]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_194,plain,
% 4.16/1.06      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 4.16/1.06      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_29,plain,
% 4.16/1.06      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 4.16/1.06      inference(cnf_transformation,[],[f126]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_2855,plain,
% 4.16/1.06      ( ~ l1_pre_topc(sK7) | l1_struct_0(sK7) ),
% 4.16/1.06      inference(instantiation,[status(thm)],[c_29]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_2856,plain,
% 4.16/1.06      ( l1_pre_topc(sK7) != iProver_top | l1_struct_0(sK7) = iProver_top ),
% 4.16/1.06      inference(predicate_to_equality,[status(thm)],[c_2855]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_30,plain,
% 4.16/1.06      ( ~ v2_struct_0(X0) | ~ l1_struct_0(X0) | v1_xboole_0(u1_struct_0(X0)) ),
% 4.16/1.06      inference(cnf_transformation,[],[f127]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_3177,plain,
% 4.16/1.06      ( ~ v2_struct_0(sK7)
% 4.16/1.06      | ~ l1_struct_0(sK7)
% 4.16/1.06      | v1_xboole_0(u1_struct_0(sK7)) ),
% 4.16/1.06      inference(instantiation,[status(thm)],[c_30]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_3178,plain,
% 4.16/1.06      ( v2_struct_0(sK7) != iProver_top
% 4.16/1.06      | l1_struct_0(sK7) != iProver_top
% 4.16/1.06      | v1_xboole_0(u1_struct_0(sK7)) = iProver_top ),
% 4.16/1.06      inference(predicate_to_equality,[status(thm)],[c_3177]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_31,plain,
% 4.16/1.06      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(k2_struct_0(X0)) ),
% 4.16/1.06      inference(cnf_transformation,[],[f128]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_3176,plain,
% 4.16/1.06      ( v2_struct_0(sK7)
% 4.16/1.06      | ~ l1_struct_0(sK7)
% 4.16/1.06      | ~ v1_xboole_0(k2_struct_0(sK7)) ),
% 4.16/1.06      inference(instantiation,[status(thm)],[c_31]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_3180,plain,
% 4.16/1.06      ( v2_struct_0(sK7) = iProver_top
% 4.16/1.06      | l1_struct_0(sK7) != iProver_top
% 4.16/1.06      | v1_xboole_0(k2_struct_0(sK7)) != iProver_top ),
% 4.16/1.06      inference(predicate_to_equality,[status(thm)],[c_3176]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_983,plain,
% 4.16/1.06      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 4.16/1.06      theory(equality) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_3554,plain,
% 4.16/1.06      ( ~ v1_xboole_0(X0)
% 4.16/1.06      | v1_xboole_0(k2_struct_0(sK7))
% 4.16/1.06      | k2_struct_0(sK7) != X0 ),
% 4.16/1.06      inference(instantiation,[status(thm)],[c_983]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_3555,plain,
% 4.16/1.06      ( k2_struct_0(sK7) != X0
% 4.16/1.06      | v1_xboole_0(X0) != iProver_top
% 4.16/1.06      | v1_xboole_0(k2_struct_0(sK7)) = iProver_top ),
% 4.16/1.06      inference(predicate_to_equality,[status(thm)],[c_3554]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_3557,plain,
% 4.16/1.06      ( k2_struct_0(sK7) != k1_xboole_0
% 4.16/1.06      | v1_xboole_0(k2_struct_0(sK7)) = iProver_top
% 4.16/1.06      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 4.16/1.06      inference(instantiation,[status(thm)],[c_3555]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_48,plain,
% 4.16/1.06      ( v3_pre_topc(X0,X1)
% 4.16/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.16/1.06      | ~ v1_tdlat_3(X1)
% 4.16/1.06      | ~ v2_pre_topc(X1)
% 4.16/1.06      | ~ l1_pre_topc(X1) ),
% 4.16/1.06      inference(cnf_transformation,[],[f143]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_2957,plain,
% 4.16/1.06      ( v3_pre_topc(X0,sK6)
% 4.16/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 4.16/1.06      | ~ v1_tdlat_3(sK6)
% 4.16/1.06      | ~ v2_pre_topc(sK6)
% 4.16/1.06      | ~ l1_pre_topc(sK6) ),
% 4.16/1.06      inference(instantiation,[status(thm)],[c_48]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_3305,plain,
% 4.16/1.06      ( v3_pre_topc(k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,X0),sK6)
% 4.16/1.06      | ~ m1_subset_1(k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,X0),k1_zfmisc_1(u1_struct_0(sK6)))
% 4.16/1.06      | ~ v1_tdlat_3(sK6)
% 4.16/1.06      | ~ v2_pre_topc(sK6)
% 4.16/1.06      | ~ l1_pre_topc(sK6) ),
% 4.16/1.06      inference(instantiation,[status(thm)],[c_2957]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_3772,plain,
% 4.16/1.06      ( v3_pre_topc(k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,sK2(sK6,sK7,sK8)),sK6)
% 4.16/1.06      | ~ m1_subset_1(k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,sK2(sK6,sK7,sK8)),k1_zfmisc_1(u1_struct_0(sK6)))
% 4.16/1.06      | ~ v1_tdlat_3(sK6)
% 4.16/1.06      | ~ v2_pre_topc(sK6)
% 4.16/1.06      | ~ l1_pre_topc(sK6) ),
% 4.16/1.06      inference(instantiation,[status(thm)],[c_3305]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_35,plain,
% 4.16/1.06      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 4.16/1.06      | v5_pre_topc(X0,X1,X2)
% 4.16/1.06      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK2(X1,X2,X0)),X1)
% 4.16/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 4.16/1.06      | ~ v1_funct_1(X0)
% 4.16/1.06      | ~ l1_pre_topc(X1)
% 4.16/1.06      | ~ l1_pre_topc(X2)
% 4.16/1.06      | k2_struct_0(X2) = k1_xboole_0 ),
% 4.16/1.06      inference(cnf_transformation,[],[f137]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_3773,plain,
% 4.16/1.06      ( ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))
% 4.16/1.06      | v5_pre_topc(sK8,sK6,sK7)
% 4.16/1.06      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,sK2(sK6,sK7,sK8)),sK6)
% 4.16/1.06      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
% 4.16/1.06      | ~ v1_funct_1(sK8)
% 4.16/1.06      | ~ l1_pre_topc(sK7)
% 4.16/1.06      | ~ l1_pre_topc(sK6)
% 4.16/1.06      | k2_struct_0(sK7) = k1_xboole_0 ),
% 4.16/1.06      inference(instantiation,[status(thm)],[c_35]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_5312,plain,
% 4.16/1.06      ( ~ v1_xboole_0(u1_struct_0(sK7)) | v1_xboole_0(sK8) ),
% 4.16/1.06      inference(resolution,[status(thm)],[c_20,c_53]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_5313,plain,
% 4.16/1.06      ( v1_xboole_0(u1_struct_0(sK7)) != iProver_top
% 4.16/1.06      | v1_xboole_0(sK8) = iProver_top ),
% 4.16/1.06      inference(predicate_to_equality,[status(thm)],[c_5312]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_21,plain,
% 4.16/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.16/1.06      | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) ),
% 4.16/1.06      inference(cnf_transformation,[],[f117]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_2975,plain,
% 4.16/1.06      ( m1_subset_1(k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,X0),k1_zfmisc_1(u1_struct_0(sK6)))
% 4.16/1.06      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) ),
% 4.16/1.06      inference(instantiation,[status(thm)],[c_21]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_5500,plain,
% 4.16/1.06      ( m1_subset_1(k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,sK2(sK6,sK7,sK8)),k1_zfmisc_1(u1_struct_0(sK6)))
% 4.16/1.06      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) ),
% 4.16/1.06      inference(instantiation,[status(thm)],[c_2975]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_8406,plain,
% 4.16/1.06      ( v1_xboole_0(sK8) = iProver_top ),
% 4.16/1.06      inference(global_propositional_subsumption,
% 4.16/1.06                [status(thm)],
% 4.16/1.06                [c_8009,c_60,c_59,c_58,c_56,c_65,c_55,c_54,c_53,c_52,c_194,
% 4.16/1.06                 c_2856,c_3178,c_3180,c_3557,c_3772,c_3773,c_5313,c_5500]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_6,plain,
% 4.16/1.06      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 4.16/1.06      inference(cnf_transformation,[],[f102]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_2279,plain,
% 4.16/1.06      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 4.16/1.06      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_8411,plain,
% 4.16/1.06      ( sK8 = k1_xboole_0 ),
% 4.16/1.06      inference(superposition,[status(thm)],[c_8406,c_2279]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_9117,plain,
% 4.16/1.06      ( r1_tarski(sK3(sK6,sK7,k1_xboole_0),u1_struct_0(sK7)) = iProver_top ),
% 4.16/1.06      inference(light_normalisation,[status(thm)],[c_8540,c_8411]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_7,plain,
% 4.16/1.06      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 4.16/1.06      inference(cnf_transformation,[],[f105]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_2278,plain,
% 4.16/1.06      ( X0 = X1
% 4.16/1.06      | r1_tarski(X1,X0) != iProver_top
% 4.16/1.06      | r1_tarski(X0,X1) != iProver_top ),
% 4.16/1.06      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_9121,plain,
% 4.16/1.06      ( sK3(sK6,sK7,k1_xboole_0) = u1_struct_0(sK7)
% 4.16/1.06      | r1_tarski(u1_struct_0(sK7),sK3(sK6,sK7,k1_xboole_0)) != iProver_top ),
% 4.16/1.06      inference(superposition,[status(thm)],[c_9117,c_2278]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_13877,plain,
% 4.16/1.06      ( sK3(sK6,sK7,k1_xboole_0) = u1_struct_0(sK7)
% 4.16/1.06      | v1_xboole_0(u1_struct_0(sK7)) != iProver_top ),
% 4.16/1.06      inference(superposition,[status(thm)],[c_4304,c_9121]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_14184,plain,
% 4.16/1.06      ( sK3(sK6,sK7,k1_xboole_0) = u1_struct_0(sK7) ),
% 4.16/1.06      inference(global_propositional_subsumption,
% 4.16/1.06                [status(thm)],
% 4.16/1.06                [c_13877,c_60,c_59,c_58,c_56,c_65,c_55,c_54,c_53,c_52,c_194,
% 4.16/1.06                 c_2856,c_3178,c_3180,c_3557,c_3772,c_3773,c_5500]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_42,plain,
% 4.16/1.06      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 4.16/1.06      | v5_pre_topc(X0,X1,X2)
% 4.16/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 4.16/1.06      | ~ r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK3(X1,X2,X0))),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X2,sK3(X1,X2,X0))))
% 4.16/1.06      | ~ v1_funct_1(X0)
% 4.16/1.06      | ~ v2_pre_topc(X1)
% 4.16/1.06      | ~ v2_pre_topc(X2)
% 4.16/1.06      | ~ l1_pre_topc(X1)
% 4.16/1.06      | ~ l1_pre_topc(X2) ),
% 4.16/1.06      inference(cnf_transformation,[],[f141]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_2248,plain,
% 4.16/1.06      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 4.16/1.06      | v5_pre_topc(X0,X1,X2) = iProver_top
% 4.16/1.06      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 4.16/1.06      | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK3(X1,X2,X0))),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X2,sK3(X1,X2,X0)))) != iProver_top
% 4.16/1.06      | v1_funct_1(X0) != iProver_top
% 4.16/1.06      | v2_pre_topc(X1) != iProver_top
% 4.16/1.06      | v2_pre_topc(X2) != iProver_top
% 4.16/1.06      | l1_pre_topc(X1) != iProver_top
% 4.16/1.06      | l1_pre_topc(X2) != iProver_top ),
% 4.16/1.06      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_14222,plain,
% 4.16/1.06      ( v1_funct_2(k1_xboole_0,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
% 4.16/1.06      | v5_pre_topc(k1_xboole_0,sK6,sK7) = iProver_top
% 4.16/1.06      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) != iProver_top
% 4.16/1.06      | r1_tarski(k2_pre_topc(sK6,k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),k1_xboole_0,u1_struct_0(sK7))),k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),k1_xboole_0,k2_pre_topc(sK7,u1_struct_0(sK7)))) != iProver_top
% 4.16/1.06      | v1_funct_1(k1_xboole_0) != iProver_top
% 4.16/1.06      | v2_pre_topc(sK7) != iProver_top
% 4.16/1.06      | v2_pre_topc(sK6) != iProver_top
% 4.16/1.06      | l1_pre_topc(sK7) != iProver_top
% 4.16/1.06      | l1_pre_topc(sK6) != iProver_top ),
% 4.16/1.06      inference(superposition,[status(thm)],[c_14184,c_2248]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_0,plain,
% 4.16/1.06      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 4.16/1.06      inference(cnf_transformation,[],[f97]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_2285,plain,
% 4.16/1.06      ( r2_hidden(sK0(X0),X0) = iProver_top | v1_xboole_0(X0) = iProver_top ),
% 4.16/1.06      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_23,plain,
% 4.16/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.16/1.06      | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
% 4.16/1.06      inference(cnf_transformation,[],[f120]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_2267,plain,
% 4.16/1.06      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
% 4.16/1.06      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 4.16/1.06      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_6405,plain,
% 4.16/1.06      ( k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,u1_struct_0(sK7)) = k1_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8) ),
% 4.16/1.06      inference(superposition,[status(thm)],[c_2237,c_2267]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_22,plain,
% 4.16/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.16/1.06      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 4.16/1.06      inference(cnf_transformation,[],[f118]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_2268,plain,
% 4.16/1.06      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 4.16/1.06      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 4.16/1.06      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_4795,plain,
% 4.16/1.06      ( k1_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8) = k1_relat_1(sK8) ),
% 4.16/1.06      inference(superposition,[status(thm)],[c_2237,c_2268]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_6417,plain,
% 4.16/1.06      ( k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,u1_struct_0(sK7)) = k1_relat_1(sK8) ),
% 4.16/1.06      inference(light_normalisation,[status(thm)],[c_6405,c_4795]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_2269,plain,
% 4.16/1.06      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 4.16/1.06      | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) = iProver_top ),
% 4.16/1.06      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_6815,plain,
% 4.16/1.06      ( m1_subset_1(k1_relat_1(sK8),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
% 4.16/1.06      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) != iProver_top ),
% 4.16/1.06      inference(superposition,[status(thm)],[c_6417,c_2269]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_6823,plain,
% 4.16/1.06      ( m1_subset_1(k1_relat_1(sK8),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 4.16/1.06      inference(global_propositional_subsumption,[status(thm)],[c_6815,c_68]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_6828,plain,
% 4.16/1.06      ( r1_tarski(k1_relat_1(sK8),u1_struct_0(sK6)) = iProver_top ),
% 4.16/1.06      inference(superposition,[status(thm)],[c_6823,c_2274]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_4,plain,
% 4.16/1.06      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 4.16/1.06      inference(cnf_transformation,[],[f98]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_2281,plain,
% 4.16/1.06      ( r1_tarski(X0,X1) != iProver_top
% 4.16/1.06      | r2_hidden(X2,X0) != iProver_top
% 4.16/1.06      | r2_hidden(X2,X1) = iProver_top ),
% 4.16/1.06      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_6945,plain,
% 4.16/1.06      ( r2_hidden(X0,u1_struct_0(sK6)) = iProver_top
% 4.16/1.06      | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top ),
% 4.16/1.06      inference(superposition,[status(thm)],[c_6828,c_2281]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_6962,plain,
% 4.16/1.06      ( r2_hidden(sK0(k1_relat_1(sK8)),u1_struct_0(sK6)) = iProver_top
% 4.16/1.06      | v1_xboole_0(k1_relat_1(sK8)) = iProver_top ),
% 4.16/1.06      inference(superposition,[status(thm)],[c_2285,c_6945]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_8705,plain,
% 4.16/1.06      ( r2_hidden(sK0(k1_relat_1(k1_xboole_0)),u1_struct_0(sK6)) = iProver_top
% 4.16/1.06      | v1_xboole_0(k1_relat_1(k1_xboole_0)) = iProver_top ),
% 4.16/1.06      inference(demodulation,[status(thm)],[c_8411,c_6962]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_18,plain,
% 4.16/1.06      ( v4_relat_1(k1_xboole_0,X0) ),
% 4.16/1.06      inference(cnf_transformation,[],[f114]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_164,plain,
% 4.16/1.06      ( v4_relat_1(k1_xboole_0,X0) = iProver_top ),
% 4.16/1.06      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_166,plain,
% 4.16/1.06      ( v4_relat_1(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 4.16/1.06      inference(instantiation,[status(thm)],[c_164]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_19,plain,
% 4.16/1.06      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 4.16/1.06      inference(cnf_transformation,[],[f158]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_28,plain,
% 4.16/1.06      ( v1_partfun1(k6_partfun1(X0),X0) ),
% 4.16/1.06      inference(cnf_transformation,[],[f123]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_2262,plain,
% 4.16/1.06      ( v1_partfun1(k6_partfun1(X0),X0) = iProver_top ),
% 4.16/1.06      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_3192,plain,
% 4.16/1.06      ( v1_partfun1(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 4.16/1.06      inference(superposition,[status(thm)],[c_19,c_2262]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_10,plain,
% 4.16/1.06      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 4.16/1.06      inference(cnf_transformation,[],[f161]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_17,plain,
% 4.16/1.06      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 4.16/1.06      inference(cnf_transformation,[],[f113]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_2272,plain,
% 4.16/1.06      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 4.16/1.06      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_3320,plain,
% 4.16/1.06      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 4.16/1.06      inference(superposition,[status(thm)],[c_10,c_2272]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_26,plain,
% 4.16/1.06      ( ~ v1_partfun1(X0,X1)
% 4.16/1.06      | ~ v4_relat_1(X0,X1)
% 4.16/1.06      | ~ v1_relat_1(X0)
% 4.16/1.06      | k1_relat_1(X0) = X1 ),
% 4.16/1.06      inference(cnf_transformation,[],[f121]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_8987,plain,
% 4.16/1.06      ( ~ v1_partfun1(X0,X1)
% 4.16/1.06      | ~ v4_relat_1(X0,X1)
% 4.16/1.06      | ~ v1_relat_1(X0)
% 4.16/1.06      | ~ v1_xboole_0(X1)
% 4.16/1.06      | v1_xboole_0(k1_relat_1(X0)) ),
% 4.16/1.06      inference(resolution,[status(thm)],[c_26,c_983]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_8992,plain,
% 4.16/1.06      ( v1_partfun1(X0,X1) != iProver_top
% 4.16/1.06      | v4_relat_1(X0,X1) != iProver_top
% 4.16/1.06      | v1_relat_1(X0) != iProver_top
% 4.16/1.06      | v1_xboole_0(X1) != iProver_top
% 4.16/1.06      | v1_xboole_0(k1_relat_1(X0)) = iProver_top ),
% 4.16/1.06      inference(predicate_to_equality,[status(thm)],[c_8987]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_8994,plain,
% 4.16/1.06      ( v1_partfun1(k1_xboole_0,k1_xboole_0) != iProver_top
% 4.16/1.06      | v4_relat_1(k1_xboole_0,k1_xboole_0) != iProver_top
% 4.16/1.06      | v1_relat_1(k1_xboole_0) != iProver_top
% 4.16/1.06      | v1_xboole_0(k1_relat_1(k1_xboole_0)) = iProver_top
% 4.16/1.06      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 4.16/1.06      inference(instantiation,[status(thm)],[c_8992]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_11741,plain,
% 4.16/1.06      ( v1_xboole_0(k1_relat_1(k1_xboole_0)) = iProver_top ),
% 4.16/1.06      inference(global_propositional_subsumption,
% 4.16/1.06                [status(thm)],
% 4.16/1.06                [c_8705,c_166,c_194,c_3192,c_3320,c_8994]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_11746,plain,
% 4.16/1.06      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 4.16/1.06      inference(superposition,[status(thm)],[c_11741,c_2279]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_8711,plain,
% 4.16/1.06      ( k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),k1_xboole_0,u1_struct_0(sK7)) = k1_relat_1(k1_xboole_0) ),
% 4.16/1.06      inference(demodulation,[status(thm)],[c_8411,c_6417]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_12698,plain,
% 4.16/1.06      ( k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),k1_xboole_0,u1_struct_0(sK7)) = k1_xboole_0 ),
% 4.16/1.06      inference(demodulation,[status(thm)],[c_11746,c_8711]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_8710,plain,
% 4.16/1.06      ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 4.16/1.06      inference(demodulation,[status(thm)],[c_8411,c_6823]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_33,plain,
% 4.16/1.06      ( ~ v4_pre_topc(X0,X1)
% 4.16/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.16/1.06      | ~ l1_pre_topc(X1)
% 4.16/1.06      | k2_pre_topc(X1,X0) = X0 ),
% 4.16/1.06      inference(cnf_transformation,[],[f129]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_2257,plain,
% 4.16/1.06      ( k2_pre_topc(X0,X1) = X1
% 4.16/1.06      | v4_pre_topc(X1,X0) != iProver_top
% 4.16/1.06      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 4.16/1.06      | l1_pre_topc(X0) != iProver_top ),
% 4.16/1.06      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_10905,plain,
% 4.16/1.06      ( k2_pre_topc(sK6,k1_relat_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0)
% 4.16/1.06      | v4_pre_topc(k1_relat_1(k1_xboole_0),sK6) != iProver_top
% 4.16/1.06      | l1_pre_topc(sK6) != iProver_top ),
% 4.16/1.06      inference(superposition,[status(thm)],[c_8710,c_2257]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_13880,plain,
% 4.16/1.06      ( v4_pre_topc(k1_relat_1(k1_xboole_0),sK6) != iProver_top
% 4.16/1.06      | k2_pre_topc(sK6,k1_relat_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0) ),
% 4.16/1.06      inference(global_propositional_subsumption,[status(thm)],[c_10905,c_63]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_13881,plain,
% 4.16/1.06      ( k2_pre_topc(sK6,k1_relat_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0)
% 4.16/1.06      | v4_pre_topc(k1_relat_1(k1_xboole_0),sK6) != iProver_top ),
% 4.16/1.06      inference(renaming,[status(thm)],[c_13880]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_13884,plain,
% 4.16/1.06      ( k2_pre_topc(sK6,k1_xboole_0) = k1_xboole_0
% 4.16/1.06      | v4_pre_topc(k1_xboole_0,sK6) != iProver_top ),
% 4.16/1.06      inference(light_normalisation,[status(thm)],[c_13881,c_11746]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_51,plain,
% 4.16/1.06      ( v4_pre_topc(X0,X1)
% 4.16/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.16/1.06      | ~ v1_tdlat_3(X1)
% 4.16/1.06      | ~ v2_pre_topc(X1)
% 4.16/1.06      | ~ l1_pre_topc(X1) ),
% 4.16/1.06      inference(cnf_transformation,[],[f146]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_2962,plain,
% 4.16/1.06      ( v4_pre_topc(X0,sK6)
% 4.16/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 4.16/1.06      | ~ v1_tdlat_3(sK6)
% 4.16/1.06      | ~ v2_pre_topc(sK6)
% 4.16/1.06      | ~ l1_pre_topc(sK6) ),
% 4.16/1.06      inference(instantiation,[status(thm)],[c_51]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_2964,plain,
% 4.16/1.06      ( v4_pre_topc(k1_xboole_0,sK6)
% 4.16/1.06      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6)))
% 4.16/1.06      | ~ v1_tdlat_3(sK6)
% 4.16/1.06      | ~ v2_pre_topc(sK6)
% 4.16/1.06      | ~ l1_pre_topc(sK6) ),
% 4.16/1.06      inference(instantiation,[status(thm)],[c_2962]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_13,plain,
% 4.16/1.06      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 4.16/1.06      inference(cnf_transformation,[],[f109]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_3297,plain,
% 4.16/1.06      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 4.16/1.06      inference(instantiation,[status(thm)],[c_13]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_3721,plain,
% 4.16/1.06      ( ~ v4_pre_topc(X0,sK6)
% 4.16/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 4.16/1.06      | ~ l1_pre_topc(sK6)
% 4.16/1.06      | k2_pre_topc(sK6,X0) = X0 ),
% 4.16/1.06      inference(instantiation,[status(thm)],[c_33]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_3723,plain,
% 4.16/1.06      ( ~ v4_pre_topc(k1_xboole_0,sK6)
% 4.16/1.06      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6)))
% 4.16/1.06      | ~ l1_pre_topc(sK6)
% 4.16/1.06      | k2_pre_topc(sK6,k1_xboole_0) = k1_xboole_0 ),
% 4.16/1.06      inference(instantiation,[status(thm)],[c_3721]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_13888,plain,
% 4.16/1.06      ( k2_pre_topc(sK6,k1_xboole_0) = k1_xboole_0 ),
% 4.16/1.06      inference(global_propositional_subsumption,
% 4.16/1.06                [status(thm)],
% 4.16/1.06                [c_13884,c_60,c_59,c_58,c_2964,c_3297,c_3723]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_14224,plain,
% 4.16/1.06      ( v1_funct_2(k1_xboole_0,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
% 4.16/1.06      | v5_pre_topc(k1_xboole_0,sK6,sK7) = iProver_top
% 4.16/1.06      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) != iProver_top
% 4.16/1.06      | r1_tarski(k1_xboole_0,k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),k1_xboole_0,k2_pre_topc(sK7,u1_struct_0(sK7)))) != iProver_top
% 4.16/1.06      | v1_funct_1(k1_xboole_0) != iProver_top
% 4.16/1.06      | v2_pre_topc(sK7) != iProver_top
% 4.16/1.06      | v2_pre_topc(sK6) != iProver_top
% 4.16/1.06      | l1_pre_topc(sK7) != iProver_top
% 4.16/1.06      | l1_pre_topc(sK6) != iProver_top ),
% 4.16/1.06      inference(light_normalisation,[status(thm)],[c_14222,c_12698,c_13888]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_3275,plain,
% 4.16/1.06      ( ~ v1_xboole_0(sK8) | k1_xboole_0 = sK8 ),
% 4.16/1.06      inference(instantiation,[status(thm)],[c_6]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_3556,plain,
% 4.16/1.06      ( v1_xboole_0(k2_struct_0(sK7))
% 4.16/1.06      | ~ v1_xboole_0(k1_xboole_0)
% 4.16/1.06      | k2_struct_0(sK7) != k1_xboole_0 ),
% 4.16/1.06      inference(instantiation,[status(thm)],[c_3554]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_981,plain,( X0 = X0 ),theory(equality) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_3945,plain,
% 4.16/1.06      ( u1_struct_0(sK6) = u1_struct_0(sK6) ),
% 4.16/1.06      inference(instantiation,[status(thm)],[c_981]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_1002,plain,
% 4.16/1.06      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 4.16/1.06      theory(equality) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_3593,plain,
% 4.16/1.06      ( ~ v1_funct_1(X0) | v1_funct_1(k1_xboole_0) | ~ v1_xboole_0(X0) ),
% 4.16/1.06      inference(resolution,[status(thm)],[c_6,c_1002]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_4199,plain,
% 4.16/1.06      ( v1_funct_1(k1_xboole_0) | ~ v1_xboole_0(sK8) ),
% 4.16/1.06      inference(resolution,[status(thm)],[c_3593,c_55]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_4200,plain,
% 4.16/1.06      ( v1_funct_1(k1_xboole_0) = iProver_top
% 4.16/1.06      | v1_xboole_0(sK8) != iProver_top ),
% 4.16/1.06      inference(predicate_to_equality,[status(thm)],[c_4199]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_4599,plain,
% 4.16/1.06      ( u1_struct_0(sK7) = u1_struct_0(sK7) ),
% 4.16/1.06      inference(instantiation,[status(thm)],[c_981]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_1001,plain,
% 4.16/1.06      ( ~ v1_funct_2(X0,X1,X2)
% 4.16/1.06      | v1_funct_2(X3,X4,X5)
% 4.16/1.06      | X3 != X0
% 4.16/1.06      | X4 != X1
% 4.16/1.06      | X5 != X2 ),
% 4.16/1.06      theory(equality) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_3026,plain,
% 4.16/1.06      ( v1_funct_2(X0,X1,X2)
% 4.16/1.06      | ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))
% 4.16/1.06      | X2 != u1_struct_0(sK7)
% 4.16/1.06      | X1 != u1_struct_0(sK6)
% 4.16/1.06      | X0 != sK8 ),
% 4.16/1.06      inference(instantiation,[status(thm)],[c_1001]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_4598,plain,
% 4.16/1.06      ( v1_funct_2(X0,X1,u1_struct_0(sK7))
% 4.16/1.06      | ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))
% 4.16/1.06      | X1 != u1_struct_0(sK6)
% 4.16/1.06      | X0 != sK8
% 4.16/1.06      | u1_struct_0(sK7) != u1_struct_0(sK7) ),
% 4.16/1.06      inference(instantiation,[status(thm)],[c_3026]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_5653,plain,
% 4.16/1.06      ( v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(sK7))
% 4.16/1.06      | ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))
% 4.16/1.06      | X0 != sK8
% 4.16/1.06      | u1_struct_0(sK7) != u1_struct_0(sK7)
% 4.16/1.06      | u1_struct_0(sK6) != u1_struct_0(sK6) ),
% 4.16/1.06      inference(instantiation,[status(thm)],[c_4598]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_5654,plain,
% 4.16/1.06      ( X0 != sK8
% 4.16/1.06      | u1_struct_0(sK7) != u1_struct_0(sK7)
% 4.16/1.06      | u1_struct_0(sK6) != u1_struct_0(sK6)
% 4.16/1.06      | v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(sK7)) = iProver_top
% 4.16/1.06      | v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top ),
% 4.16/1.06      inference(predicate_to_equality,[status(thm)],[c_5653]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_5656,plain,
% 4.16/1.06      ( u1_struct_0(sK7) != u1_struct_0(sK7)
% 4.16/1.06      | u1_struct_0(sK6) != u1_struct_0(sK6)
% 4.16/1.06      | k1_xboole_0 != sK8
% 4.16/1.06      | v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
% 4.16/1.06      | v1_funct_2(k1_xboole_0,u1_struct_0(sK6),u1_struct_0(sK7)) = iProver_top ),
% 4.16/1.06      inference(instantiation,[status(thm)],[c_5654]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_2238,plain,
% 4.16/1.06      ( v5_pre_topc(sK8,sK6,sK7) != iProver_top ),
% 4.16/1.06      inference(predicate_to_equality,[status(thm)],[c_52]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_8722,plain,
% 4.16/1.06      ( v5_pre_topc(k1_xboole_0,sK6,sK7) != iProver_top ),
% 4.16/1.06      inference(demodulation,[status(thm)],[c_8411,c_2238]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_988,plain,
% 4.16/1.06      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 4.16/1.06      theory(equality) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_9199,plain,
% 4.16/1.06      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X1) | X2 != X0 ),
% 4.16/1.06      inference(resolution,[status(thm)],[c_988,c_981]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_12032,plain,
% 4.16/1.06      ( ~ m1_subset_1(X0,X1)
% 4.16/1.06      | m1_subset_1(k1_xboole_0,X1)
% 4.16/1.06      | ~ v1_xboole_0(X0) ),
% 4.16/1.06      inference(resolution,[status(thm)],[c_9199,c_6]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_12302,plain,
% 4.16/1.06      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
% 4.16/1.06      | ~ v1_xboole_0(sK8) ),
% 4.16/1.06      inference(resolution,[status(thm)],[c_12032,c_53]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_12303,plain,
% 4.16/1.06      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) = iProver_top
% 4.16/1.06      | v1_xboole_0(sK8) != iProver_top ),
% 4.16/1.06      inference(predicate_to_equality,[status(thm)],[c_12302]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_15589,plain,
% 4.16/1.06      ( r1_tarski(k1_xboole_0,k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),k1_xboole_0,k2_pre_topc(sK7,u1_struct_0(sK7)))) != iProver_top ),
% 4.16/1.06      inference(global_propositional_subsumption,
% 4.16/1.06                [status(thm)],
% 4.16/1.06                [c_14224,c_60,c_61,c_59,c_58,c_63,c_64,c_56,c_65,c_55,c_54,
% 4.16/1.06                 c_67,c_53,c_52,c_5,c_194,c_2855,c_2856,c_3177,c_3178,c_3176,
% 4.16/1.06                 c_3180,c_3275,c_3556,c_3557,c_3772,c_3773,c_3945,c_4200,
% 4.16/1.06                 c_4599,c_5312,c_5313,c_5500,c_5656,c_8722,c_12303]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_2276,plain,
% 4.16/1.06      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 4.16/1.06      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_3876,plain,
% 4.16/1.06      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 4.16/1.06      inference(superposition,[status(thm)],[c_2276,c_2274]) ).
% 4.16/1.06  
% 4.16/1.06  cnf(c_15594,plain,
% 4.16/1.06      ( $false ),
% 4.16/1.06      inference(forward_subsumption_resolution,[status(thm)],[c_15589,c_3876]) ).
% 4.16/1.06  
% 4.16/1.06  
% 4.16/1.06  % SZS output end CNFRefutation for theBenchmark.p
% 4.16/1.06  
% 4.16/1.06  ------                               Statistics
% 4.16/1.06  
% 4.16/1.06  ------ Selected
% 4.16/1.06  
% 4.16/1.06  total_time:                             0.522
% 4.16/1.06  
%------------------------------------------------------------------------------
