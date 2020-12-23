%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:35 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 557 expanded)
%              Number of clauses        :   73 ( 141 expanded)
%              Number of leaves         :   14 ( 149 expanded)
%              Depth                    :   21
%              Number of atoms          :  523 (3937 expanded)
%              Number of equality atoms :   89 ( 502 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,X3)
                            & v3_pre_topc(X3,X0) ) )
                    & r2_hidden(X2,X1) ) )
           => v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ? [X2] :
              ( ! [X3] :
                  ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,X3)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ? [X2] :
              ( ! [X3] :
                  ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,X3)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,X3)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( k6_domain_1(u1_struct_0(X0),sK2(X0,X1)) != k9_subset_1(u1_struct_0(X0),X1,X3)
            | ~ v3_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r2_hidden(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ( ! [X3] :
                ( k6_domain_1(u1_struct_0(X0),sK2(X0,X1)) != k9_subset_1(u1_struct_0(X0),X1,X3)
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & r2_hidden(sK2(X0,X1),X1)
            & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f42])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,X1)
                 => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) )
           => v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( r2_hidden(X2,X1)
                   => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) )
             => v2_tex_2(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & ! [X2] :
              ( k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & ! [X2] :
              ( k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & ! [X2] :
              ( k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v2_tex_2(sK4,X0)
        & ! [X2] :
            ( k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),sK4,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
            | ~ r2_hidden(X2,sK4)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tex_2(X1,X0)
            & ! [X2] :
                ( k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v2_tex_2(X1,sK3)
          & ! [X2] :
              ( k6_domain_1(u1_struct_0(sK3),X2) = k9_subset_1(u1_struct_0(sK3),X1,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X2)))
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(sK3)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) )
      & l1_pre_topc(sK3)
      & v3_tdlat_3(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ~ v2_tex_2(sK4,sK3)
    & ! [X2] :
        ( k6_domain_1(u1_struct_0(sK3),X2) = k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X2)))
        | ~ r2_hidden(X2,sK4)
        | ~ m1_subset_1(X2,u1_struct_0(sK3)) )
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & l1_pre_topc(sK3)
    & v3_tdlat_3(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f28,f45,f44])).

fof(f78,plain,(
    ~ v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f72,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f73,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f75,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f76,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f46])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | r2_hidden(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f77,plain,(
    ! [X2] :
      ( k6_domain_1(u1_struct_0(sK3),X2) = k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X2)))
      | ~ r2_hidden(X2,sK4)
      | ~ m1_subset_1(X2,u1_struct_0(sK3)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( v2_tex_2(X1,X0)
      | k6_domain_1(u1_struct_0(X0),sK2(X0,X1)) != k9_subset_1(u1_struct_0(X0),X1,X3)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f38,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v3_pre_topc(X1,X0)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f39,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK1(X0),X0)
        & v4_pre_topc(sK1(X0),X0)
        & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK1(X0),X0)
            & v4_pre_topc(sK1(X0),X0)
            & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).

fof(f65,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f74,plain,(
    v3_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_24,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X1,X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_25,negated_conjecture,
    ( ~ v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_447,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X1,X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_25])).

cnf(c_448,plain,
    ( m1_subset_1(sK2(sK3,sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_447])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_30,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_28,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_450,plain,
    ( m1_subset_1(sK2(sK3,sK4),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_448,c_31,c_30,c_28,c_27])).

cnf(c_1247,plain,
    ( m1_subset_1(sK2(sK3,sK4),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_450])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1251,plain,
    ( k6_domain_1(X0,X1) = k1_tarski(X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3133,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK2(sK3,sK4)) = k1_tarski(sK2(sK3,sK4))
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1247,c_1251])).

cnf(c_23,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(sK2(X1,X0),X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_458,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(sK2(X1,X0),X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_25])).

cnf(c_459,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(sK2(sK3,sK4),sK4)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_458])).

cnf(c_1471,plain,
    ( ~ m1_subset_1(sK2(sK3,sK4),u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3))
    | k6_domain_1(u1_struct_0(sK3),sK2(sK3,sK4)) = k1_tarski(sK2(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1249,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1252,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1749,plain,
    ( r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1249,c_1252])).

cnf(c_1757,plain,
    ( r1_tarski(sK4,u1_struct_0(sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1749])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_12,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_239,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_12])).

cnf(c_240,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_239])).

cnf(c_299,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_14,c_240])).

cnf(c_1536,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,u1_struct_0(sK3))
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_299])).

cnf(c_1769,plain,
    ( ~ r2_hidden(sK2(sK3,sK4),sK4)
    | ~ r1_tarski(sK4,u1_struct_0(sK3))
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1536])).

cnf(c_3478,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK2(sK3,sK4)) = k1_tarski(sK2(sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3133,c_31,c_30,c_28,c_27,c_448,c_459,c_1471,c_1757,c_1769])).

cnf(c_1253,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_26,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ r2_hidden(X0,sK4)
    | k6_domain_1(u1_struct_0(sK3),X0) = k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X0))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1250,plain,
    ( k6_domain_1(u1_struct_0(sK3),X0) = k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X0)))
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1458,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK2(sK3,sK4)))) = k6_domain_1(u1_struct_0(sK3),sK2(sK3,sK4))
    | r2_hidden(sK2(sK3,sK4),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1247,c_1250])).

cnf(c_32,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_33,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_35,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_36,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_460,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(sK2(sK3,sK4),sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_459])).

cnf(c_1509,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK2(sK3,sK4)))) = k6_domain_1(u1_struct_0(sK3),sK2(sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1458,c_32,c_33,c_35,c_36,c_460])).

cnf(c_22,plain,
    ( v2_tex_2(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k6_domain_1(u1_struct_0(X1),sK2(X1,X0)) != k9_subset_1(u1_struct_0(X1),X0,X2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_469,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k6_domain_1(u1_struct_0(X1),sK2(X1,X2)) != k9_subset_1(u1_struct_0(X1),X2,X0)
    | sK3 != X1
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_25])).

cnf(c_470,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | k6_domain_1(u1_struct_0(sK3),sK2(sK3,sK4)) != k9_subset_1(u1_struct_0(sK3),sK4,X0) ),
    inference(unflattening,[status(thm)],[c_469])).

cnf(c_474,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k6_domain_1(u1_struct_0(sK3),sK2(sK3,sK4)) != k9_subset_1(u1_struct_0(sK3),sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_470,c_31,c_30,c_28,c_27])).

cnf(c_17,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_21,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_413,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | X1 != X3
    | k2_pre_topc(X3,X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_21])).

cnf(c_414,plain,
    ( v3_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v3_tdlat_3(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_413])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_430,plain,
    ( v3_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v3_tdlat_3(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_414,c_15])).

cnf(c_498,plain,
    ( v3_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v3_tdlat_3(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_430,c_30])).

cnf(c_499,plain,
    ( v3_pre_topc(k2_pre_topc(sK3,X0),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v3_tdlat_3(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_498])).

cnf(c_29,negated_conjecture,
    ( v3_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_503,plain,
    ( v3_pre_topc(k2_pre_topc(sK3,X0),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_499,c_29,c_28])).

cnf(c_538,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | k6_domain_1(u1_struct_0(sK3),sK2(sK3,sK4)) != k9_subset_1(u1_struct_0(sK3),sK4,X0)
    | k2_pre_topc(sK3,X1) != X0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_474,c_503])).

cnf(c_539,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k2_pre_topc(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | k6_domain_1(u1_struct_0(sK3),sK2(sK3,sK4)) != k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X0)) ),
    inference(unflattening,[status(thm)],[c_538])).

cnf(c_523,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_28])).

cnf(c_524,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k2_pre_topc(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unflattening,[status(thm)],[c_523])).

cnf(c_543,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k6_domain_1(u1_struct_0(sK3),sK2(sK3,sK4)) != k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_539,c_524])).

cnf(c_1244,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK2(sK3,sK4)) != k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_543])).

cnf(c_1547,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK2(sK3,sK4)),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1509,c_1244])).

cnf(c_1765,plain,
    ( r1_tarski(k6_domain_1(u1_struct_0(sK3),sK2(sK3,sK4)),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1253,c_1547])).

cnf(c_3481,plain,
    ( r1_tarski(k1_tarski(sK2(sK3,sK4)),u1_struct_0(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3478,c_1765])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1728,plain,
    ( ~ r2_hidden(sK2(sK3,sK4),X0)
    | r1_tarski(k1_tarski(sK2(sK3,sK4)),X0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2189,plain,
    ( ~ r2_hidden(sK2(sK3,sK4),u1_struct_0(sK3))
    | r1_tarski(k1_tarski(sK2(sK3,sK4)),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1728])).

cnf(c_2190,plain,
    ( r2_hidden(sK2(sK3,sK4),u1_struct_0(sK3)) != iProver_top
    | r1_tarski(k1_tarski(sK2(sK3,sK4)),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2189])).

cnf(c_1770,plain,
    ( r2_hidden(sK2(sK3,sK4),sK4) != iProver_top
    | r1_tarski(sK4,u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1769])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1451,plain,
    ( ~ m1_subset_1(sK2(sK3,sK4),u1_struct_0(sK3))
    | r2_hidden(sK2(sK3,sK4),u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1452,plain,
    ( m1_subset_1(sK2(sK3,sK4),u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK2(sK3,sK4),u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1451])).

cnf(c_449,plain,
    ( m1_subset_1(sK2(sK3,sK4),u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_448])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3481,c_2190,c_1770,c_1749,c_1452,c_460,c_449,c_36,c_35,c_33,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:52:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.67/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.01  
% 2.67/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.67/1.01  
% 2.67/1.01  ------  iProver source info
% 2.67/1.01  
% 2.67/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.67/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.67/1.01  git: non_committed_changes: false
% 2.67/1.01  git: last_make_outside_of_git: false
% 2.67/1.01  
% 2.67/1.01  ------ 
% 2.67/1.01  
% 2.67/1.01  ------ Input Options
% 2.67/1.01  
% 2.67/1.01  --out_options                           all
% 2.67/1.01  --tptp_safe_out                         true
% 2.67/1.01  --problem_path                          ""
% 2.67/1.01  --include_path                          ""
% 2.67/1.01  --clausifier                            res/vclausify_rel
% 2.67/1.01  --clausifier_options                    --mode clausify
% 2.67/1.01  --stdin                                 false
% 2.67/1.01  --stats_out                             all
% 2.67/1.01  
% 2.67/1.01  ------ General Options
% 2.67/1.01  
% 2.67/1.01  --fof                                   false
% 2.67/1.01  --time_out_real                         305.
% 2.67/1.01  --time_out_virtual                      -1.
% 2.67/1.01  --symbol_type_check                     false
% 2.67/1.01  --clausify_out                          false
% 2.67/1.01  --sig_cnt_out                           false
% 2.67/1.01  --trig_cnt_out                          false
% 2.67/1.01  --trig_cnt_out_tolerance                1.
% 2.67/1.01  --trig_cnt_out_sk_spl                   false
% 2.67/1.01  --abstr_cl_out                          false
% 2.67/1.01  
% 2.67/1.01  ------ Global Options
% 2.67/1.01  
% 2.67/1.01  --schedule                              default
% 2.67/1.01  --add_important_lit                     false
% 2.67/1.01  --prop_solver_per_cl                    1000
% 2.67/1.01  --min_unsat_core                        false
% 2.67/1.01  --soft_assumptions                      false
% 2.67/1.01  --soft_lemma_size                       3
% 2.67/1.01  --prop_impl_unit_size                   0
% 2.67/1.01  --prop_impl_unit                        []
% 2.67/1.01  --share_sel_clauses                     true
% 2.67/1.01  --reset_solvers                         false
% 2.67/1.01  --bc_imp_inh                            [conj_cone]
% 2.67/1.01  --conj_cone_tolerance                   3.
% 2.67/1.01  --extra_neg_conj                        none
% 2.67/1.01  --large_theory_mode                     true
% 2.67/1.01  --prolific_symb_bound                   200
% 2.67/1.01  --lt_threshold                          2000
% 2.67/1.01  --clause_weak_htbl                      true
% 2.67/1.01  --gc_record_bc_elim                     false
% 2.67/1.01  
% 2.67/1.01  ------ Preprocessing Options
% 2.67/1.01  
% 2.67/1.01  --preprocessing_flag                    true
% 2.67/1.01  --time_out_prep_mult                    0.1
% 2.67/1.01  --splitting_mode                        input
% 2.67/1.01  --splitting_grd                         true
% 2.67/1.01  --splitting_cvd                         false
% 2.67/1.01  --splitting_cvd_svl                     false
% 2.67/1.01  --splitting_nvd                         32
% 2.67/1.01  --sub_typing                            true
% 2.67/1.01  --prep_gs_sim                           true
% 2.67/1.01  --prep_unflatten                        true
% 2.67/1.01  --prep_res_sim                          true
% 2.67/1.01  --prep_upred                            true
% 2.67/1.01  --prep_sem_filter                       exhaustive
% 2.67/1.01  --prep_sem_filter_out                   false
% 2.67/1.01  --pred_elim                             true
% 2.67/1.01  --res_sim_input                         true
% 2.67/1.01  --eq_ax_congr_red                       true
% 2.67/1.01  --pure_diseq_elim                       true
% 2.67/1.01  --brand_transform                       false
% 2.67/1.01  --non_eq_to_eq                          false
% 2.67/1.01  --prep_def_merge                        true
% 2.67/1.01  --prep_def_merge_prop_impl              false
% 2.67/1.01  --prep_def_merge_mbd                    true
% 2.67/1.01  --prep_def_merge_tr_red                 false
% 2.67/1.01  --prep_def_merge_tr_cl                  false
% 2.67/1.01  --smt_preprocessing                     true
% 2.67/1.01  --smt_ac_axioms                         fast
% 2.67/1.01  --preprocessed_out                      false
% 2.67/1.01  --preprocessed_stats                    false
% 2.67/1.01  
% 2.67/1.01  ------ Abstraction refinement Options
% 2.67/1.01  
% 2.67/1.01  --abstr_ref                             []
% 2.67/1.01  --abstr_ref_prep                        false
% 2.67/1.01  --abstr_ref_until_sat                   false
% 2.67/1.01  --abstr_ref_sig_restrict                funpre
% 2.67/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.67/1.01  --abstr_ref_under                       []
% 2.67/1.01  
% 2.67/1.01  ------ SAT Options
% 2.67/1.01  
% 2.67/1.01  --sat_mode                              false
% 2.67/1.01  --sat_fm_restart_options                ""
% 2.67/1.01  --sat_gr_def                            false
% 2.67/1.01  --sat_epr_types                         true
% 2.67/1.01  --sat_non_cyclic_types                  false
% 2.67/1.01  --sat_finite_models                     false
% 2.67/1.01  --sat_fm_lemmas                         false
% 2.67/1.01  --sat_fm_prep                           false
% 2.67/1.01  --sat_fm_uc_incr                        true
% 2.67/1.01  --sat_out_model                         small
% 2.67/1.01  --sat_out_clauses                       false
% 2.67/1.01  
% 2.67/1.01  ------ QBF Options
% 2.67/1.01  
% 2.67/1.01  --qbf_mode                              false
% 2.67/1.01  --qbf_elim_univ                         false
% 2.67/1.01  --qbf_dom_inst                          none
% 2.67/1.01  --qbf_dom_pre_inst                      false
% 2.67/1.01  --qbf_sk_in                             false
% 2.67/1.01  --qbf_pred_elim                         true
% 2.67/1.01  --qbf_split                             512
% 2.67/1.01  
% 2.67/1.01  ------ BMC1 Options
% 2.67/1.01  
% 2.67/1.01  --bmc1_incremental                      false
% 2.67/1.01  --bmc1_axioms                           reachable_all
% 2.67/1.01  --bmc1_min_bound                        0
% 2.67/1.01  --bmc1_max_bound                        -1
% 2.67/1.01  --bmc1_max_bound_default                -1
% 2.67/1.01  --bmc1_symbol_reachability              true
% 2.67/1.01  --bmc1_property_lemmas                  false
% 2.67/1.01  --bmc1_k_induction                      false
% 2.67/1.01  --bmc1_non_equiv_states                 false
% 2.67/1.01  --bmc1_deadlock                         false
% 2.67/1.01  --bmc1_ucm                              false
% 2.67/1.01  --bmc1_add_unsat_core                   none
% 2.67/1.01  --bmc1_unsat_core_children              false
% 2.67/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.67/1.01  --bmc1_out_stat                         full
% 2.67/1.01  --bmc1_ground_init                      false
% 2.67/1.01  --bmc1_pre_inst_next_state              false
% 2.67/1.01  --bmc1_pre_inst_state                   false
% 2.67/1.01  --bmc1_pre_inst_reach_state             false
% 2.67/1.01  --bmc1_out_unsat_core                   false
% 2.67/1.01  --bmc1_aig_witness_out                  false
% 2.67/1.01  --bmc1_verbose                          false
% 2.67/1.01  --bmc1_dump_clauses_tptp                false
% 2.67/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.67/1.01  --bmc1_dump_file                        -
% 2.67/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.67/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.67/1.01  --bmc1_ucm_extend_mode                  1
% 2.67/1.01  --bmc1_ucm_init_mode                    2
% 2.67/1.01  --bmc1_ucm_cone_mode                    none
% 2.67/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.67/1.01  --bmc1_ucm_relax_model                  4
% 2.67/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.67/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.67/1.01  --bmc1_ucm_layered_model                none
% 2.67/1.01  --bmc1_ucm_max_lemma_size               10
% 2.67/1.01  
% 2.67/1.01  ------ AIG Options
% 2.67/1.01  
% 2.67/1.01  --aig_mode                              false
% 2.67/1.01  
% 2.67/1.01  ------ Instantiation Options
% 2.67/1.01  
% 2.67/1.01  --instantiation_flag                    true
% 2.67/1.01  --inst_sos_flag                         false
% 2.67/1.01  --inst_sos_phase                        true
% 2.67/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.67/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.67/1.01  --inst_lit_sel_side                     num_symb
% 2.67/1.01  --inst_solver_per_active                1400
% 2.67/1.01  --inst_solver_calls_frac                1.
% 2.67/1.01  --inst_passive_queue_type               priority_queues
% 2.67/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.67/1.01  --inst_passive_queues_freq              [25;2]
% 2.67/1.01  --inst_dismatching                      true
% 2.67/1.01  --inst_eager_unprocessed_to_passive     true
% 2.67/1.01  --inst_prop_sim_given                   true
% 2.67/1.01  --inst_prop_sim_new                     false
% 2.67/1.01  --inst_subs_new                         false
% 2.67/1.01  --inst_eq_res_simp                      false
% 2.67/1.01  --inst_subs_given                       false
% 2.67/1.01  --inst_orphan_elimination               true
% 2.67/1.01  --inst_learning_loop_flag               true
% 2.67/1.01  --inst_learning_start                   3000
% 2.67/1.01  --inst_learning_factor                  2
% 2.67/1.01  --inst_start_prop_sim_after_learn       3
% 2.67/1.01  --inst_sel_renew                        solver
% 2.67/1.01  --inst_lit_activity_flag                true
% 2.67/1.01  --inst_restr_to_given                   false
% 2.67/1.01  --inst_activity_threshold               500
% 2.67/1.01  --inst_out_proof                        true
% 2.67/1.01  
% 2.67/1.01  ------ Resolution Options
% 2.67/1.01  
% 2.67/1.01  --resolution_flag                       true
% 2.67/1.01  --res_lit_sel                           adaptive
% 2.67/1.01  --res_lit_sel_side                      none
% 2.67/1.01  --res_ordering                          kbo
% 2.67/1.01  --res_to_prop_solver                    active
% 2.67/1.01  --res_prop_simpl_new                    false
% 2.67/1.01  --res_prop_simpl_given                  true
% 2.67/1.01  --res_passive_queue_type                priority_queues
% 2.67/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.67/1.01  --res_passive_queues_freq               [15;5]
% 2.67/1.01  --res_forward_subs                      full
% 2.67/1.01  --res_backward_subs                     full
% 2.67/1.01  --res_forward_subs_resolution           true
% 2.67/1.01  --res_backward_subs_resolution          true
% 2.67/1.01  --res_orphan_elimination                true
% 2.67/1.01  --res_time_limit                        2.
% 2.67/1.01  --res_out_proof                         true
% 2.67/1.01  
% 2.67/1.01  ------ Superposition Options
% 2.67/1.01  
% 2.67/1.01  --superposition_flag                    true
% 2.67/1.01  --sup_passive_queue_type                priority_queues
% 2.67/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.67/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.67/1.01  --demod_completeness_check              fast
% 2.67/1.01  --demod_use_ground                      true
% 2.67/1.01  --sup_to_prop_solver                    passive
% 2.67/1.01  --sup_prop_simpl_new                    true
% 2.67/1.01  --sup_prop_simpl_given                  true
% 2.67/1.01  --sup_fun_splitting                     false
% 2.67/1.01  --sup_smt_interval                      50000
% 2.67/1.01  
% 2.67/1.01  ------ Superposition Simplification Setup
% 2.67/1.01  
% 2.67/1.01  --sup_indices_passive                   []
% 2.67/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.67/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/1.01  --sup_full_bw                           [BwDemod]
% 2.67/1.01  --sup_immed_triv                        [TrivRules]
% 2.67/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.67/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/1.01  --sup_immed_bw_main                     []
% 2.67/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.67/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/1.01  
% 2.67/1.01  ------ Combination Options
% 2.67/1.01  
% 2.67/1.01  --comb_res_mult                         3
% 2.67/1.01  --comb_sup_mult                         2
% 2.67/1.01  --comb_inst_mult                        10
% 2.67/1.01  
% 2.67/1.01  ------ Debug Options
% 2.67/1.01  
% 2.67/1.01  --dbg_backtrace                         false
% 2.67/1.01  --dbg_dump_prop_clauses                 false
% 2.67/1.01  --dbg_dump_prop_clauses_file            -
% 2.67/1.01  --dbg_out_stat                          false
% 2.67/1.01  ------ Parsing...
% 2.67/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.67/1.01  
% 2.67/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 2.67/1.01  
% 2.67/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.67/1.01  
% 2.67/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.67/1.01  ------ Proving...
% 2.67/1.01  ------ Problem Properties 
% 2.67/1.01  
% 2.67/1.01  
% 2.67/1.01  clauses                                 21
% 2.67/1.01  conjectures                             2
% 2.67/1.01  EPR                                     8
% 2.67/1.01  Horn                                    17
% 2.67/1.01  unary                                   4
% 2.67/1.01  binary                                  8
% 2.67/1.01  lits                                    47
% 2.67/1.01  lits eq                                 4
% 2.67/1.01  fd_pure                                 0
% 2.67/1.01  fd_pseudo                               0
% 2.67/1.01  fd_cond                                 0
% 2.67/1.01  fd_pseudo_cond                          1
% 2.67/1.01  AC symbols                              0
% 2.67/1.01  
% 2.67/1.01  ------ Schedule dynamic 5 is on 
% 2.67/1.01  
% 2.67/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.67/1.01  
% 2.67/1.01  
% 2.67/1.01  ------ 
% 2.67/1.01  Current options:
% 2.67/1.01  ------ 
% 2.67/1.01  
% 2.67/1.01  ------ Input Options
% 2.67/1.01  
% 2.67/1.01  --out_options                           all
% 2.67/1.01  --tptp_safe_out                         true
% 2.67/1.01  --problem_path                          ""
% 2.67/1.01  --include_path                          ""
% 2.67/1.01  --clausifier                            res/vclausify_rel
% 2.67/1.01  --clausifier_options                    --mode clausify
% 2.67/1.01  --stdin                                 false
% 2.67/1.01  --stats_out                             all
% 2.67/1.01  
% 2.67/1.01  ------ General Options
% 2.67/1.01  
% 2.67/1.01  --fof                                   false
% 2.67/1.01  --time_out_real                         305.
% 2.67/1.01  --time_out_virtual                      -1.
% 2.67/1.01  --symbol_type_check                     false
% 2.67/1.01  --clausify_out                          false
% 2.67/1.01  --sig_cnt_out                           false
% 2.67/1.01  --trig_cnt_out                          false
% 2.67/1.01  --trig_cnt_out_tolerance                1.
% 2.67/1.01  --trig_cnt_out_sk_spl                   false
% 2.67/1.01  --abstr_cl_out                          false
% 2.67/1.01  
% 2.67/1.01  ------ Global Options
% 2.67/1.01  
% 2.67/1.01  --schedule                              default
% 2.67/1.01  --add_important_lit                     false
% 2.67/1.01  --prop_solver_per_cl                    1000
% 2.67/1.01  --min_unsat_core                        false
% 2.67/1.01  --soft_assumptions                      false
% 2.67/1.01  --soft_lemma_size                       3
% 2.67/1.01  --prop_impl_unit_size                   0
% 2.67/1.01  --prop_impl_unit                        []
% 2.67/1.01  --share_sel_clauses                     true
% 2.67/1.01  --reset_solvers                         false
% 2.67/1.01  --bc_imp_inh                            [conj_cone]
% 2.67/1.01  --conj_cone_tolerance                   3.
% 2.67/1.01  --extra_neg_conj                        none
% 2.67/1.01  --large_theory_mode                     true
% 2.67/1.01  --prolific_symb_bound                   200
% 2.67/1.01  --lt_threshold                          2000
% 2.67/1.01  --clause_weak_htbl                      true
% 2.67/1.01  --gc_record_bc_elim                     false
% 2.67/1.01  
% 2.67/1.01  ------ Preprocessing Options
% 2.67/1.01  
% 2.67/1.01  --preprocessing_flag                    true
% 2.67/1.01  --time_out_prep_mult                    0.1
% 2.67/1.01  --splitting_mode                        input
% 2.67/1.01  --splitting_grd                         true
% 2.67/1.01  --splitting_cvd                         false
% 2.67/1.01  --splitting_cvd_svl                     false
% 2.67/1.01  --splitting_nvd                         32
% 2.67/1.01  --sub_typing                            true
% 2.67/1.01  --prep_gs_sim                           true
% 2.67/1.01  --prep_unflatten                        true
% 2.67/1.01  --prep_res_sim                          true
% 2.67/1.01  --prep_upred                            true
% 2.67/1.01  --prep_sem_filter                       exhaustive
% 2.67/1.01  --prep_sem_filter_out                   false
% 2.67/1.01  --pred_elim                             true
% 2.67/1.01  --res_sim_input                         true
% 2.67/1.01  --eq_ax_congr_red                       true
% 2.67/1.01  --pure_diseq_elim                       true
% 2.67/1.01  --brand_transform                       false
% 2.67/1.01  --non_eq_to_eq                          false
% 2.67/1.01  --prep_def_merge                        true
% 2.67/1.01  --prep_def_merge_prop_impl              false
% 2.67/1.01  --prep_def_merge_mbd                    true
% 2.67/1.01  --prep_def_merge_tr_red                 false
% 2.67/1.01  --prep_def_merge_tr_cl                  false
% 2.67/1.01  --smt_preprocessing                     true
% 2.67/1.01  --smt_ac_axioms                         fast
% 2.67/1.01  --preprocessed_out                      false
% 2.67/1.01  --preprocessed_stats                    false
% 2.67/1.01  
% 2.67/1.01  ------ Abstraction refinement Options
% 2.67/1.01  
% 2.67/1.01  --abstr_ref                             []
% 2.67/1.01  --abstr_ref_prep                        false
% 2.67/1.01  --abstr_ref_until_sat                   false
% 2.67/1.01  --abstr_ref_sig_restrict                funpre
% 2.67/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.67/1.01  --abstr_ref_under                       []
% 2.67/1.01  
% 2.67/1.01  ------ SAT Options
% 2.67/1.01  
% 2.67/1.01  --sat_mode                              false
% 2.67/1.01  --sat_fm_restart_options                ""
% 2.67/1.01  --sat_gr_def                            false
% 2.67/1.01  --sat_epr_types                         true
% 2.67/1.01  --sat_non_cyclic_types                  false
% 2.67/1.01  --sat_finite_models                     false
% 2.67/1.01  --sat_fm_lemmas                         false
% 2.67/1.01  --sat_fm_prep                           false
% 2.67/1.01  --sat_fm_uc_incr                        true
% 2.67/1.01  --sat_out_model                         small
% 2.67/1.01  --sat_out_clauses                       false
% 2.67/1.01  
% 2.67/1.01  ------ QBF Options
% 2.67/1.01  
% 2.67/1.01  --qbf_mode                              false
% 2.67/1.01  --qbf_elim_univ                         false
% 2.67/1.01  --qbf_dom_inst                          none
% 2.67/1.01  --qbf_dom_pre_inst                      false
% 2.67/1.01  --qbf_sk_in                             false
% 2.67/1.01  --qbf_pred_elim                         true
% 2.67/1.01  --qbf_split                             512
% 2.67/1.01  
% 2.67/1.01  ------ BMC1 Options
% 2.67/1.01  
% 2.67/1.01  --bmc1_incremental                      false
% 2.67/1.01  --bmc1_axioms                           reachable_all
% 2.67/1.01  --bmc1_min_bound                        0
% 2.67/1.01  --bmc1_max_bound                        -1
% 2.67/1.01  --bmc1_max_bound_default                -1
% 2.67/1.01  --bmc1_symbol_reachability              true
% 2.67/1.01  --bmc1_property_lemmas                  false
% 2.67/1.01  --bmc1_k_induction                      false
% 2.67/1.01  --bmc1_non_equiv_states                 false
% 2.67/1.01  --bmc1_deadlock                         false
% 2.67/1.01  --bmc1_ucm                              false
% 2.67/1.01  --bmc1_add_unsat_core                   none
% 2.67/1.01  --bmc1_unsat_core_children              false
% 2.67/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.67/1.01  --bmc1_out_stat                         full
% 2.67/1.01  --bmc1_ground_init                      false
% 2.67/1.01  --bmc1_pre_inst_next_state              false
% 2.67/1.01  --bmc1_pre_inst_state                   false
% 2.67/1.01  --bmc1_pre_inst_reach_state             false
% 2.67/1.01  --bmc1_out_unsat_core                   false
% 2.67/1.01  --bmc1_aig_witness_out                  false
% 2.67/1.01  --bmc1_verbose                          false
% 2.67/1.01  --bmc1_dump_clauses_tptp                false
% 2.67/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.67/1.01  --bmc1_dump_file                        -
% 2.67/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.67/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.67/1.01  --bmc1_ucm_extend_mode                  1
% 2.67/1.01  --bmc1_ucm_init_mode                    2
% 2.67/1.01  --bmc1_ucm_cone_mode                    none
% 2.67/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.67/1.01  --bmc1_ucm_relax_model                  4
% 2.67/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.67/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.67/1.01  --bmc1_ucm_layered_model                none
% 2.67/1.01  --bmc1_ucm_max_lemma_size               10
% 2.67/1.01  
% 2.67/1.01  ------ AIG Options
% 2.67/1.01  
% 2.67/1.01  --aig_mode                              false
% 2.67/1.01  
% 2.67/1.01  ------ Instantiation Options
% 2.67/1.01  
% 2.67/1.01  --instantiation_flag                    true
% 2.67/1.01  --inst_sos_flag                         false
% 2.67/1.01  --inst_sos_phase                        true
% 2.67/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.67/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.67/1.01  --inst_lit_sel_side                     none
% 2.67/1.01  --inst_solver_per_active                1400
% 2.67/1.01  --inst_solver_calls_frac                1.
% 2.67/1.01  --inst_passive_queue_type               priority_queues
% 2.67/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.67/1.01  --inst_passive_queues_freq              [25;2]
% 2.67/1.01  --inst_dismatching                      true
% 2.67/1.01  --inst_eager_unprocessed_to_passive     true
% 2.67/1.01  --inst_prop_sim_given                   true
% 2.67/1.01  --inst_prop_sim_new                     false
% 2.67/1.01  --inst_subs_new                         false
% 2.67/1.01  --inst_eq_res_simp                      false
% 2.67/1.01  --inst_subs_given                       false
% 2.67/1.01  --inst_orphan_elimination               true
% 2.67/1.01  --inst_learning_loop_flag               true
% 2.67/1.01  --inst_learning_start                   3000
% 2.67/1.01  --inst_learning_factor                  2
% 2.67/1.01  --inst_start_prop_sim_after_learn       3
% 2.67/1.01  --inst_sel_renew                        solver
% 2.67/1.01  --inst_lit_activity_flag                true
% 2.67/1.01  --inst_restr_to_given                   false
% 2.67/1.01  --inst_activity_threshold               500
% 2.67/1.01  --inst_out_proof                        true
% 2.67/1.01  
% 2.67/1.01  ------ Resolution Options
% 2.67/1.01  
% 2.67/1.01  --resolution_flag                       false
% 2.67/1.01  --res_lit_sel                           adaptive
% 2.67/1.01  --res_lit_sel_side                      none
% 2.67/1.01  --res_ordering                          kbo
% 2.67/1.01  --res_to_prop_solver                    active
% 2.67/1.01  --res_prop_simpl_new                    false
% 2.67/1.01  --res_prop_simpl_given                  true
% 2.67/1.01  --res_passive_queue_type                priority_queues
% 2.67/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.67/1.01  --res_passive_queues_freq               [15;5]
% 2.67/1.01  --res_forward_subs                      full
% 2.67/1.01  --res_backward_subs                     full
% 2.67/1.01  --res_forward_subs_resolution           true
% 2.67/1.01  --res_backward_subs_resolution          true
% 2.67/1.01  --res_orphan_elimination                true
% 2.67/1.01  --res_time_limit                        2.
% 2.67/1.01  --res_out_proof                         true
% 2.67/1.01  
% 2.67/1.01  ------ Superposition Options
% 2.67/1.01  
% 2.67/1.01  --superposition_flag                    true
% 2.67/1.01  --sup_passive_queue_type                priority_queues
% 2.67/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.67/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.67/1.01  --demod_completeness_check              fast
% 2.67/1.01  --demod_use_ground                      true
% 2.67/1.01  --sup_to_prop_solver                    passive
% 2.67/1.01  --sup_prop_simpl_new                    true
% 2.67/1.01  --sup_prop_simpl_given                  true
% 2.67/1.01  --sup_fun_splitting                     false
% 2.67/1.01  --sup_smt_interval                      50000
% 2.67/1.01  
% 2.67/1.01  ------ Superposition Simplification Setup
% 2.67/1.01  
% 2.67/1.01  --sup_indices_passive                   []
% 2.67/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.67/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/1.01  --sup_full_bw                           [BwDemod]
% 2.67/1.01  --sup_immed_triv                        [TrivRules]
% 2.67/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.67/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/1.01  --sup_immed_bw_main                     []
% 2.67/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.67/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/1.01  
% 2.67/1.01  ------ Combination Options
% 2.67/1.01  
% 2.67/1.01  --comb_res_mult                         3
% 2.67/1.01  --comb_sup_mult                         2
% 2.67/1.01  --comb_inst_mult                        10
% 2.67/1.01  
% 2.67/1.01  ------ Debug Options
% 2.67/1.01  
% 2.67/1.01  --dbg_backtrace                         false
% 2.67/1.01  --dbg_dump_prop_clauses                 false
% 2.67/1.01  --dbg_dump_prop_clauses_file            -
% 2.67/1.01  --dbg_out_stat                          false
% 2.67/1.01  
% 2.67/1.01  
% 2.67/1.01  
% 2.67/1.01  
% 2.67/1.01  ------ Proving...
% 2.67/1.01  
% 2.67/1.01  
% 2.67/1.01  % SZS status Theorem for theBenchmark.p
% 2.67/1.01  
% 2.67/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.67/1.01  
% 2.67/1.01  fof(f11,axiom,(
% 2.67/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,X3) & v3_pre_topc(X3,X0))) & r2_hidden(X2,X1))) => v2_tex_2(X1,X0))))),
% 2.67/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.01  
% 2.67/1.01  fof(f25,plain,(
% 2.67/1.01    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) | ? [X2] : ((! [X3] : ((k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v3_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.67/1.01    inference(ennf_transformation,[],[f11])).
% 2.67/1.01  
% 2.67/1.01  fof(f26,plain,(
% 2.67/1.01    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.67/1.01    inference(flattening,[],[f25])).
% 2.67/1.01  
% 2.67/1.01  fof(f42,plain,(
% 2.67/1.01    ! [X1,X0] : (? [X2] : (! [X3] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (! [X3] : (k6_domain_1(u1_struct_0(X0),sK2(X0,X1)) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 2.67/1.01    introduced(choice_axiom,[])).
% 2.67/1.01  
% 2.67/1.01  fof(f43,plain,(
% 2.67/1.01    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | (! [X3] : (k6_domain_1(u1_struct_0(X0),sK2(X0,X1)) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.67/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f42])).
% 2.67/1.01  
% 2.67/1.01  fof(f69,plain,(
% 2.67/1.01    ( ! [X0,X1] : (v2_tex_2(X1,X0) | m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.67/1.01    inference(cnf_transformation,[],[f43])).
% 2.67/1.01  
% 2.67/1.01  fof(f12,conjecture,(
% 2.67/1.01    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))) => v2_tex_2(X1,X0))))),
% 2.67/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.01  
% 2.67/1.01  fof(f13,negated_conjecture,(
% 2.67/1.01    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))) => v2_tex_2(X1,X0))))),
% 2.67/1.01    inference(negated_conjecture,[],[f12])).
% 2.67/1.01  
% 2.67/1.01  fof(f27,plain,(
% 2.67/1.01    ? [X0] : (? [X1] : ((~v2_tex_2(X1,X0) & ! [X2] : ((k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.67/1.01    inference(ennf_transformation,[],[f13])).
% 2.67/1.01  
% 2.67/1.01  fof(f28,plain,(
% 2.67/1.01    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & ! [X2] : (k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.67/1.01    inference(flattening,[],[f27])).
% 2.67/1.01  
% 2.67/1.01  fof(f45,plain,(
% 2.67/1.01    ( ! [X0] : (? [X1] : (~v2_tex_2(X1,X0) & ! [X2] : (k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v2_tex_2(sK4,X0) & ! [X2] : (k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),sK4,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_hidden(X2,sK4) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.67/1.01    introduced(choice_axiom,[])).
% 2.67/1.01  
% 2.67/1.01  fof(f44,plain,(
% 2.67/1.01    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & ! [X2] : (k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v2_tex_2(X1,sK3) & ! [X2] : (k6_domain_1(u1_struct_0(sK3),X2) = k9_subset_1(u1_struct_0(sK3),X1,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X2))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(sK3))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK3) & v3_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 2.67/1.01    introduced(choice_axiom,[])).
% 2.67/1.01  
% 2.67/1.01  fof(f46,plain,(
% 2.67/1.01    (~v2_tex_2(sK4,sK3) & ! [X2] : (k6_domain_1(u1_struct_0(sK3),X2) = k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X2))) | ~r2_hidden(X2,sK4) | ~m1_subset_1(X2,u1_struct_0(sK3))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK3) & v3_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 2.67/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f28,f45,f44])).
% 2.67/1.01  
% 2.67/1.01  fof(f78,plain,(
% 2.67/1.01    ~v2_tex_2(sK4,sK3)),
% 2.67/1.01    inference(cnf_transformation,[],[f46])).
% 2.67/1.01  
% 2.67/1.01  fof(f72,plain,(
% 2.67/1.01    ~v2_struct_0(sK3)),
% 2.67/1.01    inference(cnf_transformation,[],[f46])).
% 2.67/1.01  
% 2.67/1.01  fof(f73,plain,(
% 2.67/1.01    v2_pre_topc(sK3)),
% 2.67/1.01    inference(cnf_transformation,[],[f46])).
% 2.67/1.01  
% 2.67/1.01  fof(f75,plain,(
% 2.67/1.01    l1_pre_topc(sK3)),
% 2.67/1.01    inference(cnf_transformation,[],[f46])).
% 2.67/1.01  
% 2.67/1.01  fof(f76,plain,(
% 2.67/1.01    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 2.67/1.01    inference(cnf_transformation,[],[f46])).
% 2.67/1.01  
% 2.67/1.01  fof(f8,axiom,(
% 2.67/1.01    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 2.67/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.01  
% 2.67/1.01  fof(f19,plain,(
% 2.67/1.01    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.67/1.01    inference(ennf_transformation,[],[f8])).
% 2.67/1.01  
% 2.67/1.01  fof(f20,plain,(
% 2.67/1.01    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.67/1.01    inference(flattening,[],[f19])).
% 2.67/1.01  
% 2.67/1.01  fof(f63,plain,(
% 2.67/1.01    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.67/1.01    inference(cnf_transformation,[],[f20])).
% 2.67/1.01  
% 2.67/1.01  fof(f70,plain,(
% 2.67/1.01    ( ! [X0,X1] : (v2_tex_2(X1,X0) | r2_hidden(sK2(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.67/1.01    inference(cnf_transformation,[],[f43])).
% 2.67/1.01  
% 2.67/1.01  fof(f5,axiom,(
% 2.67/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.67/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.01  
% 2.67/1.01  fof(f37,plain,(
% 2.67/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.67/1.01    inference(nnf_transformation,[],[f5])).
% 2.67/1.01  
% 2.67/1.01  fof(f59,plain,(
% 2.67/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.67/1.01    inference(cnf_transformation,[],[f37])).
% 2.67/1.01  
% 2.67/1.01  fof(f6,axiom,(
% 2.67/1.01    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.67/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.01  
% 2.67/1.01  fof(f16,plain,(
% 2.67/1.01    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.67/1.01    inference(ennf_transformation,[],[f6])).
% 2.67/1.01  
% 2.67/1.01  fof(f61,plain,(
% 2.67/1.01    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.67/1.01    inference(cnf_transformation,[],[f16])).
% 2.67/1.01  
% 2.67/1.01  fof(f60,plain,(
% 2.67/1.01    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.67/1.01    inference(cnf_transformation,[],[f37])).
% 2.67/1.01  
% 2.67/1.01  fof(f77,plain,(
% 2.67/1.01    ( ! [X2] : (k6_domain_1(u1_struct_0(sK3),X2) = k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X2))) | ~r2_hidden(X2,sK4) | ~m1_subset_1(X2,u1_struct_0(sK3))) )),
% 2.67/1.01    inference(cnf_transformation,[],[f46])).
% 2.67/1.01  
% 2.67/1.01  fof(f71,plain,(
% 2.67/1.01    ( ! [X0,X3,X1] : (v2_tex_2(X1,X0) | k6_domain_1(u1_struct_0(X0),sK2(X0,X1)) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.67/1.01    inference(cnf_transformation,[],[f43])).
% 2.67/1.01  
% 2.67/1.01  fof(f9,axiom,(
% 2.67/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 2.67/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.01  
% 2.67/1.01  fof(f21,plain,(
% 2.67/1.01    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.67/1.01    inference(ennf_transformation,[],[f9])).
% 2.67/1.01  
% 2.67/1.01  fof(f22,plain,(
% 2.67/1.01    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.67/1.01    inference(flattening,[],[f21])).
% 2.67/1.01  
% 2.67/1.01  fof(f64,plain,(
% 2.67/1.01    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.67/1.01    inference(cnf_transformation,[],[f22])).
% 2.67/1.01  
% 2.67/1.01  fof(f10,axiom,(
% 2.67/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_pre_topc(X1,X0)))))),
% 2.67/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.01  
% 2.67/1.01  fof(f23,plain,(
% 2.67/1.01    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.67/1.01    inference(ennf_transformation,[],[f10])).
% 2.67/1.01  
% 2.67/1.01  fof(f24,plain,(
% 2.67/1.01    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.67/1.01    inference(flattening,[],[f23])).
% 2.67/1.01  
% 2.67/1.01  fof(f38,plain,(
% 2.67/1.01    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.67/1.01    inference(nnf_transformation,[],[f24])).
% 2.67/1.01  
% 2.67/1.01  fof(f39,plain,(
% 2.67/1.01    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.67/1.01    inference(rectify,[],[f38])).
% 2.67/1.01  
% 2.67/1.01  fof(f40,plain,(
% 2.67/1.01    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK1(X0),X0) & v4_pre_topc(sK1(X0),X0) & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.67/1.01    introduced(choice_axiom,[])).
% 2.67/1.01  
% 2.67/1.01  fof(f41,plain,(
% 2.67/1.01    ! [X0] : (((v3_tdlat_3(X0) | (~v3_pre_topc(sK1(X0),X0) & v4_pre_topc(sK1(X0),X0) & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.67/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).
% 2.67/1.01  
% 2.67/1.01  fof(f65,plain,(
% 2.67/1.01    ( ! [X2,X0] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.67/1.01    inference(cnf_transformation,[],[f41])).
% 2.67/1.01  
% 2.67/1.01  fof(f7,axiom,(
% 2.67/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.67/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.01  
% 2.67/1.01  fof(f17,plain,(
% 2.67/1.01    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.67/1.01    inference(ennf_transformation,[],[f7])).
% 2.67/1.01  
% 2.67/1.01  fof(f18,plain,(
% 2.67/1.01    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.67/1.01    inference(flattening,[],[f17])).
% 2.67/1.01  
% 2.67/1.01  fof(f62,plain,(
% 2.67/1.01    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.67/1.01    inference(cnf_transformation,[],[f18])).
% 2.67/1.01  
% 2.67/1.01  fof(f74,plain,(
% 2.67/1.01    v3_tdlat_3(sK3)),
% 2.67/1.01    inference(cnf_transformation,[],[f46])).
% 2.67/1.01  
% 2.67/1.01  fof(f3,axiom,(
% 2.67/1.01    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.67/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.01  
% 2.67/1.01  fof(f35,plain,(
% 2.67/1.01    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 2.67/1.01    inference(nnf_transformation,[],[f3])).
% 2.67/1.01  
% 2.67/1.01  fof(f54,plain,(
% 2.67/1.01    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.67/1.01    inference(cnf_transformation,[],[f35])).
% 2.67/1.01  
% 2.67/1.01  fof(f4,axiom,(
% 2.67/1.01    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.67/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.01  
% 2.67/1.01  fof(f15,plain,(
% 2.67/1.01    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.67/1.01    inference(ennf_transformation,[],[f4])).
% 2.67/1.01  
% 2.67/1.01  fof(f36,plain,(
% 2.67/1.01    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 2.67/1.01    inference(nnf_transformation,[],[f15])).
% 2.67/1.01  
% 2.67/1.01  fof(f55,plain,(
% 2.67/1.01    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.67/1.01    inference(cnf_transformation,[],[f36])).
% 2.67/1.01  
% 2.67/1.01  cnf(c_24,plain,
% 2.67/1.01      ( v2_tex_2(X0,X1)
% 2.67/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.67/1.01      | m1_subset_1(sK2(X1,X0),u1_struct_0(X1))
% 2.67/1.01      | v2_struct_0(X1)
% 2.67/1.01      | ~ v2_pre_topc(X1)
% 2.67/1.01      | ~ l1_pre_topc(X1) ),
% 2.67/1.01      inference(cnf_transformation,[],[f69]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_25,negated_conjecture,
% 2.67/1.01      ( ~ v2_tex_2(sK4,sK3) ),
% 2.67/1.01      inference(cnf_transformation,[],[f78]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_447,plain,
% 2.67/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.67/1.01      | m1_subset_1(sK2(X1,X0),u1_struct_0(X1))
% 2.67/1.01      | v2_struct_0(X1)
% 2.67/1.01      | ~ v2_pre_topc(X1)
% 2.67/1.01      | ~ l1_pre_topc(X1)
% 2.67/1.01      | sK3 != X1
% 2.67/1.01      | sK4 != X0 ),
% 2.67/1.01      inference(resolution_lifted,[status(thm)],[c_24,c_25]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_448,plain,
% 2.67/1.01      ( m1_subset_1(sK2(sK3,sK4),u1_struct_0(sK3))
% 2.67/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.67/1.01      | v2_struct_0(sK3)
% 2.67/1.01      | ~ v2_pre_topc(sK3)
% 2.67/1.01      | ~ l1_pre_topc(sK3) ),
% 2.67/1.01      inference(unflattening,[status(thm)],[c_447]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_31,negated_conjecture,
% 2.67/1.01      ( ~ v2_struct_0(sK3) ),
% 2.67/1.01      inference(cnf_transformation,[],[f72]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_30,negated_conjecture,
% 2.67/1.01      ( v2_pre_topc(sK3) ),
% 2.67/1.01      inference(cnf_transformation,[],[f73]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_28,negated_conjecture,
% 2.67/1.01      ( l1_pre_topc(sK3) ),
% 2.67/1.01      inference(cnf_transformation,[],[f75]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_27,negated_conjecture,
% 2.67/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.67/1.01      inference(cnf_transformation,[],[f76]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_450,plain,
% 2.67/1.01      ( m1_subset_1(sK2(sK3,sK4),u1_struct_0(sK3)) ),
% 2.67/1.01      inference(global_propositional_subsumption,
% 2.67/1.01                [status(thm)],
% 2.67/1.01                [c_448,c_31,c_30,c_28,c_27]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1247,plain,
% 2.67/1.01      ( m1_subset_1(sK2(sK3,sK4),u1_struct_0(sK3)) = iProver_top ),
% 2.67/1.01      inference(predicate_to_equality,[status(thm)],[c_450]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_16,plain,
% 2.67/1.01      ( ~ m1_subset_1(X0,X1)
% 2.67/1.01      | v1_xboole_0(X1)
% 2.67/1.01      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 2.67/1.01      inference(cnf_transformation,[],[f63]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1251,plain,
% 2.67/1.01      ( k6_domain_1(X0,X1) = k1_tarski(X1)
% 2.67/1.01      | m1_subset_1(X1,X0) != iProver_top
% 2.67/1.01      | v1_xboole_0(X0) = iProver_top ),
% 2.67/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_3133,plain,
% 2.67/1.01      ( k6_domain_1(u1_struct_0(sK3),sK2(sK3,sK4)) = k1_tarski(sK2(sK3,sK4))
% 2.67/1.01      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 2.67/1.01      inference(superposition,[status(thm)],[c_1247,c_1251]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_23,plain,
% 2.67/1.01      ( v2_tex_2(X0,X1)
% 2.67/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.67/1.01      | r2_hidden(sK2(X1,X0),X0)
% 2.67/1.01      | v2_struct_0(X1)
% 2.67/1.01      | ~ v2_pre_topc(X1)
% 2.67/1.01      | ~ l1_pre_topc(X1) ),
% 2.67/1.01      inference(cnf_transformation,[],[f70]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_458,plain,
% 2.67/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.67/1.01      | r2_hidden(sK2(X1,X0),X0)
% 2.67/1.01      | v2_struct_0(X1)
% 2.67/1.01      | ~ v2_pre_topc(X1)
% 2.67/1.01      | ~ l1_pre_topc(X1)
% 2.67/1.01      | sK3 != X1
% 2.67/1.01      | sK4 != X0 ),
% 2.67/1.01      inference(resolution_lifted,[status(thm)],[c_23,c_25]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_459,plain,
% 2.67/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.67/1.01      | r2_hidden(sK2(sK3,sK4),sK4)
% 2.67/1.01      | v2_struct_0(sK3)
% 2.67/1.01      | ~ v2_pre_topc(sK3)
% 2.67/1.01      | ~ l1_pre_topc(sK3) ),
% 2.67/1.01      inference(unflattening,[status(thm)],[c_458]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1471,plain,
% 2.67/1.01      ( ~ m1_subset_1(sK2(sK3,sK4),u1_struct_0(sK3))
% 2.67/1.01      | v1_xboole_0(u1_struct_0(sK3))
% 2.67/1.01      | k6_domain_1(u1_struct_0(sK3),sK2(sK3,sK4)) = k1_tarski(sK2(sK3,sK4)) ),
% 2.67/1.01      inference(instantiation,[status(thm)],[c_16]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1249,plain,
% 2.67/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.67/1.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_13,plain,
% 2.67/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.67/1.01      inference(cnf_transformation,[],[f59]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1252,plain,
% 2.67/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.67/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 2.67/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1749,plain,
% 2.67/1.01      ( r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
% 2.67/1.01      inference(superposition,[status(thm)],[c_1249,c_1252]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1757,plain,
% 2.67/1.01      ( r1_tarski(sK4,u1_struct_0(sK3)) ),
% 2.67/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_1749]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_14,plain,
% 2.67/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.67/1.01      | ~ r2_hidden(X2,X0)
% 2.67/1.01      | ~ v1_xboole_0(X1) ),
% 2.67/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_12,plain,
% 2.67/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.67/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_239,plain,
% 2.67/1.01      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.67/1.01      inference(prop_impl,[status(thm)],[c_12]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_240,plain,
% 2.67/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.67/1.01      inference(renaming,[status(thm)],[c_239]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_299,plain,
% 2.67/1.01      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 2.67/1.01      inference(bin_hyper_res,[status(thm)],[c_14,c_240]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1536,plain,
% 2.67/1.01      ( ~ r2_hidden(X0,X1)
% 2.67/1.01      | ~ r1_tarski(X1,u1_struct_0(sK3))
% 2.67/1.01      | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 2.67/1.01      inference(instantiation,[status(thm)],[c_299]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1769,plain,
% 2.67/1.01      ( ~ r2_hidden(sK2(sK3,sK4),sK4)
% 2.67/1.01      | ~ r1_tarski(sK4,u1_struct_0(sK3))
% 2.67/1.01      | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 2.67/1.01      inference(instantiation,[status(thm)],[c_1536]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_3478,plain,
% 2.67/1.01      ( k6_domain_1(u1_struct_0(sK3),sK2(sK3,sK4)) = k1_tarski(sK2(sK3,sK4)) ),
% 2.67/1.01      inference(global_propositional_subsumption,
% 2.67/1.01                [status(thm)],
% 2.67/1.01                [c_3133,c_31,c_30,c_28,c_27,c_448,c_459,c_1471,c_1757,
% 2.67/1.01                 c_1769]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1253,plain,
% 2.67/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.67/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 2.67/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_26,negated_conjecture,
% 2.67/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.67/1.01      | ~ r2_hidden(X0,sK4)
% 2.67/1.01      | k6_domain_1(u1_struct_0(sK3),X0) = k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X0))) ),
% 2.67/1.01      inference(cnf_transformation,[],[f77]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1250,plain,
% 2.67/1.01      ( k6_domain_1(u1_struct_0(sK3),X0) = k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X0)))
% 2.67/1.01      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 2.67/1.01      | r2_hidden(X0,sK4) != iProver_top ),
% 2.67/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1458,plain,
% 2.67/1.01      ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK2(sK3,sK4)))) = k6_domain_1(u1_struct_0(sK3),sK2(sK3,sK4))
% 2.67/1.01      | r2_hidden(sK2(sK3,sK4),sK4) != iProver_top ),
% 2.67/1.01      inference(superposition,[status(thm)],[c_1247,c_1250]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_32,plain,
% 2.67/1.01      ( v2_struct_0(sK3) != iProver_top ),
% 2.67/1.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_33,plain,
% 2.67/1.01      ( v2_pre_topc(sK3) = iProver_top ),
% 2.67/1.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_35,plain,
% 2.67/1.01      ( l1_pre_topc(sK3) = iProver_top ),
% 2.67/1.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_36,plain,
% 2.67/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.67/1.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_460,plain,
% 2.67/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.67/1.01      | r2_hidden(sK2(sK3,sK4),sK4) = iProver_top
% 2.67/1.01      | v2_struct_0(sK3) = iProver_top
% 2.67/1.01      | v2_pre_topc(sK3) != iProver_top
% 2.67/1.01      | l1_pre_topc(sK3) != iProver_top ),
% 2.67/1.01      inference(predicate_to_equality,[status(thm)],[c_459]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1509,plain,
% 2.67/1.01      ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK2(sK3,sK4)))) = k6_domain_1(u1_struct_0(sK3),sK2(sK3,sK4)) ),
% 2.67/1.01      inference(global_propositional_subsumption,
% 2.67/1.01                [status(thm)],
% 2.67/1.01                [c_1458,c_32,c_33,c_35,c_36,c_460]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_22,plain,
% 2.67/1.01      ( v2_tex_2(X0,X1)
% 2.67/1.01      | ~ v3_pre_topc(X2,X1)
% 2.67/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.67/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.67/1.01      | v2_struct_0(X1)
% 2.67/1.01      | ~ v2_pre_topc(X1)
% 2.67/1.01      | ~ l1_pre_topc(X1)
% 2.67/1.01      | k6_domain_1(u1_struct_0(X1),sK2(X1,X0)) != k9_subset_1(u1_struct_0(X1),X0,X2) ),
% 2.67/1.01      inference(cnf_transformation,[],[f71]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_469,plain,
% 2.67/1.01      ( ~ v3_pre_topc(X0,X1)
% 2.67/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.67/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.67/1.01      | v2_struct_0(X1)
% 2.67/1.01      | ~ v2_pre_topc(X1)
% 2.67/1.01      | ~ l1_pre_topc(X1)
% 2.67/1.01      | k6_domain_1(u1_struct_0(X1),sK2(X1,X2)) != k9_subset_1(u1_struct_0(X1),X2,X0)
% 2.67/1.01      | sK3 != X1
% 2.67/1.01      | sK4 != X2 ),
% 2.67/1.01      inference(resolution_lifted,[status(thm)],[c_22,c_25]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_470,plain,
% 2.67/1.01      ( ~ v3_pre_topc(X0,sK3)
% 2.67/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.67/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.67/1.01      | v2_struct_0(sK3)
% 2.67/1.01      | ~ v2_pre_topc(sK3)
% 2.67/1.01      | ~ l1_pre_topc(sK3)
% 2.67/1.01      | k6_domain_1(u1_struct_0(sK3),sK2(sK3,sK4)) != k9_subset_1(u1_struct_0(sK3),sK4,X0) ),
% 2.67/1.01      inference(unflattening,[status(thm)],[c_469]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_474,plain,
% 2.67/1.01      ( ~ v3_pre_topc(X0,sK3)
% 2.67/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.67/1.01      | k6_domain_1(u1_struct_0(sK3),sK2(sK3,sK4)) != k9_subset_1(u1_struct_0(sK3),sK4,X0) ),
% 2.67/1.01      inference(global_propositional_subsumption,
% 2.67/1.01                [status(thm)],
% 2.67/1.01                [c_470,c_31,c_30,c_28,c_27]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_17,plain,
% 2.67/1.01      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
% 2.67/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.67/1.01      | ~ v2_pre_topc(X0)
% 2.67/1.01      | ~ l1_pre_topc(X0) ),
% 2.67/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_21,plain,
% 2.67/1.01      ( v3_pre_topc(X0,X1)
% 2.67/1.01      | ~ v4_pre_topc(X0,X1)
% 2.67/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.67/1.01      | ~ v3_tdlat_3(X1)
% 2.67/1.01      | ~ v2_pre_topc(X1)
% 2.67/1.01      | ~ l1_pre_topc(X1) ),
% 2.67/1.01      inference(cnf_transformation,[],[f65]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_413,plain,
% 2.67/1.01      ( v3_pre_topc(X0,X1)
% 2.67/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.67/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.67/1.01      | ~ v3_tdlat_3(X1)
% 2.67/1.01      | ~ v2_pre_topc(X3)
% 2.67/1.01      | ~ v2_pre_topc(X1)
% 2.67/1.01      | ~ l1_pre_topc(X3)
% 2.67/1.01      | ~ l1_pre_topc(X1)
% 2.67/1.01      | X1 != X3
% 2.67/1.01      | k2_pre_topc(X3,X2) != X0 ),
% 2.67/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_21]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_414,plain,
% 2.67/1.01      ( v3_pre_topc(k2_pre_topc(X0,X1),X0)
% 2.67/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.67/1.01      | ~ m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 2.67/1.01      | ~ v3_tdlat_3(X0)
% 2.67/1.01      | ~ v2_pre_topc(X0)
% 2.67/1.01      | ~ l1_pre_topc(X0) ),
% 2.67/1.01      inference(unflattening,[status(thm)],[c_413]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_15,plain,
% 2.67/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.67/1.01      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.67/1.01      | ~ l1_pre_topc(X1) ),
% 2.67/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_430,plain,
% 2.67/1.01      ( v3_pre_topc(k2_pre_topc(X0,X1),X0)
% 2.67/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.67/1.01      | ~ v3_tdlat_3(X0)
% 2.67/1.01      | ~ v2_pre_topc(X0)
% 2.67/1.01      | ~ l1_pre_topc(X0) ),
% 2.67/1.01      inference(forward_subsumption_resolution,
% 2.67/1.01                [status(thm)],
% 2.67/1.01                [c_414,c_15]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_498,plain,
% 2.67/1.01      ( v3_pre_topc(k2_pre_topc(X0,X1),X0)
% 2.67/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.67/1.01      | ~ v3_tdlat_3(X0)
% 2.67/1.01      | ~ l1_pre_topc(X0)
% 2.67/1.01      | sK3 != X0 ),
% 2.67/1.01      inference(resolution_lifted,[status(thm)],[c_430,c_30]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_499,plain,
% 2.67/1.01      ( v3_pre_topc(k2_pre_topc(sK3,X0),sK3)
% 2.67/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.67/1.01      | ~ v3_tdlat_3(sK3)
% 2.67/1.01      | ~ l1_pre_topc(sK3) ),
% 2.67/1.01      inference(unflattening,[status(thm)],[c_498]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_29,negated_conjecture,
% 2.67/1.01      ( v3_tdlat_3(sK3) ),
% 2.67/1.01      inference(cnf_transformation,[],[f74]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_503,plain,
% 2.67/1.01      ( v3_pre_topc(k2_pre_topc(sK3,X0),sK3)
% 2.67/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.67/1.01      inference(global_propositional_subsumption,
% 2.67/1.01                [status(thm)],
% 2.67/1.01                [c_499,c_29,c_28]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_538,plain,
% 2.67/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.67/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.67/1.01      | k6_domain_1(u1_struct_0(sK3),sK2(sK3,sK4)) != k9_subset_1(u1_struct_0(sK3),sK4,X0)
% 2.67/1.01      | k2_pre_topc(sK3,X1) != X0
% 2.67/1.01      | sK3 != sK3 ),
% 2.67/1.01      inference(resolution_lifted,[status(thm)],[c_474,c_503]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_539,plain,
% 2.67/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.67/1.01      | ~ m1_subset_1(k2_pre_topc(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.67/1.01      | k6_domain_1(u1_struct_0(sK3),sK2(sK3,sK4)) != k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X0)) ),
% 2.67/1.01      inference(unflattening,[status(thm)],[c_538]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_523,plain,
% 2.67/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.67/1.01      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.67/1.01      | sK3 != X1 ),
% 2.67/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_28]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_524,plain,
% 2.67/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.67/1.01      | m1_subset_1(k2_pre_topc(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.67/1.01      inference(unflattening,[status(thm)],[c_523]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_543,plain,
% 2.67/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.67/1.01      | k6_domain_1(u1_struct_0(sK3),sK2(sK3,sK4)) != k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X0)) ),
% 2.67/1.01      inference(global_propositional_subsumption,
% 2.67/1.01                [status(thm)],
% 2.67/1.01                [c_539,c_524]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1244,plain,
% 2.67/1.01      ( k6_domain_1(u1_struct_0(sK3),sK2(sK3,sK4)) != k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X0))
% 2.67/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.67/1.01      inference(predicate_to_equality,[status(thm)],[c_543]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1547,plain,
% 2.67/1.01      ( m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK2(sK3,sK4)),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.67/1.01      inference(superposition,[status(thm)],[c_1509,c_1244]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1765,plain,
% 2.67/1.01      ( r1_tarski(k6_domain_1(u1_struct_0(sK3),sK2(sK3,sK4)),u1_struct_0(sK3)) != iProver_top ),
% 2.67/1.01      inference(superposition,[status(thm)],[c_1253,c_1547]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_3481,plain,
% 2.67/1.01      ( r1_tarski(k1_tarski(sK2(sK3,sK4)),u1_struct_0(sK3)) != iProver_top ),
% 2.67/1.01      inference(demodulation,[status(thm)],[c_3478,c_1765]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_6,plain,
% 2.67/1.01      ( ~ r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1) ),
% 2.67/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1728,plain,
% 2.67/1.01      ( ~ r2_hidden(sK2(sK3,sK4),X0)
% 2.67/1.01      | r1_tarski(k1_tarski(sK2(sK3,sK4)),X0) ),
% 2.67/1.01      inference(instantiation,[status(thm)],[c_6]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_2189,plain,
% 2.67/1.01      ( ~ r2_hidden(sK2(sK3,sK4),u1_struct_0(sK3))
% 2.67/1.01      | r1_tarski(k1_tarski(sK2(sK3,sK4)),u1_struct_0(sK3)) ),
% 2.67/1.01      inference(instantiation,[status(thm)],[c_1728]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_2190,plain,
% 2.67/1.01      ( r2_hidden(sK2(sK3,sK4),u1_struct_0(sK3)) != iProver_top
% 2.67/1.01      | r1_tarski(k1_tarski(sK2(sK3,sK4)),u1_struct_0(sK3)) = iProver_top ),
% 2.67/1.01      inference(predicate_to_equality,[status(thm)],[c_2189]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1770,plain,
% 2.67/1.01      ( r2_hidden(sK2(sK3,sK4),sK4) != iProver_top
% 2.67/1.01      | r1_tarski(sK4,u1_struct_0(sK3)) != iProver_top
% 2.67/1.01      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 2.67/1.01      inference(predicate_to_equality,[status(thm)],[c_1769]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_11,plain,
% 2.67/1.01      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.67/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1451,plain,
% 2.67/1.01      ( ~ m1_subset_1(sK2(sK3,sK4),u1_struct_0(sK3))
% 2.67/1.01      | r2_hidden(sK2(sK3,sK4),u1_struct_0(sK3))
% 2.67/1.01      | v1_xboole_0(u1_struct_0(sK3)) ),
% 2.67/1.01      inference(instantiation,[status(thm)],[c_11]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1452,plain,
% 2.67/1.01      ( m1_subset_1(sK2(sK3,sK4),u1_struct_0(sK3)) != iProver_top
% 2.67/1.01      | r2_hidden(sK2(sK3,sK4),u1_struct_0(sK3)) = iProver_top
% 2.67/1.01      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 2.67/1.01      inference(predicate_to_equality,[status(thm)],[c_1451]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_449,plain,
% 2.67/1.01      ( m1_subset_1(sK2(sK3,sK4),u1_struct_0(sK3)) = iProver_top
% 2.67/1.01      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.67/1.01      | v2_struct_0(sK3) = iProver_top
% 2.67/1.01      | v2_pre_topc(sK3) != iProver_top
% 2.67/1.01      | l1_pre_topc(sK3) != iProver_top ),
% 2.67/1.01      inference(predicate_to_equality,[status(thm)],[c_448]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(contradiction,plain,
% 2.67/1.01      ( $false ),
% 2.67/1.01      inference(minisat,
% 2.67/1.01                [status(thm)],
% 2.67/1.01                [c_3481,c_2190,c_1770,c_1749,c_1452,c_460,c_449,c_36,
% 2.67/1.01                 c_35,c_33,c_32]) ).
% 2.67/1.01  
% 2.67/1.01  
% 2.67/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.67/1.01  
% 2.67/1.01  ------                               Statistics
% 2.67/1.01  
% 2.67/1.01  ------ General
% 2.67/1.01  
% 2.67/1.01  abstr_ref_over_cycles:                  0
% 2.67/1.01  abstr_ref_under_cycles:                 0
% 2.67/1.01  gc_basic_clause_elim:                   0
% 2.67/1.01  forced_gc_time:                         0
% 2.67/1.01  parsing_time:                           0.012
% 2.67/1.01  unif_index_cands_time:                  0.
% 2.67/1.01  unif_index_add_time:                    0.
% 2.67/1.01  orderings_time:                         0.
% 2.67/1.01  out_proof_time:                         0.009
% 2.67/1.01  total_time:                             0.165
% 2.67/1.01  num_of_symbols:                         53
% 2.67/1.01  num_of_terms:                           2726
% 2.67/1.01  
% 2.67/1.01  ------ Preprocessing
% 2.67/1.01  
% 2.67/1.01  num_of_splits:                          0
% 2.67/1.01  num_of_split_atoms:                     0
% 2.67/1.01  num_of_reused_defs:                     0
% 2.67/1.01  num_eq_ax_congr_red:                    20
% 2.67/1.01  num_of_sem_filtered_clauses:            1
% 2.67/1.01  num_of_subtypes:                        0
% 2.67/1.01  monotx_restored_types:                  0
% 2.67/1.01  sat_num_of_epr_types:                   0
% 2.67/1.01  sat_num_of_non_cyclic_types:            0
% 2.67/1.01  sat_guarded_non_collapsed_types:        0
% 2.67/1.01  num_pure_diseq_elim:                    0
% 2.67/1.01  simp_replaced_by:                       0
% 2.67/1.01  res_preprocessed:                       117
% 2.67/1.01  prep_upred:                             0
% 2.67/1.01  prep_unflattend:                        15
% 2.67/1.01  smt_new_axioms:                         0
% 2.67/1.01  pred_elim_cands:                        4
% 2.67/1.01  pred_elim:                              7
% 2.67/1.01  pred_elim_cl:                           10
% 2.67/1.01  pred_elim_cycles:                       9
% 2.67/1.01  merged_defs:                            16
% 2.67/1.01  merged_defs_ncl:                        0
% 2.67/1.01  bin_hyper_res:                          17
% 2.67/1.01  prep_cycles:                            4
% 2.67/1.01  pred_elim_time:                         0.019
% 2.67/1.01  splitting_time:                         0.
% 2.67/1.01  sem_filter_time:                        0.
% 2.67/1.01  monotx_time:                            0.001
% 2.67/1.01  subtype_inf_time:                       0.
% 2.67/1.01  
% 2.67/1.01  ------ Problem properties
% 2.67/1.01  
% 2.67/1.01  clauses:                                21
% 2.67/1.01  conjectures:                            2
% 2.67/1.01  epr:                                    8
% 2.67/1.01  horn:                                   17
% 2.67/1.01  ground:                                 3
% 2.67/1.01  unary:                                  4
% 2.67/1.01  binary:                                 8
% 2.67/1.01  lits:                                   47
% 2.67/1.01  lits_eq:                                4
% 2.67/1.01  fd_pure:                                0
% 2.67/1.01  fd_pseudo:                              0
% 2.67/1.01  fd_cond:                                0
% 2.67/1.01  fd_pseudo_cond:                         1
% 2.67/1.01  ac_symbols:                             0
% 2.67/1.01  
% 2.67/1.01  ------ Propositional Solver
% 2.67/1.01  
% 2.67/1.01  prop_solver_calls:                      27
% 2.67/1.01  prop_fast_solver_calls:                 733
% 2.67/1.01  smt_solver_calls:                       0
% 2.67/1.01  smt_fast_solver_calls:                  0
% 2.67/1.01  prop_num_of_clauses:                    1203
% 2.67/1.01  prop_preprocess_simplified:             4896
% 2.67/1.01  prop_fo_subsumed:                       25
% 2.67/1.01  prop_solver_time:                       0.
% 2.67/1.01  smt_solver_time:                        0.
% 2.67/1.01  smt_fast_solver_time:                   0.
% 2.67/1.01  prop_fast_solver_time:                  0.
% 2.67/1.01  prop_unsat_core_time:                   0.
% 2.67/1.01  
% 2.67/1.01  ------ QBF
% 2.67/1.01  
% 2.67/1.01  qbf_q_res:                              0
% 2.67/1.01  qbf_num_tautologies:                    0
% 2.67/1.01  qbf_prep_cycles:                        0
% 2.67/1.01  
% 2.67/1.01  ------ BMC1
% 2.67/1.01  
% 2.67/1.01  bmc1_current_bound:                     -1
% 2.67/1.01  bmc1_last_solved_bound:                 -1
% 2.67/1.01  bmc1_unsat_core_size:                   -1
% 2.67/1.01  bmc1_unsat_core_parents_size:           -1
% 2.67/1.01  bmc1_merge_next_fun:                    0
% 2.67/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.67/1.01  
% 2.67/1.01  ------ Instantiation
% 2.67/1.01  
% 2.67/1.01  inst_num_of_clauses:                    342
% 2.67/1.01  inst_num_in_passive:                    134
% 2.67/1.01  inst_num_in_active:                     155
% 2.67/1.01  inst_num_in_unprocessed:                53
% 2.67/1.01  inst_num_of_loops:                      210
% 2.67/1.01  inst_num_of_learning_restarts:          0
% 2.67/1.01  inst_num_moves_active_passive:          53
% 2.67/1.01  inst_lit_activity:                      0
% 2.67/1.01  inst_lit_activity_moves:                0
% 2.67/1.01  inst_num_tautologies:                   0
% 2.67/1.01  inst_num_prop_implied:                  0
% 2.67/1.01  inst_num_existing_simplified:           0
% 2.67/1.01  inst_num_eq_res_simplified:             0
% 2.67/1.01  inst_num_child_elim:                    0
% 2.67/1.01  inst_num_of_dismatching_blockings:      75
% 2.67/1.01  inst_num_of_non_proper_insts:           296
% 2.67/1.01  inst_num_of_duplicates:                 0
% 2.67/1.01  inst_inst_num_from_inst_to_res:         0
% 2.67/1.01  inst_dismatching_checking_time:         0.
% 2.67/1.01  
% 2.67/1.01  ------ Resolution
% 2.67/1.01  
% 2.67/1.01  res_num_of_clauses:                     0
% 2.67/1.01  res_num_in_passive:                     0
% 2.67/1.01  res_num_in_active:                      0
% 2.67/1.01  res_num_of_loops:                       121
% 2.67/1.01  res_forward_subset_subsumed:            31
% 2.67/1.01  res_backward_subset_subsumed:           0
% 2.67/1.01  res_forward_subsumed:                   0
% 2.67/1.01  res_backward_subsumed:                  0
% 2.67/1.01  res_forward_subsumption_resolution:     1
% 2.67/1.01  res_backward_subsumption_resolution:    0
% 2.67/1.01  res_clause_to_clause_subsumption:       148
% 2.67/1.01  res_orphan_elimination:                 0
% 2.67/1.01  res_tautology_del:                      47
% 2.67/1.01  res_num_eq_res_simplified:              0
% 2.67/1.01  res_num_sel_changes:                    0
% 2.67/1.01  res_moves_from_active_to_pass:          0
% 2.67/1.01  
% 2.67/1.01  ------ Superposition
% 2.67/1.01  
% 2.67/1.01  sup_time_total:                         0.
% 2.67/1.01  sup_time_generating:                    0.
% 2.67/1.01  sup_time_sim_full:                      0.
% 2.67/1.01  sup_time_sim_immed:                     0.
% 2.67/1.01  
% 2.67/1.01  sup_num_of_clauses:                     58
% 2.67/1.01  sup_num_in_active:                      37
% 2.67/1.01  sup_num_in_passive:                     21
% 2.67/1.01  sup_num_of_loops:                       41
% 2.67/1.01  sup_fw_superposition:                   38
% 2.67/1.01  sup_bw_superposition:                   22
% 2.67/1.01  sup_immediate_simplified:               6
% 2.67/1.01  sup_given_eliminated:                   0
% 2.67/1.01  comparisons_done:                       0
% 2.67/1.01  comparisons_avoided:                    0
% 2.67/1.01  
% 2.67/1.01  ------ Simplifications
% 2.67/1.01  
% 2.67/1.01  
% 2.67/1.01  sim_fw_subset_subsumed:                 5
% 2.67/1.01  sim_bw_subset_subsumed:                 0
% 2.67/1.01  sim_fw_subsumed:                        1
% 2.67/1.01  sim_bw_subsumed:                        0
% 2.67/1.01  sim_fw_subsumption_res:                 0
% 2.67/1.01  sim_bw_subsumption_res:                 0
% 2.67/1.01  sim_tautology_del:                      5
% 2.67/1.01  sim_eq_tautology_del:                   1
% 2.67/1.01  sim_eq_res_simp:                        0
% 2.67/1.01  sim_fw_demodulated:                     0
% 2.67/1.01  sim_bw_demodulated:                     4
% 2.67/1.01  sim_light_normalised:                   0
% 2.67/1.01  sim_joinable_taut:                      0
% 2.67/1.01  sim_joinable_simp:                      0
% 2.67/1.01  sim_ac_normalised:                      0
% 2.67/1.01  sim_smt_subsumption:                    0
% 2.67/1.01  
%------------------------------------------------------------------------------
