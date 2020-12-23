%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1890+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:49 EST 2020

% Result     : Theorem 0.96s
% Output     : CNFRefutation 0.96s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 383 expanded)
%              Number of clauses        :   51 (  90 expanded)
%              Number of leaves         :    9 ( 107 expanded)
%              Depth                    :   21
%              Number of atoms          :  402 (2935 expanded)
%              Number of equality atoms :   51 ( 351 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   18 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,conjecture,(
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

fof(f8,negated_conjecture,(
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
    inference(negated_conjecture,[],[f7])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & ! [X2] :
              ( k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v2_tex_2(sK2,X0)
        & ! [X2] :
            ( k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),sK2,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
            | ~ r2_hidden(X2,sK2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
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
          ( ~ v2_tex_2(X1,sK1)
          & ! [X2] :
              ( k6_domain_1(u1_struct_0(sK1),X2) = k9_subset_1(u1_struct_0(sK1),X1,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X2)))
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(sK1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1)
      & v3_tdlat_3(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ~ v2_tex_2(sK2,sK1)
    & ! [X2] :
        ( k6_domain_1(u1_struct_0(sK1),X2) = k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X2)))
        | ~ r2_hidden(X2,sK2)
        | ~ m1_subset_1(X2,u1_struct_0(sK1)) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1)
    & v3_tdlat_3(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f21,f25,f24])).

fof(f41,plain,(
    ~ v2_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,X3)
                            & v4_pre_topc(X3,X0) ) )
                    & r2_hidden(X2,X1) ) )
           => v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ? [X2] :
              ( ! [X3] :
                  ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,X3)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ? [X2] :
              ( ! [X3] :
                  ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,X3)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,X3)
              | ~ v4_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( k6_domain_1(u1_struct_0(X0),sK0(X0,X1)) != k9_subset_1(u1_struct_0(X0),X1,X3)
            | ~ v4_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r2_hidden(sK0(X0,X1),X1)
        & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ( ! [X3] :
                ( k6_domain_1(u1_struct_0(X0),sK0(X0,X1)) != k9_subset_1(u1_struct_0(X0),X1,X3)
                | ~ v4_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & r2_hidden(sK0(X0,X1),X1)
            & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f22])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | r2_hidden(sK0(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f36,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f35,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f37,plain,(
    v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f38,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f39,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( v2_tex_2(X1,X0)
      | k6_domain_1(u1_struct_0(X0),sK0(X0,X1)) != k9_subset_1(u1_struct_0(X0),X1,X3)
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f10,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f40,plain,(
    ! [X2] :
      ( k6_domain_1(u1_struct_0(sK1),X2) = k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X2)))
      | ~ r2_hidden(X2,sK2)
      | ~ m1_subset_1(X2,u1_struct_0(sK1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | m1_subset_1(sK0(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_8,negated_conjecture,
    ( ~ v2_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_5,plain,
    ( v2_tex_2(X0,X1)
    | r2_hidden(sK0(X1,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_13,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_280,plain,
    ( v2_tex_2(X0,X1)
    | r2_hidden(sK0(X1,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_13])).

cnf(c_281,plain,
    ( v2_tex_2(X0,sK1)
    | r2_hidden(sK0(sK1,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_tdlat_3(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_280])).

cnf(c_14,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_12,negated_conjecture,
    ( v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_11,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_285,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(sK0(sK1,X0),X0)
    | v2_tex_2(X0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_281,c_14,c_12,c_11])).

cnf(c_286,plain,
    ( v2_tex_2(X0,sK1)
    | r2_hidden(sK0(sK1,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(renaming,[status(thm)],[c_285])).

cnf(c_329,plain,
    ( r2_hidden(sK0(sK1,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_286])).

cnf(c_330,plain,
    ( r2_hidden(sK0(sK1,sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_329])).

cnf(c_10,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_332,plain,
    ( r2_hidden(sK0(sK1,sK2),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_330,c_10])).

cnf(c_376,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | sK0(sK1,sK2) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_332])).

cnf(c_377,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
    | ~ v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_376])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_415,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(X2))
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_377,c_1])).

cnf(c_416,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(X1)) ),
    inference(unflattening,[status(thm)],[c_415])).

cnf(c_483,plain,
    ( ~ m1_subset_1(X0_45,X0_46)
    | m1_subset_1(k6_domain_1(X0_46,X0_45),k1_zfmisc_1(X0_46))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(X0_46)) ),
    inference(subtyping,[status(esa)],[c_416])).

cnf(c_663,plain,
    ( ~ m1_subset_1(X0_45,u1_struct_0(sK1))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK1),X0_45),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_483])).

cnf(c_694,plain,
    ( ~ m1_subset_1(sK0(sK1,sK2),u1_struct_0(sK1))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_663])).

cnf(c_2,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_4,plain,
    ( v2_tex_2(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k6_domain_1(u1_struct_0(X1),sK0(X1,X0)) != k9_subset_1(u1_struct_0(X1),X0,X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_191,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | X1 != X3
    | k6_domain_1(u1_struct_0(X1),sK0(X1,X0)) != k9_subset_1(u1_struct_0(X1),X0,X4)
    | k2_pre_topc(X3,X2) != X4 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_4])).

cnf(c_192,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k6_domain_1(u1_struct_0(X1),sK0(X1,X0)) != k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) ),
    inference(unflattening,[status(thm)],[c_191])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_214,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k6_domain_1(u1_struct_0(X1),sK0(X1,X0)) != k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_192,c_0])).

cnf(c_235,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) != k6_domain_1(u1_struct_0(X1),sK0(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_214,c_13])).

cnf(c_236,plain,
    ( v2_tex_2(X0,sK1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_tdlat_3(sK1)
    | ~ l1_pre_topc(sK1)
    | k9_subset_1(u1_struct_0(sK1),X0,k2_pre_topc(sK1,X1)) != k6_domain_1(u1_struct_0(sK1),sK0(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_235])).

cnf(c_240,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_tex_2(X0,sK1)
    | k9_subset_1(u1_struct_0(sK1),X0,k2_pre_topc(sK1,X1)) != k6_domain_1(u1_struct_0(sK1),sK0(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_236,c_14,c_12,c_11])).

cnf(c_241,plain,
    ( v2_tex_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | k9_subset_1(u1_struct_0(sK1),X0,k2_pre_topc(sK1,X1)) != k6_domain_1(u1_struct_0(sK1),sK0(sK1,X0)) ),
    inference(renaming,[status(thm)],[c_240])).

cnf(c_351,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | k9_subset_1(u1_struct_0(sK1),X0,k2_pre_topc(sK1,X1)) != k6_domain_1(u1_struct_0(sK1),sK0(sK1,X0))
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_241])).

cnf(c_352,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,X0)) != k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_351])).

cnf(c_356,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,X0)) != k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_352,c_10])).

cnf(c_486,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1)))
    | k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,X0_45)) != k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)) ),
    inference(subtyping,[status(esa)],[c_356])).

cnf(c_659,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)))) != k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_486])).

cnf(c_9,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k6_domain_1(u1_struct_0(sK1),X0) = k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_400,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0))) = k6_domain_1(u1_struct_0(sK1),X0)
    | sK0(sK1,sK2) != X0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_332])).

cnf(c_401,plain,
    ( ~ m1_subset_1(sK0(sK1,sK2),u1_struct_0(sK1))
    | k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)))) = k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_400])).

cnf(c_6,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_259,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_13])).

cnf(c_260,plain,
    ( v2_tex_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(sK1,X0),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ v3_tdlat_3(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_259])).

cnf(c_264,plain,
    ( m1_subset_1(sK0(sK1,X0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_tex_2(X0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_260,c_14,c_12,c_11])).

cnf(c_265,plain,
    ( v2_tex_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(sK1,X0),u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_264])).

cnf(c_340,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(sK1,X0),u1_struct_0(sK1))
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_265])).

cnf(c_341,plain,
    ( m1_subset_1(sK0(sK1,sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_340])).

cnf(c_403,plain,
    ( k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)))) = k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_401,c_10,c_341])).

cnf(c_484,plain,
    ( k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)))) = k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)) ),
    inference(subtyping,[status(esa)],[c_403])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_694,c_659,c_484,c_341,c_10])).


%------------------------------------------------------------------------------
