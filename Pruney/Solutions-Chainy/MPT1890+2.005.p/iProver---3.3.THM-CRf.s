%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:35 EST 2020

% Result     : Theorem 0.88s
% Output     : CNFRefutation 0.88s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 412 expanded)
%              Number of clauses        :   53 (  96 expanded)
%              Number of leaves         :    9 ( 116 expanded)
%              Depth                    :   19
%              Number of atoms          :  391 (3165 expanded)
%              Number of equality atoms :   67 ( 403 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   18 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
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
                 => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) = k6_domain_1(u1_struct_0(X0),X2) ) )
           => v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
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
                   => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) = k6_domain_1(u1_struct_0(X0),X2) ) )
             => v2_tex_2(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & ! [X2] :
              ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) = k6_domain_1(u1_struct_0(X0),X2)
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & ! [X2] :
              ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) = k6_domain_1(u1_struct_0(X0),X2)
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & ! [X2] :
              ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) = k6_domain_1(u1_struct_0(X0),X2)
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v2_tex_2(sK2,X0)
        & ! [X2] :
            ( k9_subset_1(u1_struct_0(X0),sK2,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) = k6_domain_1(u1_struct_0(X0),X2)
            | ~ r2_hidden(X2,sK2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tex_2(X1,X0)
            & ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) = k6_domain_1(u1_struct_0(X0),X2)
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
              ( k9_subset_1(u1_struct_0(sK1),X1,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X2))) = k6_domain_1(u1_struct_0(sK1),X2)
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(sK1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1)
      & v3_tdlat_3(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ~ v2_tex_2(sK2,sK1)
    & ! [X2] :
        ( k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X2))) = k6_domain_1(u1_struct_0(sK1),X2)
        | ~ r2_hidden(X2,sK2)
        | ~ m1_subset_1(X2,u1_struct_0(sK1)) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1)
    & v3_tdlat_3(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f17,f21,f20])).

fof(f36,plain,(
    ~ v2_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f22])).

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
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = k6_domain_1(u1_struct_0(X0),X2)
                            & v4_pre_topc(X3,X0) ) )
                    & r2_hidden(X2,X1) ) )
           => v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ? [X2] :
              ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2)
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

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ? [X2] :
              ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2)
              | ~ v4_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK0(X0,X1))
            | ~ v4_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r2_hidden(sK0(X0,X1),X1)
        & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK0(X0,X1))
                | ~ v4_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & r2_hidden(sK0(X0,X1),X1)
            & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f18])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | m1_subset_1(sK0(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f31,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f30,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f32,plain,(
    v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f33,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f34,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | r2_hidden(sK0(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f35,plain,(
    ! [X2] :
      ( k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X2))) = k6_domain_1(u1_struct_0(sK1),X2)
      | ~ r2_hidden(X2,sK2)
      | ~ m1_subset_1(X2,u1_struct_0(sK1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( v2_tex_2(X1,X0)
      | k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK0(X0,X1))
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_7,negated_conjecture,
    ( ~ v2_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_6,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_12,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_281,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_12])).

cnf(c_282,plain,
    ( v2_tex_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(sK1,X0),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ v3_tdlat_3(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_281])).

cnf(c_13,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_11,negated_conjecture,
    ( v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_10,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_286,plain,
    ( m1_subset_1(sK0(sK1,X0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_tex_2(X0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_282,c_13,c_11,c_10])).

cnf(c_287,plain,
    ( v2_tex_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(sK1,X0),u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_286])).

cnf(c_329,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(sK1,X0),u1_struct_0(sK1))
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_287])).

cnf(c_330,plain,
    ( m1_subset_1(sK0(sK1,sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_329])).

cnf(c_9,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_332,plain,
    ( m1_subset_1(sK0(sK1,sK2),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_330,c_9])).

cnf(c_5,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | v2_tex_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_tdlat_3(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_8,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0))) = k6_domain_1(u1_struct_0(sK1),X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_160,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X2))) = k6_domain_1(u1_struct_0(sK1),X2)
    | sK0(X1,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_8])).

cnf(c_161,plain,
    ( v2_tex_2(sK2,X0)
    | ~ m1_subset_1(sK0(X0,sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_tdlat_3(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK0(X0,sK2)))) = k6_domain_1(u1_struct_0(sK1),sK0(X0,sK2)) ),
    inference(unflattening,[status(thm)],[c_160])).

cnf(c_243,plain,
    ( v2_tex_2(sK2,X0)
    | ~ m1_subset_1(sK0(X0,sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_tdlat_3(X0)
    | ~ l1_pre_topc(X0)
    | k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK0(X0,sK2)))) = k6_domain_1(u1_struct_0(sK1),sK0(X0,sK2))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_161,c_12])).

cnf(c_244,plain,
    ( v2_tex_2(sK2,sK1)
    | ~ m1_subset_1(sK0(sK1,sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_tdlat_3(sK1)
    | ~ l1_pre_topc(sK1)
    | k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)))) = k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_243])).

cnf(c_246,plain,
    ( ~ m1_subset_1(sK0(sK1,sK2),u1_struct_0(sK1))
    | k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)))) = k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_244,c_13,c_11,c_10,c_9,c_7])).

cnf(c_359,plain,
    ( k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)))) = k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_332,c_246])).

cnf(c_414,plain,
    ( k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)))) = k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)) ),
    inference(subtyping,[status(esa)],[c_359])).

cnf(c_418,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_551,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_418])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_420,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X0_45))
    | k9_subset_1(X0_45,X0_44,X1_44) = k9_subset_1(X0_45,X1_44,X0_44) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_549,plain,
    ( k9_subset_1(X0_45,X0_44,X1_44) = k9_subset_1(X0_45,X1_44,X0_44)
    | m1_subset_1(X0_44,k1_zfmisc_1(X0_45)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_420])).

cnf(c_739,plain,
    ( k9_subset_1(u1_struct_0(sK1),sK2,X0_44) = k9_subset_1(u1_struct_0(sK1),X0_44,sK2) ),
    inference(superposition,[status(thm)],[c_551,c_549])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_419,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X0_45))
    | m1_subset_1(k9_subset_1(X0_45,X1_44,X0_44),k1_zfmisc_1(X0_45)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_550,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(X0_45)) != iProver_top
    | m1_subset_1(k9_subset_1(X0_45,X1_44,X0_44),k1_zfmisc_1(X0_45)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_419])).

cnf(c_824,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK1),sK2,X0_44),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_739,c_550])).

cnf(c_18,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_850,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK1),sK2,X0_44),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_824,c_18])).

cnf(c_857,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_414,c_850])).

cnf(c_3,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f26])).

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
    inference(cnf_transformation,[],[f29])).

cnf(c_199,plain,
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
    inference(resolution_lifted,[status(thm)],[c_3,c_4])).

cnf(c_200,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k6_domain_1(u1_struct_0(X1),sK0(X1,X0)) != k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) ),
    inference(unflattening,[status(thm)],[c_199])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_222,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k6_domain_1(u1_struct_0(X1),sK0(X1,X0)) != k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_200,c_2])).

cnf(c_257,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) != k6_domain_1(u1_struct_0(X1),sK0(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_222,c_12])).

cnf(c_258,plain,
    ( v2_tex_2(X0,sK1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_tdlat_3(sK1)
    | ~ l1_pre_topc(sK1)
    | k9_subset_1(u1_struct_0(sK1),X0,k2_pre_topc(sK1,X1)) != k6_domain_1(u1_struct_0(sK1),sK0(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_257])).

cnf(c_262,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_tex_2(X0,sK1)
    | k9_subset_1(u1_struct_0(sK1),X0,k2_pre_topc(sK1,X1)) != k6_domain_1(u1_struct_0(sK1),sK0(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_258,c_13,c_11,c_10])).

cnf(c_263,plain,
    ( v2_tex_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | k9_subset_1(u1_struct_0(sK1),X0,k2_pre_topc(sK1,X1)) != k6_domain_1(u1_struct_0(sK1),sK0(sK1,X0)) ),
    inference(renaming,[status(thm)],[c_262])).

cnf(c_340,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | k9_subset_1(u1_struct_0(sK1),X0,k2_pre_topc(sK1,X1)) != k6_domain_1(u1_struct_0(sK1),sK0(sK1,X0))
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_263])).

cnf(c_341,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,X0)) != k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_340])).

cnf(c_345,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,X0)) != k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_341,c_9])).

cnf(c_415,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
    | k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,X0_44)) != k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)) ),
    inference(subtyping,[status(esa)],[c_345])).

cnf(c_590,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)))) != k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_415])).

cnf(c_591,plain,
    ( k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)))) != k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_590])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_857,c_591,c_414])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:55:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 0.88/1.04  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.88/1.04  
% 0.88/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.88/1.04  
% 0.88/1.04  ------  iProver source info
% 0.88/1.04  
% 0.88/1.04  git: date: 2020-06-30 10:37:57 +0100
% 0.88/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.88/1.04  git: non_committed_changes: false
% 0.88/1.04  git: last_make_outside_of_git: false
% 0.88/1.04  
% 0.88/1.04  ------ 
% 0.88/1.04  
% 0.88/1.04  ------ Input Options
% 0.88/1.04  
% 0.88/1.04  --out_options                           all
% 0.88/1.04  --tptp_safe_out                         true
% 0.88/1.04  --problem_path                          ""
% 0.88/1.04  --include_path                          ""
% 0.88/1.04  --clausifier                            res/vclausify_rel
% 0.88/1.04  --clausifier_options                    --mode clausify
% 0.88/1.04  --stdin                                 false
% 0.88/1.04  --stats_out                             all
% 0.88/1.04  
% 0.88/1.04  ------ General Options
% 0.88/1.04  
% 0.88/1.04  --fof                                   false
% 0.88/1.04  --time_out_real                         305.
% 0.88/1.04  --time_out_virtual                      -1.
% 0.88/1.04  --symbol_type_check                     false
% 0.88/1.04  --clausify_out                          false
% 0.88/1.04  --sig_cnt_out                           false
% 0.88/1.04  --trig_cnt_out                          false
% 0.88/1.04  --trig_cnt_out_tolerance                1.
% 0.88/1.04  --trig_cnt_out_sk_spl                   false
% 0.88/1.04  --abstr_cl_out                          false
% 0.88/1.04  
% 0.88/1.04  ------ Global Options
% 0.88/1.04  
% 0.88/1.04  --schedule                              default
% 0.88/1.04  --add_important_lit                     false
% 0.88/1.04  --prop_solver_per_cl                    1000
% 0.88/1.04  --min_unsat_core                        false
% 0.88/1.04  --soft_assumptions                      false
% 0.88/1.04  --soft_lemma_size                       3
% 0.88/1.04  --prop_impl_unit_size                   0
% 0.88/1.04  --prop_impl_unit                        []
% 0.88/1.04  --share_sel_clauses                     true
% 0.88/1.04  --reset_solvers                         false
% 0.88/1.04  --bc_imp_inh                            [conj_cone]
% 0.88/1.04  --conj_cone_tolerance                   3.
% 0.88/1.04  --extra_neg_conj                        none
% 0.88/1.04  --large_theory_mode                     true
% 0.88/1.04  --prolific_symb_bound                   200
% 0.88/1.04  --lt_threshold                          2000
% 0.88/1.04  --clause_weak_htbl                      true
% 0.88/1.04  --gc_record_bc_elim                     false
% 0.88/1.04  
% 0.88/1.04  ------ Preprocessing Options
% 0.88/1.04  
% 0.88/1.04  --preprocessing_flag                    true
% 0.88/1.04  --time_out_prep_mult                    0.1
% 0.88/1.04  --splitting_mode                        input
% 0.88/1.04  --splitting_grd                         true
% 0.88/1.04  --splitting_cvd                         false
% 0.88/1.04  --splitting_cvd_svl                     false
% 0.88/1.04  --splitting_nvd                         32
% 0.88/1.04  --sub_typing                            true
% 0.88/1.04  --prep_gs_sim                           true
% 0.88/1.04  --prep_unflatten                        true
% 0.88/1.04  --prep_res_sim                          true
% 0.88/1.04  --prep_upred                            true
% 0.88/1.04  --prep_sem_filter                       exhaustive
% 0.88/1.04  --prep_sem_filter_out                   false
% 0.88/1.04  --pred_elim                             true
% 0.88/1.04  --res_sim_input                         true
% 0.88/1.04  --eq_ax_congr_red                       true
% 0.88/1.04  --pure_diseq_elim                       true
% 0.88/1.04  --brand_transform                       false
% 0.88/1.04  --non_eq_to_eq                          false
% 0.88/1.04  --prep_def_merge                        true
% 0.88/1.04  --prep_def_merge_prop_impl              false
% 0.88/1.04  --prep_def_merge_mbd                    true
% 0.88/1.04  --prep_def_merge_tr_red                 false
% 0.88/1.04  --prep_def_merge_tr_cl                  false
% 0.88/1.04  --smt_preprocessing                     true
% 0.88/1.04  --smt_ac_axioms                         fast
% 0.88/1.04  --preprocessed_out                      false
% 0.88/1.04  --preprocessed_stats                    false
% 0.88/1.04  
% 0.88/1.04  ------ Abstraction refinement Options
% 0.88/1.04  
% 0.88/1.04  --abstr_ref                             []
% 0.88/1.04  --abstr_ref_prep                        false
% 0.88/1.04  --abstr_ref_until_sat                   false
% 0.88/1.04  --abstr_ref_sig_restrict                funpre
% 0.88/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 0.88/1.04  --abstr_ref_under                       []
% 0.88/1.04  
% 0.88/1.04  ------ SAT Options
% 0.88/1.04  
% 0.88/1.04  --sat_mode                              false
% 0.88/1.04  --sat_fm_restart_options                ""
% 0.88/1.04  --sat_gr_def                            false
% 0.88/1.04  --sat_epr_types                         true
% 0.88/1.04  --sat_non_cyclic_types                  false
% 0.88/1.04  --sat_finite_models                     false
% 0.88/1.04  --sat_fm_lemmas                         false
% 0.88/1.04  --sat_fm_prep                           false
% 0.88/1.04  --sat_fm_uc_incr                        true
% 0.88/1.04  --sat_out_model                         small
% 0.88/1.04  --sat_out_clauses                       false
% 0.88/1.04  
% 0.88/1.04  ------ QBF Options
% 0.88/1.04  
% 0.88/1.04  --qbf_mode                              false
% 0.88/1.04  --qbf_elim_univ                         false
% 0.88/1.04  --qbf_dom_inst                          none
% 0.88/1.04  --qbf_dom_pre_inst                      false
% 0.88/1.04  --qbf_sk_in                             false
% 0.88/1.04  --qbf_pred_elim                         true
% 0.88/1.04  --qbf_split                             512
% 0.88/1.04  
% 0.88/1.04  ------ BMC1 Options
% 0.88/1.04  
% 0.88/1.04  --bmc1_incremental                      false
% 0.88/1.04  --bmc1_axioms                           reachable_all
% 0.88/1.04  --bmc1_min_bound                        0
% 0.88/1.04  --bmc1_max_bound                        -1
% 0.88/1.04  --bmc1_max_bound_default                -1
% 0.88/1.04  --bmc1_symbol_reachability              true
% 0.88/1.04  --bmc1_property_lemmas                  false
% 0.88/1.04  --bmc1_k_induction                      false
% 0.88/1.04  --bmc1_non_equiv_states                 false
% 0.88/1.04  --bmc1_deadlock                         false
% 0.88/1.04  --bmc1_ucm                              false
% 0.88/1.04  --bmc1_add_unsat_core                   none
% 0.88/1.04  --bmc1_unsat_core_children              false
% 0.88/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 0.88/1.04  --bmc1_out_stat                         full
% 0.88/1.04  --bmc1_ground_init                      false
% 0.88/1.04  --bmc1_pre_inst_next_state              false
% 0.88/1.04  --bmc1_pre_inst_state                   false
% 0.88/1.04  --bmc1_pre_inst_reach_state             false
% 0.88/1.04  --bmc1_out_unsat_core                   false
% 0.88/1.04  --bmc1_aig_witness_out                  false
% 0.88/1.04  --bmc1_verbose                          false
% 0.88/1.04  --bmc1_dump_clauses_tptp                false
% 0.88/1.04  --bmc1_dump_unsat_core_tptp             false
% 0.88/1.04  --bmc1_dump_file                        -
% 0.88/1.04  --bmc1_ucm_expand_uc_limit              128
% 0.88/1.04  --bmc1_ucm_n_expand_iterations          6
% 0.88/1.04  --bmc1_ucm_extend_mode                  1
% 0.88/1.04  --bmc1_ucm_init_mode                    2
% 0.88/1.04  --bmc1_ucm_cone_mode                    none
% 0.88/1.04  --bmc1_ucm_reduced_relation_type        0
% 0.88/1.04  --bmc1_ucm_relax_model                  4
% 0.88/1.04  --bmc1_ucm_full_tr_after_sat            true
% 0.88/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 0.88/1.04  --bmc1_ucm_layered_model                none
% 0.88/1.04  --bmc1_ucm_max_lemma_size               10
% 0.88/1.04  
% 0.88/1.04  ------ AIG Options
% 0.88/1.04  
% 0.88/1.04  --aig_mode                              false
% 0.88/1.04  
% 0.88/1.04  ------ Instantiation Options
% 0.88/1.04  
% 0.88/1.04  --instantiation_flag                    true
% 0.88/1.04  --inst_sos_flag                         false
% 0.88/1.04  --inst_sos_phase                        true
% 0.88/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.88/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.88/1.04  --inst_lit_sel_side                     num_symb
% 0.88/1.04  --inst_solver_per_active                1400
% 0.88/1.04  --inst_solver_calls_frac                1.
% 0.88/1.04  --inst_passive_queue_type               priority_queues
% 0.88/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.88/1.04  --inst_passive_queues_freq              [25;2]
% 0.88/1.04  --inst_dismatching                      true
% 0.88/1.04  --inst_eager_unprocessed_to_passive     true
% 0.88/1.04  --inst_prop_sim_given                   true
% 0.88/1.04  --inst_prop_sim_new                     false
% 0.88/1.04  --inst_subs_new                         false
% 0.88/1.04  --inst_eq_res_simp                      false
% 0.88/1.04  --inst_subs_given                       false
% 0.88/1.04  --inst_orphan_elimination               true
% 0.88/1.04  --inst_learning_loop_flag               true
% 0.88/1.04  --inst_learning_start                   3000
% 0.88/1.04  --inst_learning_factor                  2
% 0.88/1.04  --inst_start_prop_sim_after_learn       3
% 0.88/1.04  --inst_sel_renew                        solver
% 0.88/1.04  --inst_lit_activity_flag                true
% 0.88/1.04  --inst_restr_to_given                   false
% 0.88/1.04  --inst_activity_threshold               500
% 0.88/1.04  --inst_out_proof                        true
% 0.88/1.04  
% 0.88/1.04  ------ Resolution Options
% 0.88/1.04  
% 0.88/1.04  --resolution_flag                       true
% 0.88/1.04  --res_lit_sel                           adaptive
% 0.88/1.04  --res_lit_sel_side                      none
% 0.88/1.04  --res_ordering                          kbo
% 0.88/1.04  --res_to_prop_solver                    active
% 0.88/1.04  --res_prop_simpl_new                    false
% 0.88/1.04  --res_prop_simpl_given                  true
% 0.88/1.04  --res_passive_queue_type                priority_queues
% 0.88/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.88/1.04  --res_passive_queues_freq               [15;5]
% 0.88/1.04  --res_forward_subs                      full
% 0.88/1.04  --res_backward_subs                     full
% 0.88/1.04  --res_forward_subs_resolution           true
% 0.88/1.04  --res_backward_subs_resolution          true
% 0.88/1.04  --res_orphan_elimination                true
% 0.88/1.04  --res_time_limit                        2.
% 0.88/1.04  --res_out_proof                         true
% 0.88/1.04  
% 0.88/1.04  ------ Superposition Options
% 0.88/1.04  
% 0.88/1.04  --superposition_flag                    true
% 0.88/1.04  --sup_passive_queue_type                priority_queues
% 0.88/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.88/1.04  --sup_passive_queues_freq               [8;1;4]
% 0.88/1.04  --demod_completeness_check              fast
% 0.88/1.04  --demod_use_ground                      true
% 0.88/1.04  --sup_to_prop_solver                    passive
% 0.88/1.04  --sup_prop_simpl_new                    true
% 0.88/1.04  --sup_prop_simpl_given                  true
% 0.88/1.04  --sup_fun_splitting                     false
% 0.88/1.04  --sup_smt_interval                      50000
% 0.88/1.04  
% 0.88/1.04  ------ Superposition Simplification Setup
% 0.88/1.04  
% 0.88/1.04  --sup_indices_passive                   []
% 0.88/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.88/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.88/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.88/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 0.88/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.88/1.04  --sup_full_bw                           [BwDemod]
% 0.88/1.04  --sup_immed_triv                        [TrivRules]
% 0.88/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.88/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.88/1.04  --sup_immed_bw_main                     []
% 0.88/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.88/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 0.88/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.88/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.88/1.04  
% 0.88/1.04  ------ Combination Options
% 0.88/1.04  
% 0.88/1.04  --comb_res_mult                         3
% 0.88/1.04  --comb_sup_mult                         2
% 0.88/1.04  --comb_inst_mult                        10
% 0.88/1.04  
% 0.88/1.04  ------ Debug Options
% 0.88/1.04  
% 0.88/1.04  --dbg_backtrace                         false
% 0.88/1.04  --dbg_dump_prop_clauses                 false
% 0.88/1.04  --dbg_dump_prop_clauses_file            -
% 0.88/1.04  --dbg_out_stat                          false
% 0.88/1.04  ------ Parsing...
% 0.88/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.88/1.04  
% 0.88/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 0.88/1.04  
% 0.88/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.88/1.04  
% 0.88/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.88/1.04  ------ Proving...
% 0.88/1.04  ------ Problem Properties 
% 0.88/1.04  
% 0.88/1.04  
% 0.88/1.04  clauses                                 7
% 0.88/1.04  conjectures                             1
% 0.88/1.04  EPR                                     0
% 0.88/1.04  Horn                                    7
% 0.88/1.04  unary                                   3
% 0.88/1.04  binary                                  4
% 0.88/1.04  lits                                    11
% 0.88/1.04  lits eq                                 3
% 0.88/1.04  fd_pure                                 0
% 0.88/1.04  fd_pseudo                               0
% 0.88/1.04  fd_cond                                 0
% 0.88/1.04  fd_pseudo_cond                          0
% 0.88/1.04  AC symbols                              0
% 0.88/1.04  
% 0.88/1.04  ------ Schedule dynamic 5 is on 
% 0.88/1.04  
% 0.88/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.88/1.04  
% 0.88/1.04  
% 0.88/1.04  ------ 
% 0.88/1.04  Current options:
% 0.88/1.04  ------ 
% 0.88/1.04  
% 0.88/1.04  ------ Input Options
% 0.88/1.04  
% 0.88/1.04  --out_options                           all
% 0.88/1.04  --tptp_safe_out                         true
% 0.88/1.04  --problem_path                          ""
% 0.88/1.04  --include_path                          ""
% 0.88/1.04  --clausifier                            res/vclausify_rel
% 0.88/1.04  --clausifier_options                    --mode clausify
% 0.88/1.04  --stdin                                 false
% 0.88/1.04  --stats_out                             all
% 0.88/1.04  
% 0.88/1.04  ------ General Options
% 0.88/1.04  
% 0.88/1.04  --fof                                   false
% 0.88/1.04  --time_out_real                         305.
% 0.88/1.04  --time_out_virtual                      -1.
% 0.88/1.04  --symbol_type_check                     false
% 0.88/1.04  --clausify_out                          false
% 0.88/1.04  --sig_cnt_out                           false
% 0.88/1.04  --trig_cnt_out                          false
% 0.88/1.04  --trig_cnt_out_tolerance                1.
% 0.88/1.04  --trig_cnt_out_sk_spl                   false
% 0.88/1.04  --abstr_cl_out                          false
% 0.88/1.04  
% 0.88/1.04  ------ Global Options
% 0.88/1.04  
% 0.88/1.04  --schedule                              default
% 0.88/1.04  --add_important_lit                     false
% 0.88/1.04  --prop_solver_per_cl                    1000
% 0.88/1.04  --min_unsat_core                        false
% 0.88/1.04  --soft_assumptions                      false
% 0.88/1.04  --soft_lemma_size                       3
% 0.88/1.04  --prop_impl_unit_size                   0
% 0.88/1.04  --prop_impl_unit                        []
% 0.88/1.04  --share_sel_clauses                     true
% 0.88/1.04  --reset_solvers                         false
% 0.88/1.04  --bc_imp_inh                            [conj_cone]
% 0.88/1.04  --conj_cone_tolerance                   3.
% 0.88/1.04  --extra_neg_conj                        none
% 0.88/1.04  --large_theory_mode                     true
% 0.88/1.04  --prolific_symb_bound                   200
% 0.88/1.04  --lt_threshold                          2000
% 0.88/1.04  --clause_weak_htbl                      true
% 0.88/1.04  --gc_record_bc_elim                     false
% 0.88/1.04  
% 0.88/1.04  ------ Preprocessing Options
% 0.88/1.04  
% 0.88/1.04  --preprocessing_flag                    true
% 0.88/1.04  --time_out_prep_mult                    0.1
% 0.88/1.04  --splitting_mode                        input
% 0.88/1.04  --splitting_grd                         true
% 0.88/1.04  --splitting_cvd                         false
% 0.88/1.04  --splitting_cvd_svl                     false
% 0.88/1.04  --splitting_nvd                         32
% 0.88/1.04  --sub_typing                            true
% 0.88/1.04  --prep_gs_sim                           true
% 0.88/1.04  --prep_unflatten                        true
% 0.88/1.04  --prep_res_sim                          true
% 0.88/1.04  --prep_upred                            true
% 0.88/1.04  --prep_sem_filter                       exhaustive
% 0.88/1.04  --prep_sem_filter_out                   false
% 0.88/1.04  --pred_elim                             true
% 0.88/1.04  --res_sim_input                         true
% 0.88/1.04  --eq_ax_congr_red                       true
% 0.88/1.04  --pure_diseq_elim                       true
% 0.88/1.04  --brand_transform                       false
% 0.88/1.04  --non_eq_to_eq                          false
% 0.88/1.04  --prep_def_merge                        true
% 0.88/1.04  --prep_def_merge_prop_impl              false
% 0.88/1.04  --prep_def_merge_mbd                    true
% 0.88/1.04  --prep_def_merge_tr_red                 false
% 0.88/1.04  --prep_def_merge_tr_cl                  false
% 0.88/1.04  --smt_preprocessing                     true
% 0.88/1.04  --smt_ac_axioms                         fast
% 0.88/1.04  --preprocessed_out                      false
% 0.88/1.04  --preprocessed_stats                    false
% 0.88/1.04  
% 0.88/1.04  ------ Abstraction refinement Options
% 0.88/1.04  
% 0.88/1.04  --abstr_ref                             []
% 0.88/1.04  --abstr_ref_prep                        false
% 0.88/1.04  --abstr_ref_until_sat                   false
% 0.88/1.04  --abstr_ref_sig_restrict                funpre
% 0.88/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 0.88/1.04  --abstr_ref_under                       []
% 0.88/1.04  
% 0.88/1.04  ------ SAT Options
% 0.88/1.04  
% 0.88/1.04  --sat_mode                              false
% 0.88/1.04  --sat_fm_restart_options                ""
% 0.88/1.04  --sat_gr_def                            false
% 0.88/1.04  --sat_epr_types                         true
% 0.88/1.04  --sat_non_cyclic_types                  false
% 0.88/1.04  --sat_finite_models                     false
% 0.88/1.04  --sat_fm_lemmas                         false
% 0.88/1.04  --sat_fm_prep                           false
% 0.88/1.04  --sat_fm_uc_incr                        true
% 0.88/1.04  --sat_out_model                         small
% 0.88/1.04  --sat_out_clauses                       false
% 0.88/1.04  
% 0.88/1.04  ------ QBF Options
% 0.88/1.04  
% 0.88/1.04  --qbf_mode                              false
% 0.88/1.04  --qbf_elim_univ                         false
% 0.88/1.04  --qbf_dom_inst                          none
% 0.88/1.04  --qbf_dom_pre_inst                      false
% 0.88/1.04  --qbf_sk_in                             false
% 0.88/1.04  --qbf_pred_elim                         true
% 0.88/1.04  --qbf_split                             512
% 0.88/1.04  
% 0.88/1.04  ------ BMC1 Options
% 0.88/1.04  
% 0.88/1.04  --bmc1_incremental                      false
% 0.88/1.04  --bmc1_axioms                           reachable_all
% 0.88/1.04  --bmc1_min_bound                        0
% 0.88/1.04  --bmc1_max_bound                        -1
% 0.88/1.04  --bmc1_max_bound_default                -1
% 0.88/1.04  --bmc1_symbol_reachability              true
% 0.88/1.04  --bmc1_property_lemmas                  false
% 0.88/1.04  --bmc1_k_induction                      false
% 0.88/1.04  --bmc1_non_equiv_states                 false
% 0.88/1.04  --bmc1_deadlock                         false
% 0.88/1.04  --bmc1_ucm                              false
% 0.88/1.04  --bmc1_add_unsat_core                   none
% 0.88/1.04  --bmc1_unsat_core_children              false
% 0.88/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 0.88/1.04  --bmc1_out_stat                         full
% 0.88/1.04  --bmc1_ground_init                      false
% 0.88/1.04  --bmc1_pre_inst_next_state              false
% 0.88/1.04  --bmc1_pre_inst_state                   false
% 0.88/1.04  --bmc1_pre_inst_reach_state             false
% 0.88/1.04  --bmc1_out_unsat_core                   false
% 0.88/1.04  --bmc1_aig_witness_out                  false
% 0.88/1.04  --bmc1_verbose                          false
% 0.88/1.04  --bmc1_dump_clauses_tptp                false
% 0.88/1.04  --bmc1_dump_unsat_core_tptp             false
% 0.88/1.04  --bmc1_dump_file                        -
% 0.88/1.04  --bmc1_ucm_expand_uc_limit              128
% 0.88/1.04  --bmc1_ucm_n_expand_iterations          6
% 0.88/1.04  --bmc1_ucm_extend_mode                  1
% 0.88/1.04  --bmc1_ucm_init_mode                    2
% 0.88/1.04  --bmc1_ucm_cone_mode                    none
% 0.88/1.04  --bmc1_ucm_reduced_relation_type        0
% 0.88/1.04  --bmc1_ucm_relax_model                  4
% 0.88/1.04  --bmc1_ucm_full_tr_after_sat            true
% 0.88/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 0.88/1.04  --bmc1_ucm_layered_model                none
% 0.88/1.04  --bmc1_ucm_max_lemma_size               10
% 0.88/1.04  
% 0.88/1.04  ------ AIG Options
% 0.88/1.04  
% 0.88/1.04  --aig_mode                              false
% 0.88/1.04  
% 0.88/1.04  ------ Instantiation Options
% 0.88/1.04  
% 0.88/1.04  --instantiation_flag                    true
% 0.88/1.04  --inst_sos_flag                         false
% 0.88/1.04  --inst_sos_phase                        true
% 0.88/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.88/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.88/1.04  --inst_lit_sel_side                     none
% 0.88/1.04  --inst_solver_per_active                1400
% 0.88/1.04  --inst_solver_calls_frac                1.
% 0.88/1.04  --inst_passive_queue_type               priority_queues
% 0.88/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.88/1.04  --inst_passive_queues_freq              [25;2]
% 0.88/1.04  --inst_dismatching                      true
% 0.88/1.04  --inst_eager_unprocessed_to_passive     true
% 0.88/1.04  --inst_prop_sim_given                   true
% 0.88/1.04  --inst_prop_sim_new                     false
% 0.88/1.04  --inst_subs_new                         false
% 0.88/1.04  --inst_eq_res_simp                      false
% 0.88/1.04  --inst_subs_given                       false
% 0.88/1.04  --inst_orphan_elimination               true
% 0.88/1.04  --inst_learning_loop_flag               true
% 0.88/1.04  --inst_learning_start                   3000
% 0.88/1.04  --inst_learning_factor                  2
% 0.88/1.04  --inst_start_prop_sim_after_learn       3
% 0.88/1.04  --inst_sel_renew                        solver
% 0.88/1.04  --inst_lit_activity_flag                true
% 0.88/1.04  --inst_restr_to_given                   false
% 0.88/1.04  --inst_activity_threshold               500
% 0.88/1.04  --inst_out_proof                        true
% 0.88/1.04  
% 0.88/1.04  ------ Resolution Options
% 0.88/1.04  
% 0.88/1.04  --resolution_flag                       false
% 0.88/1.04  --res_lit_sel                           adaptive
% 0.88/1.04  --res_lit_sel_side                      none
% 0.88/1.04  --res_ordering                          kbo
% 0.88/1.04  --res_to_prop_solver                    active
% 0.88/1.04  --res_prop_simpl_new                    false
% 0.88/1.04  --res_prop_simpl_given                  true
% 0.88/1.04  --res_passive_queue_type                priority_queues
% 0.88/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.88/1.04  --res_passive_queues_freq               [15;5]
% 0.88/1.04  --res_forward_subs                      full
% 0.88/1.04  --res_backward_subs                     full
% 0.88/1.04  --res_forward_subs_resolution           true
% 0.88/1.04  --res_backward_subs_resolution          true
% 0.88/1.04  --res_orphan_elimination                true
% 0.88/1.04  --res_time_limit                        2.
% 0.88/1.04  --res_out_proof                         true
% 0.88/1.04  
% 0.88/1.04  ------ Superposition Options
% 0.88/1.04  
% 0.88/1.04  --superposition_flag                    true
% 0.88/1.04  --sup_passive_queue_type                priority_queues
% 0.88/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.88/1.04  --sup_passive_queues_freq               [8;1;4]
% 0.88/1.04  --demod_completeness_check              fast
% 0.88/1.04  --demod_use_ground                      true
% 0.88/1.04  --sup_to_prop_solver                    passive
% 0.88/1.04  --sup_prop_simpl_new                    true
% 0.88/1.04  --sup_prop_simpl_given                  true
% 0.88/1.04  --sup_fun_splitting                     false
% 0.88/1.04  --sup_smt_interval                      50000
% 0.88/1.04  
% 0.88/1.04  ------ Superposition Simplification Setup
% 0.88/1.04  
% 0.88/1.04  --sup_indices_passive                   []
% 0.88/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.88/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.88/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.88/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 0.88/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.88/1.04  --sup_full_bw                           [BwDemod]
% 0.88/1.04  --sup_immed_triv                        [TrivRules]
% 0.88/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.88/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.88/1.04  --sup_immed_bw_main                     []
% 0.88/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.88/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 0.88/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.88/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.88/1.04  
% 0.88/1.04  ------ Combination Options
% 0.88/1.04  
% 0.88/1.04  --comb_res_mult                         3
% 0.88/1.04  --comb_sup_mult                         2
% 0.88/1.04  --comb_inst_mult                        10
% 0.88/1.04  
% 0.88/1.04  ------ Debug Options
% 0.88/1.04  
% 0.88/1.04  --dbg_backtrace                         false
% 0.88/1.04  --dbg_dump_prop_clauses                 false
% 0.88/1.04  --dbg_dump_prop_clauses_file            -
% 0.88/1.04  --dbg_out_stat                          false
% 0.88/1.04  
% 0.88/1.04  
% 0.88/1.04  
% 0.88/1.04  
% 0.88/1.04  ------ Proving...
% 0.88/1.04  
% 0.88/1.04  
% 0.88/1.04  % SZS status Theorem for theBenchmark.p
% 0.88/1.04  
% 0.88/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 0.88/1.04  
% 0.88/1.04  fof(f6,conjecture,(
% 0.88/1.04    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) = k6_domain_1(u1_struct_0(X0),X2))) => v2_tex_2(X1,X0))))),
% 0.88/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.88/1.04  
% 0.88/1.04  fof(f7,negated_conjecture,(
% 0.88/1.04    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) = k6_domain_1(u1_struct_0(X0),X2))) => v2_tex_2(X1,X0))))),
% 0.88/1.04    inference(negated_conjecture,[],[f6])).
% 0.88/1.04  
% 0.88/1.04  fof(f16,plain,(
% 0.88/1.04    ? [X0] : (? [X1] : ((~v2_tex_2(X1,X0) & ! [X2] : ((k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) = k6_domain_1(u1_struct_0(X0),X2) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.88/1.04    inference(ennf_transformation,[],[f7])).
% 0.88/1.04  
% 0.88/1.04  fof(f17,plain,(
% 0.88/1.04    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) = k6_domain_1(u1_struct_0(X0),X2) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.88/1.04    inference(flattening,[],[f16])).
% 0.88/1.04  
% 0.88/1.04  fof(f21,plain,(
% 0.88/1.04    ( ! [X0] : (? [X1] : (~v2_tex_2(X1,X0) & ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) = k6_domain_1(u1_struct_0(X0),X2) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v2_tex_2(sK2,X0) & ! [X2] : (k9_subset_1(u1_struct_0(X0),sK2,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) = k6_domain_1(u1_struct_0(X0),X2) | ~r2_hidden(X2,sK2) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 0.88/1.04    introduced(choice_axiom,[])).
% 0.88/1.04  
% 0.88/1.04  fof(f20,plain,(
% 0.88/1.04    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) = k6_domain_1(u1_struct_0(X0),X2) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v2_tex_2(X1,sK1) & ! [X2] : (k9_subset_1(u1_struct_0(sK1),X1,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X2))) = k6_domain_1(u1_struct_0(sK1),X2) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(sK1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v3_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.88/1.04    introduced(choice_axiom,[])).
% 0.88/1.04  
% 0.88/1.04  fof(f22,plain,(
% 0.88/1.04    (~v2_tex_2(sK2,sK1) & ! [X2] : (k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X2))) = k6_domain_1(u1_struct_0(sK1),X2) | ~r2_hidden(X2,sK2) | ~m1_subset_1(X2,u1_struct_0(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v3_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 0.88/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f17,f21,f20])).
% 0.88/1.04  
% 0.88/1.04  fof(f36,plain,(
% 0.88/1.04    ~v2_tex_2(sK2,sK1)),
% 0.88/1.04    inference(cnf_transformation,[],[f22])).
% 0.88/1.04  
% 0.88/1.04  fof(f5,axiom,(
% 0.88/1.04    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k6_domain_1(u1_struct_0(X0),X2) & v4_pre_topc(X3,X0))) & r2_hidden(X2,X1))) => v2_tex_2(X1,X0))))),
% 0.88/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.88/1.04  
% 0.88/1.04  fof(f14,plain,(
% 0.88/1.04    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) | ? [X2] : ((! [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2) | ~v4_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.88/1.04    inference(ennf_transformation,[],[f5])).
% 0.88/1.04  
% 0.88/1.04  fof(f15,plain,(
% 0.88/1.04    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.88/1.04    inference(flattening,[],[f14])).
% 0.88/1.04  
% 0.88/1.04  fof(f18,plain,(
% 0.88/1.04    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK0(X0,X1)) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),u1_struct_0(X0))))),
% 0.88/1.04    introduced(choice_axiom,[])).
% 0.88/1.04  
% 0.88/1.04  fof(f19,plain,(
% 0.88/1.04    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK0(X0,X1)) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.88/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f18])).
% 0.88/1.04  
% 0.88/1.04  fof(f27,plain,(
% 0.88/1.04    ( ! [X0,X1] : (v2_tex_2(X1,X0) | m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.88/1.04    inference(cnf_transformation,[],[f19])).
% 0.88/1.04  
% 0.88/1.04  fof(f31,plain,(
% 0.88/1.04    v2_pre_topc(sK1)),
% 0.88/1.04    inference(cnf_transformation,[],[f22])).
% 0.88/1.04  
% 0.88/1.04  fof(f30,plain,(
% 0.88/1.04    ~v2_struct_0(sK1)),
% 0.88/1.04    inference(cnf_transformation,[],[f22])).
% 0.88/1.04  
% 0.88/1.04  fof(f32,plain,(
% 0.88/1.04    v3_tdlat_3(sK1)),
% 0.88/1.04    inference(cnf_transformation,[],[f22])).
% 0.88/1.04  
% 0.88/1.04  fof(f33,plain,(
% 0.88/1.04    l1_pre_topc(sK1)),
% 0.88/1.04    inference(cnf_transformation,[],[f22])).
% 0.88/1.04  
% 0.88/1.04  fof(f34,plain,(
% 0.88/1.04    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.88/1.04    inference(cnf_transformation,[],[f22])).
% 0.88/1.04  
% 0.88/1.04  fof(f28,plain,(
% 0.88/1.04    ( ! [X0,X1] : (v2_tex_2(X1,X0) | r2_hidden(sK0(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.88/1.04    inference(cnf_transformation,[],[f19])).
% 0.88/1.04  
% 0.88/1.04  fof(f35,plain,(
% 0.88/1.04    ( ! [X2] : (k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X2))) = k6_domain_1(u1_struct_0(sK1),X2) | ~r2_hidden(X2,sK2) | ~m1_subset_1(X2,u1_struct_0(sK1))) )),
% 0.88/1.04    inference(cnf_transformation,[],[f22])).
% 0.88/1.04  
% 0.88/1.04  fof(f1,axiom,(
% 0.88/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 0.88/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.88/1.04  
% 0.88/1.04  fof(f8,plain,(
% 0.88/1.04    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.88/1.04    inference(ennf_transformation,[],[f1])).
% 0.88/1.04  
% 0.88/1.04  fof(f23,plain,(
% 0.88/1.04    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.88/1.04    inference(cnf_transformation,[],[f8])).
% 0.88/1.04  
% 0.88/1.04  fof(f2,axiom,(
% 0.88/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.88/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.88/1.04  
% 0.88/1.04  fof(f9,plain,(
% 0.88/1.04    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.88/1.04    inference(ennf_transformation,[],[f2])).
% 0.88/1.04  
% 0.88/1.04  fof(f24,plain,(
% 0.88/1.04    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.88/1.04    inference(cnf_transformation,[],[f9])).
% 0.88/1.04  
% 0.88/1.04  fof(f4,axiom,(
% 0.88/1.04    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 0.88/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.88/1.04  
% 0.88/1.04  fof(f12,plain,(
% 0.88/1.04    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.88/1.04    inference(ennf_transformation,[],[f4])).
% 0.88/1.04  
% 0.88/1.04  fof(f13,plain,(
% 0.88/1.04    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.88/1.04    inference(flattening,[],[f12])).
% 0.88/1.04  
% 0.88/1.04  fof(f26,plain,(
% 0.88/1.04    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.88/1.04    inference(cnf_transformation,[],[f13])).
% 0.88/1.04  
% 0.88/1.04  fof(f29,plain,(
% 0.88/1.04    ( ! [X0,X3,X1] : (v2_tex_2(X1,X0) | k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK0(X0,X1)) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.88/1.04    inference(cnf_transformation,[],[f19])).
% 0.88/1.04  
% 0.88/1.04  fof(f3,axiom,(
% 0.88/1.04    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.88/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.88/1.04  
% 0.88/1.04  fof(f10,plain,(
% 0.88/1.04    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.88/1.04    inference(ennf_transformation,[],[f3])).
% 0.88/1.04  
% 0.88/1.04  fof(f11,plain,(
% 0.88/1.04    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.88/1.04    inference(flattening,[],[f10])).
% 0.88/1.04  
% 0.88/1.04  fof(f25,plain,(
% 0.88/1.04    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.88/1.04    inference(cnf_transformation,[],[f11])).
% 0.88/1.04  
% 0.88/1.04  cnf(c_7,negated_conjecture,
% 0.88/1.04      ( ~ v2_tex_2(sK2,sK1) ),
% 0.88/1.04      inference(cnf_transformation,[],[f36]) ).
% 0.88/1.04  
% 0.88/1.04  cnf(c_6,plain,
% 0.88/1.04      ( v2_tex_2(X0,X1)
% 0.88/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.88/1.04      | m1_subset_1(sK0(X1,X0),u1_struct_0(X1))
% 0.88/1.04      | v2_struct_0(X1)
% 0.88/1.04      | ~ v3_tdlat_3(X1)
% 0.88/1.04      | ~ v2_pre_topc(X1)
% 0.88/1.04      | ~ l1_pre_topc(X1) ),
% 0.88/1.04      inference(cnf_transformation,[],[f27]) ).
% 0.88/1.04  
% 0.88/1.04  cnf(c_12,negated_conjecture,
% 0.88/1.04      ( v2_pre_topc(sK1) ),
% 0.88/1.04      inference(cnf_transformation,[],[f31]) ).
% 0.88/1.04  
% 0.88/1.04  cnf(c_281,plain,
% 0.88/1.04      ( v2_tex_2(X0,X1)
% 0.88/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.88/1.04      | m1_subset_1(sK0(X1,X0),u1_struct_0(X1))
% 0.88/1.04      | v2_struct_0(X1)
% 0.88/1.04      | ~ v3_tdlat_3(X1)
% 0.88/1.04      | ~ l1_pre_topc(X1)
% 0.88/1.04      | sK1 != X1 ),
% 0.88/1.04      inference(resolution_lifted,[status(thm)],[c_6,c_12]) ).
% 0.88/1.04  
% 0.88/1.04  cnf(c_282,plain,
% 0.88/1.04      ( v2_tex_2(X0,sK1)
% 0.88/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.88/1.04      | m1_subset_1(sK0(sK1,X0),u1_struct_0(sK1))
% 0.88/1.04      | v2_struct_0(sK1)
% 0.88/1.04      | ~ v3_tdlat_3(sK1)
% 0.88/1.04      | ~ l1_pre_topc(sK1) ),
% 0.88/1.04      inference(unflattening,[status(thm)],[c_281]) ).
% 0.88/1.04  
% 0.88/1.04  cnf(c_13,negated_conjecture,
% 0.88/1.04      ( ~ v2_struct_0(sK1) ),
% 0.88/1.04      inference(cnf_transformation,[],[f30]) ).
% 0.88/1.04  
% 0.88/1.04  cnf(c_11,negated_conjecture,
% 0.88/1.04      ( v3_tdlat_3(sK1) ),
% 0.88/1.04      inference(cnf_transformation,[],[f32]) ).
% 0.88/1.04  
% 0.88/1.04  cnf(c_10,negated_conjecture,
% 0.88/1.04      ( l1_pre_topc(sK1) ),
% 0.88/1.04      inference(cnf_transformation,[],[f33]) ).
% 0.88/1.04  
% 0.88/1.04  cnf(c_286,plain,
% 0.88/1.04      ( m1_subset_1(sK0(sK1,X0),u1_struct_0(sK1))
% 0.88/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.88/1.04      | v2_tex_2(X0,sK1) ),
% 0.88/1.04      inference(global_propositional_subsumption,
% 0.88/1.04                [status(thm)],
% 0.88/1.04                [c_282,c_13,c_11,c_10]) ).
% 0.88/1.04  
% 0.88/1.04  cnf(c_287,plain,
% 0.88/1.04      ( v2_tex_2(X0,sK1)
% 0.88/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.88/1.04      | m1_subset_1(sK0(sK1,X0),u1_struct_0(sK1)) ),
% 0.88/1.04      inference(renaming,[status(thm)],[c_286]) ).
% 0.88/1.04  
% 0.88/1.04  cnf(c_329,plain,
% 0.88/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.88/1.04      | m1_subset_1(sK0(sK1,X0),u1_struct_0(sK1))
% 0.88/1.04      | sK1 != sK1
% 0.88/1.04      | sK2 != X0 ),
% 0.88/1.04      inference(resolution_lifted,[status(thm)],[c_7,c_287]) ).
% 0.88/1.04  
% 0.88/1.04  cnf(c_330,plain,
% 0.88/1.04      ( m1_subset_1(sK0(sK1,sK2),u1_struct_0(sK1))
% 0.88/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 0.88/1.04      inference(unflattening,[status(thm)],[c_329]) ).
% 0.88/1.04  
% 0.88/1.04  cnf(c_9,negated_conjecture,
% 0.88/1.04      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 0.88/1.04      inference(cnf_transformation,[],[f34]) ).
% 0.88/1.04  
% 0.88/1.04  cnf(c_332,plain,
% 0.88/1.04      ( m1_subset_1(sK0(sK1,sK2),u1_struct_0(sK1)) ),
% 0.88/1.04      inference(global_propositional_subsumption,
% 0.88/1.04                [status(thm)],
% 0.88/1.04                [c_330,c_9]) ).
% 0.88/1.04  
% 0.88/1.04  cnf(c_5,plain,
% 0.88/1.04      ( r2_hidden(sK0(X0,X1),X1)
% 0.88/1.04      | v2_tex_2(X1,X0)
% 0.88/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 0.88/1.04      | v2_struct_0(X0)
% 0.88/1.04      | ~ v3_tdlat_3(X0)
% 0.88/1.04      | ~ v2_pre_topc(X0)
% 0.88/1.04      | ~ l1_pre_topc(X0) ),
% 0.88/1.04      inference(cnf_transformation,[],[f28]) ).
% 0.88/1.04  
% 0.88/1.04  cnf(c_8,negated_conjecture,
% 0.88/1.04      ( ~ r2_hidden(X0,sK2)
% 0.88/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 0.88/1.04      | k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0))) = k6_domain_1(u1_struct_0(sK1),X0) ),
% 0.88/1.04      inference(cnf_transformation,[],[f35]) ).
% 0.88/1.04  
% 0.88/1.04  cnf(c_160,plain,
% 0.88/1.04      ( v2_tex_2(X0,X1)
% 0.88/1.04      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 0.88/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.88/1.04      | v2_struct_0(X1)
% 0.88/1.04      | ~ v3_tdlat_3(X1)
% 0.88/1.04      | ~ v2_pre_topc(X1)
% 0.88/1.04      | ~ l1_pre_topc(X1)
% 0.88/1.04      | k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X2))) = k6_domain_1(u1_struct_0(sK1),X2)
% 0.88/1.04      | sK0(X1,X0) != X2
% 0.88/1.04      | sK2 != X0 ),
% 0.88/1.04      inference(resolution_lifted,[status(thm)],[c_5,c_8]) ).
% 0.88/1.04  
% 0.88/1.04  cnf(c_161,plain,
% 0.88/1.04      ( v2_tex_2(sK2,X0)
% 0.88/1.04      | ~ m1_subset_1(sK0(X0,sK2),u1_struct_0(sK1))
% 0.88/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
% 0.88/1.04      | v2_struct_0(X0)
% 0.88/1.04      | ~ v3_tdlat_3(X0)
% 0.88/1.04      | ~ v2_pre_topc(X0)
% 0.88/1.04      | ~ l1_pre_topc(X0)
% 0.88/1.04      | k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK0(X0,sK2)))) = k6_domain_1(u1_struct_0(sK1),sK0(X0,sK2)) ),
% 0.88/1.04      inference(unflattening,[status(thm)],[c_160]) ).
% 0.88/1.04  
% 0.88/1.04  cnf(c_243,plain,
% 0.88/1.04      ( v2_tex_2(sK2,X0)
% 0.88/1.04      | ~ m1_subset_1(sK0(X0,sK2),u1_struct_0(sK1))
% 0.88/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
% 0.88/1.04      | v2_struct_0(X0)
% 0.88/1.04      | ~ v3_tdlat_3(X0)
% 0.88/1.04      | ~ l1_pre_topc(X0)
% 0.88/1.04      | k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK0(X0,sK2)))) = k6_domain_1(u1_struct_0(sK1),sK0(X0,sK2))
% 0.88/1.04      | sK1 != X0 ),
% 0.88/1.04      inference(resolution_lifted,[status(thm)],[c_161,c_12]) ).
% 0.88/1.04  
% 0.88/1.04  cnf(c_244,plain,
% 0.88/1.04      ( v2_tex_2(sK2,sK1)
% 0.88/1.04      | ~ m1_subset_1(sK0(sK1,sK2),u1_struct_0(sK1))
% 0.88/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.88/1.04      | v2_struct_0(sK1)
% 0.88/1.04      | ~ v3_tdlat_3(sK1)
% 0.88/1.04      | ~ l1_pre_topc(sK1)
% 0.88/1.04      | k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)))) = k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)) ),
% 0.88/1.04      inference(unflattening,[status(thm)],[c_243]) ).
% 0.88/1.04  
% 0.88/1.04  cnf(c_246,plain,
% 0.88/1.04      ( ~ m1_subset_1(sK0(sK1,sK2),u1_struct_0(sK1))
% 0.88/1.04      | k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)))) = k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)) ),
% 0.88/1.04      inference(global_propositional_subsumption,
% 0.88/1.04                [status(thm)],
% 0.88/1.04                [c_244,c_13,c_11,c_10,c_9,c_7]) ).
% 0.88/1.04  
% 0.88/1.04  cnf(c_359,plain,
% 0.88/1.04      ( k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)))) = k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)) ),
% 0.88/1.04      inference(backward_subsumption_resolution,
% 0.88/1.04                [status(thm)],
% 0.88/1.04                [c_332,c_246]) ).
% 0.88/1.04  
% 0.88/1.04  cnf(c_414,plain,
% 0.88/1.04      ( k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)))) = k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)) ),
% 0.88/1.04      inference(subtyping,[status(esa)],[c_359]) ).
% 0.88/1.04  
% 0.88/1.04  cnf(c_418,negated_conjecture,
% 0.88/1.04      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 0.88/1.04      inference(subtyping,[status(esa)],[c_9]) ).
% 0.88/1.04  
% 0.88/1.04  cnf(c_551,plain,
% 0.88/1.04      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 0.88/1.04      inference(predicate_to_equality,[status(thm)],[c_418]) ).
% 0.88/1.04  
% 0.88/1.04  cnf(c_0,plain,
% 0.88/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 0.88/1.04      | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
% 0.88/1.04      inference(cnf_transformation,[],[f23]) ).
% 0.88/1.04  
% 0.88/1.04  cnf(c_420,plain,
% 0.88/1.04      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X0_45))
% 0.88/1.04      | k9_subset_1(X0_45,X0_44,X1_44) = k9_subset_1(X0_45,X1_44,X0_44) ),
% 0.88/1.04      inference(subtyping,[status(esa)],[c_0]) ).
% 0.88/1.04  
% 0.88/1.04  cnf(c_549,plain,
% 0.88/1.04      ( k9_subset_1(X0_45,X0_44,X1_44) = k9_subset_1(X0_45,X1_44,X0_44)
% 0.88/1.04      | m1_subset_1(X0_44,k1_zfmisc_1(X0_45)) != iProver_top ),
% 0.88/1.04      inference(predicate_to_equality,[status(thm)],[c_420]) ).
% 0.88/1.04  
% 0.88/1.04  cnf(c_739,plain,
% 0.88/1.04      ( k9_subset_1(u1_struct_0(sK1),sK2,X0_44) = k9_subset_1(u1_struct_0(sK1),X0_44,sK2) ),
% 0.88/1.04      inference(superposition,[status(thm)],[c_551,c_549]) ).
% 0.88/1.04  
% 0.88/1.04  cnf(c_1,plain,
% 0.88/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 0.88/1.04      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 0.88/1.04      inference(cnf_transformation,[],[f24]) ).
% 0.88/1.04  
% 0.88/1.04  cnf(c_419,plain,
% 0.88/1.04      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X0_45))
% 0.88/1.04      | m1_subset_1(k9_subset_1(X0_45,X1_44,X0_44),k1_zfmisc_1(X0_45)) ),
% 0.88/1.04      inference(subtyping,[status(esa)],[c_1]) ).
% 0.88/1.04  
% 0.88/1.04  cnf(c_550,plain,
% 0.88/1.04      ( m1_subset_1(X0_44,k1_zfmisc_1(X0_45)) != iProver_top
% 0.88/1.04      | m1_subset_1(k9_subset_1(X0_45,X1_44,X0_44),k1_zfmisc_1(X0_45)) = iProver_top ),
% 0.88/1.04      inference(predicate_to_equality,[status(thm)],[c_419]) ).
% 0.88/1.04  
% 0.88/1.04  cnf(c_824,plain,
% 0.88/1.04      ( m1_subset_1(k9_subset_1(u1_struct_0(sK1),sK2,X0_44),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 0.88/1.04      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 0.88/1.04      inference(superposition,[status(thm)],[c_739,c_550]) ).
% 0.88/1.04  
% 0.88/1.04  cnf(c_18,plain,
% 0.88/1.04      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 0.88/1.04      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 0.88/1.04  
% 0.88/1.04  cnf(c_850,plain,
% 0.88/1.04      ( m1_subset_1(k9_subset_1(u1_struct_0(sK1),sK2,X0_44),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 0.88/1.04      inference(global_propositional_subsumption,
% 0.88/1.04                [status(thm)],
% 0.88/1.04                [c_824,c_18]) ).
% 0.88/1.04  
% 0.88/1.04  cnf(c_857,plain,
% 0.88/1.04      ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 0.88/1.04      inference(superposition,[status(thm)],[c_414,c_850]) ).
% 0.88/1.04  
% 0.88/1.04  cnf(c_3,plain,
% 0.88/1.04      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
% 0.88/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 0.88/1.04      | ~ v2_pre_topc(X0)
% 0.88/1.04      | ~ l1_pre_topc(X0) ),
% 0.88/1.04      inference(cnf_transformation,[],[f26]) ).
% 0.88/1.04  
% 0.88/1.04  cnf(c_4,plain,
% 0.88/1.04      ( v2_tex_2(X0,X1)
% 0.88/1.04      | ~ v4_pre_topc(X2,X1)
% 0.88/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.88/1.04      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 0.88/1.04      | v2_struct_0(X1)
% 0.88/1.04      | ~ v3_tdlat_3(X1)
% 0.88/1.04      | ~ v2_pre_topc(X1)
% 0.88/1.04      | ~ l1_pre_topc(X1)
% 0.88/1.04      | k6_domain_1(u1_struct_0(X1),sK0(X1,X0)) != k9_subset_1(u1_struct_0(X1),X0,X2) ),
% 0.88/1.04      inference(cnf_transformation,[],[f29]) ).
% 0.88/1.04  
% 0.88/1.04  cnf(c_199,plain,
% 0.88/1.04      ( v2_tex_2(X0,X1)
% 0.88/1.04      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 0.88/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.88/1.04      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
% 0.88/1.04      | v2_struct_0(X1)
% 0.88/1.04      | ~ v3_tdlat_3(X1)
% 0.88/1.04      | ~ v2_pre_topc(X3)
% 0.88/1.04      | ~ v2_pre_topc(X1)
% 0.88/1.04      | ~ l1_pre_topc(X3)
% 0.88/1.04      | ~ l1_pre_topc(X1)
% 0.88/1.04      | X1 != X3
% 0.88/1.04      | k6_domain_1(u1_struct_0(X1),sK0(X1,X0)) != k9_subset_1(u1_struct_0(X1),X0,X4)
% 0.88/1.04      | k2_pre_topc(X3,X2) != X4 ),
% 0.88/1.04      inference(resolution_lifted,[status(thm)],[c_3,c_4]) ).
% 0.88/1.04  
% 0.88/1.04  cnf(c_200,plain,
% 0.88/1.04      ( v2_tex_2(X0,X1)
% 0.88/1.04      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 0.88/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.88/1.04      | ~ m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 0.88/1.04      | v2_struct_0(X1)
% 0.88/1.04      | ~ v3_tdlat_3(X1)
% 0.88/1.04      | ~ v2_pre_topc(X1)
% 0.88/1.04      | ~ l1_pre_topc(X1)
% 0.88/1.04      | k6_domain_1(u1_struct_0(X1),sK0(X1,X0)) != k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) ),
% 0.88/1.04      inference(unflattening,[status(thm)],[c_199]) ).
% 0.88/1.04  
% 0.88/1.04  cnf(c_2,plain,
% 0.88/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.88/1.04      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 0.88/1.04      | ~ l1_pre_topc(X1) ),
% 0.88/1.04      inference(cnf_transformation,[],[f25]) ).
% 0.88/1.04  
% 0.88/1.04  cnf(c_222,plain,
% 0.88/1.04      ( v2_tex_2(X0,X1)
% 0.88/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.88/1.04      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 0.88/1.04      | v2_struct_0(X1)
% 0.88/1.04      | ~ v3_tdlat_3(X1)
% 0.88/1.04      | ~ v2_pre_topc(X1)
% 0.88/1.04      | ~ l1_pre_topc(X1)
% 0.88/1.04      | k6_domain_1(u1_struct_0(X1),sK0(X1,X0)) != k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) ),
% 0.88/1.04      inference(forward_subsumption_resolution,[status(thm)],[c_200,c_2]) ).
% 0.88/1.04  
% 0.88/1.04  cnf(c_257,plain,
% 0.88/1.04      ( v2_tex_2(X0,X1)
% 0.88/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.88/1.04      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 0.88/1.04      | v2_struct_0(X1)
% 0.88/1.04      | ~ v3_tdlat_3(X1)
% 0.88/1.04      | ~ l1_pre_topc(X1)
% 0.88/1.04      | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) != k6_domain_1(u1_struct_0(X1),sK0(X1,X0))
% 0.88/1.04      | sK1 != X1 ),
% 0.88/1.04      inference(resolution_lifted,[status(thm)],[c_222,c_12]) ).
% 0.88/1.04  
% 0.88/1.04  cnf(c_258,plain,
% 0.88/1.04      ( v2_tex_2(X0,sK1)
% 0.88/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.88/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.88/1.04      | v2_struct_0(sK1)
% 0.88/1.04      | ~ v3_tdlat_3(sK1)
% 0.88/1.04      | ~ l1_pre_topc(sK1)
% 0.88/1.04      | k9_subset_1(u1_struct_0(sK1),X0,k2_pre_topc(sK1,X1)) != k6_domain_1(u1_struct_0(sK1),sK0(sK1,X0)) ),
% 0.88/1.04      inference(unflattening,[status(thm)],[c_257]) ).
% 0.88/1.04  
% 0.88/1.04  cnf(c_262,plain,
% 0.88/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.88/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.88/1.04      | v2_tex_2(X0,sK1)
% 0.88/1.04      | k9_subset_1(u1_struct_0(sK1),X0,k2_pre_topc(sK1,X1)) != k6_domain_1(u1_struct_0(sK1),sK0(sK1,X0)) ),
% 0.88/1.04      inference(global_propositional_subsumption,
% 0.88/1.04                [status(thm)],
% 0.88/1.04                [c_258,c_13,c_11,c_10]) ).
% 0.88/1.04  
% 0.88/1.04  cnf(c_263,plain,
% 0.88/1.04      ( v2_tex_2(X0,sK1)
% 0.88/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.88/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.88/1.04      | k9_subset_1(u1_struct_0(sK1),X0,k2_pre_topc(sK1,X1)) != k6_domain_1(u1_struct_0(sK1),sK0(sK1,X0)) ),
% 0.88/1.04      inference(renaming,[status(thm)],[c_262]) ).
% 0.88/1.04  
% 0.88/1.04  cnf(c_340,plain,
% 0.88/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.88/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.88/1.04      | k9_subset_1(u1_struct_0(sK1),X0,k2_pre_topc(sK1,X1)) != k6_domain_1(u1_struct_0(sK1),sK0(sK1,X0))
% 0.88/1.04      | sK1 != sK1
% 0.88/1.04      | sK2 != X0 ),
% 0.88/1.04      inference(resolution_lifted,[status(thm)],[c_7,c_263]) ).
% 0.88/1.04  
% 0.88/1.04  cnf(c_341,plain,
% 0.88/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.88/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.88/1.04      | k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,X0)) != k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)) ),
% 0.88/1.04      inference(unflattening,[status(thm)],[c_340]) ).
% 0.88/1.04  
% 0.88/1.04  cnf(c_345,plain,
% 0.88/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.88/1.04      | k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,X0)) != k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)) ),
% 0.88/1.04      inference(global_propositional_subsumption,
% 0.88/1.04                [status(thm)],
% 0.88/1.04                [c_341,c_9]) ).
% 0.88/1.04  
% 0.88/1.04  cnf(c_415,plain,
% 0.88/1.04      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.88/1.04      | k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,X0_44)) != k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)) ),
% 0.88/1.04      inference(subtyping,[status(esa)],[c_345]) ).
% 0.88/1.04  
% 0.88/1.04  cnf(c_590,plain,
% 0.88/1.04      ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
% 0.88/1.04      | k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)))) != k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)) ),
% 0.88/1.04      inference(instantiation,[status(thm)],[c_415]) ).
% 0.88/1.04  
% 0.88/1.04  cnf(c_591,plain,
% 0.88/1.04      ( k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)))) != k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2))
% 0.88/1.04      | m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 0.88/1.04      inference(predicate_to_equality,[status(thm)],[c_590]) ).
% 0.88/1.04  
% 0.88/1.04  cnf(contradiction,plain,
% 0.88/1.04      ( $false ),
% 0.88/1.04      inference(minisat,[status(thm)],[c_857,c_591,c_414]) ).
% 0.88/1.04  
% 0.88/1.04  
% 0.88/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 0.88/1.04  
% 0.88/1.04  ------                               Statistics
% 0.88/1.04  
% 0.88/1.04  ------ General
% 0.88/1.04  
% 0.88/1.04  abstr_ref_over_cycles:                  0
% 0.88/1.04  abstr_ref_under_cycles:                 0
% 0.88/1.04  gc_basic_clause_elim:                   0
% 0.88/1.04  forced_gc_time:                         0
% 0.88/1.04  parsing_time:                           0.007
% 0.88/1.04  unif_index_cands_time:                  0.
% 0.88/1.04  unif_index_add_time:                    0.
% 0.88/1.04  orderings_time:                         0.
% 0.88/1.04  out_proof_time:                         0.007
% 0.88/1.04  total_time:                             0.048
% 0.88/1.04  num_of_symbols:                         47
% 0.88/1.04  num_of_terms:                           1051
% 0.88/1.04  
% 0.88/1.04  ------ Preprocessing
% 0.88/1.04  
% 0.88/1.04  num_of_splits:                          0
% 0.88/1.04  num_of_split_atoms:                     0
% 0.88/1.04  num_of_reused_defs:                     0
% 0.88/1.04  num_eq_ax_congr_red:                    10
% 0.88/1.04  num_of_sem_filtered_clauses:            1
% 0.88/1.04  num_of_subtypes:                        3
% 0.88/1.04  monotx_restored_types:                  0
% 0.88/1.04  sat_num_of_epr_types:                   0
% 0.88/1.04  sat_num_of_non_cyclic_types:            0
% 0.88/1.04  sat_guarded_non_collapsed_types:        0
% 0.88/1.04  num_pure_diseq_elim:                    0
% 0.88/1.04  simp_replaced_by:                       0
% 0.88/1.04  res_preprocessed:                       50
% 0.88/1.04  prep_upred:                             0
% 0.88/1.04  prep_unflattend:                        10
% 0.88/1.04  smt_new_axioms:                         0
% 0.88/1.04  pred_elim_cands:                        1
% 0.88/1.04  pred_elim:                              7
% 0.88/1.04  pred_elim_cl:                           7
% 0.88/1.04  pred_elim_cycles:                       9
% 0.88/1.04  merged_defs:                            0
% 0.88/1.04  merged_defs_ncl:                        0
% 0.88/1.04  bin_hyper_res:                          0
% 0.88/1.04  prep_cycles:                            4
% 0.88/1.04  pred_elim_time:                         0.004
% 0.88/1.04  splitting_time:                         0.
% 0.88/1.04  sem_filter_time:                        0.
% 0.88/1.04  monotx_time:                            0.
% 0.88/1.04  subtype_inf_time:                       0.
% 0.88/1.04  
% 0.88/1.04  ------ Problem properties
% 0.88/1.04  
% 0.88/1.04  clauses:                                7
% 0.88/1.04  conjectures:                            1
% 0.88/1.04  epr:                                    0
% 0.88/1.04  horn:                                   7
% 0.88/1.04  ground:                                 3
% 0.88/1.04  unary:                                  3
% 0.88/1.04  binary:                                 4
% 0.88/1.04  lits:                                   11
% 0.88/1.04  lits_eq:                                3
% 0.88/1.04  fd_pure:                                0
% 0.88/1.04  fd_pseudo:                              0
% 0.88/1.04  fd_cond:                                0
% 0.88/1.04  fd_pseudo_cond:                         0
% 0.88/1.04  ac_symbols:                             0
% 0.88/1.04  
% 0.88/1.04  ------ Propositional Solver
% 0.88/1.04  
% 0.88/1.04  prop_solver_calls:                      26
% 0.88/1.04  prop_fast_solver_calls:                 290
% 0.88/1.04  smt_solver_calls:                       0
% 0.88/1.04  smt_fast_solver_calls:                  0
% 0.88/1.04  prop_num_of_clauses:                    250
% 0.88/1.04  prop_preprocess_simplified:             1412
% 0.88/1.04  prop_fo_subsumed:                       14
% 0.88/1.04  prop_solver_time:                       0.
% 0.88/1.04  smt_solver_time:                        0.
% 0.88/1.04  smt_fast_solver_time:                   0.
% 0.88/1.04  prop_fast_solver_time:                  0.
% 0.88/1.04  prop_unsat_core_time:                   0.
% 0.88/1.04  
% 0.88/1.04  ------ QBF
% 0.88/1.04  
% 0.88/1.04  qbf_q_res:                              0
% 0.88/1.04  qbf_num_tautologies:                    0
% 0.88/1.04  qbf_prep_cycles:                        0
% 0.88/1.04  
% 0.88/1.04  ------ BMC1
% 0.88/1.04  
% 0.88/1.04  bmc1_current_bound:                     -1
% 0.88/1.04  bmc1_last_solved_bound:                 -1
% 0.88/1.04  bmc1_unsat_core_size:                   -1
% 0.88/1.04  bmc1_unsat_core_parents_size:           -1
% 0.88/1.04  bmc1_merge_next_fun:                    0
% 0.88/1.04  bmc1_unsat_core_clauses_time:           0.
% 0.88/1.04  
% 0.88/1.04  ------ Instantiation
% 0.88/1.04  
% 0.88/1.04  inst_num_of_clauses:                    68
% 0.88/1.04  inst_num_in_passive:                    18
% 0.88/1.04  inst_num_in_active:                     47
% 0.88/1.04  inst_num_in_unprocessed:                3
% 0.88/1.04  inst_num_of_loops:                      50
% 0.88/1.04  inst_num_of_learning_restarts:          0
% 0.88/1.04  inst_num_moves_active_passive:          0
% 0.88/1.04  inst_lit_activity:                      0
% 0.88/1.04  inst_lit_activity_moves:                0
% 0.88/1.04  inst_num_tautologies:                   0
% 0.88/1.04  inst_num_prop_implied:                  0
% 0.88/1.04  inst_num_existing_simplified:           0
% 0.88/1.04  inst_num_eq_res_simplified:             0
% 0.88/1.04  inst_num_child_elim:                    0
% 0.88/1.04  inst_num_of_dismatching_blockings:      11
% 0.88/1.04  inst_num_of_non_proper_insts:           65
% 0.88/1.04  inst_num_of_duplicates:                 0
% 0.88/1.04  inst_inst_num_from_inst_to_res:         0
% 0.88/1.04  inst_dismatching_checking_time:         0.
% 0.88/1.04  
% 0.88/1.04  ------ Resolution
% 0.88/1.04  
% 0.88/1.04  res_num_of_clauses:                     0
% 0.88/1.04  res_num_in_passive:                     0
% 0.88/1.04  res_num_in_active:                      0
% 0.88/1.04  res_num_of_loops:                       54
% 0.88/1.04  res_forward_subset_subsumed:            11
% 0.88/1.04  res_backward_subset_subsumed:           2
% 0.88/1.04  res_forward_subsumed:                   0
% 0.88/1.04  res_backward_subsumed:                  0
% 0.88/1.04  res_forward_subsumption_resolution:     1
% 0.88/1.04  res_backward_subsumption_resolution:    1
% 0.88/1.04  res_clause_to_clause_subsumption:       31
% 0.88/1.04  res_orphan_elimination:                 0
% 0.88/1.04  res_tautology_del:                      11
% 0.88/1.04  res_num_eq_res_simplified:              0
% 0.88/1.04  res_num_sel_changes:                    0
% 0.88/1.04  res_moves_from_active_to_pass:          0
% 0.88/1.04  
% 0.88/1.04  ------ Superposition
% 0.88/1.04  
% 0.88/1.04  sup_time_total:                         0.
% 0.88/1.04  sup_time_generating:                    0.
% 0.88/1.04  sup_time_sim_full:                      0.
% 0.88/1.04  sup_time_sim_immed:                     0.
% 0.88/1.04  
% 0.88/1.04  sup_num_of_clauses:                     14
% 0.88/1.04  sup_num_in_active:                      10
% 0.88/1.04  sup_num_in_passive:                     4
% 0.88/1.04  sup_num_of_loops:                       9
% 0.88/1.04  sup_fw_superposition:                   8
% 0.88/1.04  sup_bw_superposition:                   2
% 0.88/1.04  sup_immediate_simplified:               0
% 0.88/1.04  sup_given_eliminated:                   0
% 0.88/1.04  comparisons_done:                       0
% 0.88/1.04  comparisons_avoided:                    0
% 0.88/1.04  
% 0.88/1.04  ------ Simplifications
% 0.88/1.04  
% 0.88/1.04  
% 0.88/1.04  sim_fw_subset_subsumed:                 0
% 0.88/1.04  sim_bw_subset_subsumed:                 1
% 0.88/1.04  sim_fw_subsumed:                        0
% 0.88/1.04  sim_bw_subsumed:                        0
% 0.88/1.04  sim_fw_subsumption_res:                 0
% 0.88/1.04  sim_bw_subsumption_res:                 0
% 0.88/1.04  sim_tautology_del:                      0
% 0.88/1.04  sim_eq_tautology_del:                   0
% 0.88/1.04  sim_eq_res_simp:                        0
% 0.88/1.04  sim_fw_demodulated:                     0
% 0.88/1.04  sim_bw_demodulated:                     0
% 0.88/1.04  sim_light_normalised:                   0
% 0.88/1.04  sim_joinable_taut:                      0
% 0.88/1.04  sim_joinable_simp:                      0
% 0.88/1.04  sim_ac_normalised:                      0
% 0.88/1.04  sim_smt_subsumption:                    0
% 0.88/1.04  
%------------------------------------------------------------------------------
