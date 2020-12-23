%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1890+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:49 EST 2020

% Result     : Theorem 1.15s
% Output     : CNFRefutation 1.15s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 572 expanded)
%              Number of clauses        :   62 ( 134 expanded)
%              Number of leaves         :    9 ( 161 expanded)
%              Depth                    :   19
%              Number of atoms          :  418 (4358 expanded)
%              Number of equality atoms :   74 ( 556 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   18 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
                 => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) = k6_domain_1(u1_struct_0(X0),X2) ) )
           => v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
                   => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) = k6_domain_1(u1_struct_0(X0),X2) ) )
             => v2_tex_2(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f24,plain,(
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

fof(f23,plain,
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

fof(f25,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f20,f24,f23])).

fof(f39,plain,(
    ! [X2] :
      ( k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X2))) = k6_domain_1(u1_struct_0(sK1),X2)
      | ~ r2_hidden(X2,sK2)
      | ~ m1_subset_1(X2,u1_struct_0(sK1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f40,plain,(
    ~ v2_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
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

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f21,plain,(
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

fof(f22,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f21])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | r2_hidden(sK0(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f35,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f34,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f36,plain,(
    v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f37,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f38,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f25])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | m1_subset_1(sK0(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

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
      | k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK0(X0,X1))
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_9,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0))) = k6_domain_1(u1_struct_0(sK1),X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_8,negated_conjecture,
    ( ~ v2_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_6,plain,
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
    inference(cnf_transformation,[],[f35])).

cnf(c_336,plain,
    ( v2_tex_2(X0,X1)
    | r2_hidden(sK0(X1,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_13])).

cnf(c_337,plain,
    ( v2_tex_2(X0,sK1)
    | r2_hidden(sK0(sK1,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_tdlat_3(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_336])).

cnf(c_14,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_12,negated_conjecture,
    ( v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_11,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_341,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(sK0(sK1,X0),X0)
    | v2_tex_2(X0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_337,c_14,c_12,c_11])).

cnf(c_342,plain,
    ( v2_tex_2(X0,sK1)
    | r2_hidden(sK0(sK1,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(renaming,[status(thm)],[c_341])).

cnf(c_385,plain,
    ( r2_hidden(sK0(sK1,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_342])).

cnf(c_386,plain,
    ( r2_hidden(sK0(sK1,sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_385])).

cnf(c_10,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_388,plain,
    ( r2_hidden(sK0(sK1,sK2),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_386,c_10])).

cnf(c_444,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X0))) = k6_domain_1(u1_struct_0(sK1),X0)
    | sK0(sK1,sK2) != X0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_388])).

cnf(c_445,plain,
    ( ~ m1_subset_1(sK0(sK1,sK2),u1_struct_0(sK1))
    | k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)))) = k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_444])).

cnf(c_245,plain,
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
    inference(resolution_lifted,[status(thm)],[c_6,c_9])).

cnf(c_246,plain,
    ( v2_tex_2(sK2,X0)
    | ~ m1_subset_1(sK0(X0,sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_tdlat_3(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK0(X0,sK2)))) = k6_domain_1(u1_struct_0(sK1),sK0(X0,sK2)) ),
    inference(unflattening,[status(thm)],[c_245])).

cnf(c_248,plain,
    ( v2_tex_2(sK2,sK1)
    | ~ m1_subset_1(sK0(sK1,sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_tdlat_3(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)))) = k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_246])).

cnf(c_7,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_315,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_13])).

cnf(c_316,plain,
    ( v2_tex_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(sK1,X0),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ v3_tdlat_3(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_315])).

cnf(c_320,plain,
    ( m1_subset_1(sK0(sK1,X0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_tex_2(X0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_316,c_14,c_12,c_11])).

cnf(c_321,plain,
    ( v2_tex_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(sK1,X0),u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_320])).

cnf(c_396,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(sK1,X0),u1_struct_0(sK1))
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_321])).

cnf(c_397,plain,
    ( m1_subset_1(sK0(sK1,sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_396])).

cnf(c_447,plain,
    ( k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)))) = k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_445,c_14,c_13,c_12,c_11,c_10,c_8,c_248,c_397])).

cnf(c_513,plain,
    ( k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)))) = k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)) ),
    inference(subtyping,[status(esa)],[c_447])).

cnf(c_518,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_669,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_518])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_520,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X0_45))
    | k9_subset_1(X0_45,X0_44,X1_44) = k9_subset_1(X0_45,X1_44,X0_44) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_667,plain,
    ( k9_subset_1(X0_45,X0_44,X1_44) = k9_subset_1(X0_45,X1_44,X0_44)
    | m1_subset_1(X0_44,k1_zfmisc_1(X0_45)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_520])).

cnf(c_866,plain,
    ( k9_subset_1(u1_struct_0(sK1),sK2,X0_44) = k9_subset_1(u1_struct_0(sK1),X0_44,sK2) ),
    inference(superposition,[status(thm)],[c_669,c_667])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_519,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X0_45))
    | m1_subset_1(k9_subset_1(X0_45,X1_44,X0_44),k1_zfmisc_1(X0_45)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_668,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(X0_45)) != iProver_top
    | m1_subset_1(k9_subset_1(X0_45,X1_44,X0_44),k1_zfmisc_1(X0_45)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_519])).

cnf(c_969,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k9_subset_1(u1_struct_0(sK1),X0_44,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_866,c_668])).

cnf(c_19,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_719,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK1),X0_44,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_519])).

cnf(c_720,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK1),X0_44,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_719])).

cnf(c_1059,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK1),X0_44,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_969,c_19,c_720])).

cnf(c_1066,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK1),sK2,X0_44),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_866,c_1059])).

cnf(c_1199,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_513,c_1066])).

cnf(c_3,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_5,plain,
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

cnf(c_171,plain,
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
    inference(resolution_lifted,[status(thm)],[c_3,c_5])).

cnf(c_172,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k6_domain_1(u1_struct_0(X1),sK0(X1,X0)) != k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) ),
    inference(unflattening,[status(thm)],[c_171])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_194,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k6_domain_1(u1_struct_0(X1),sK0(X1,X0)) != k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_172,c_1])).

cnf(c_291,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) != k6_domain_1(u1_struct_0(X1),sK0(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_194,c_13])).

cnf(c_292,plain,
    ( v2_tex_2(X0,sK1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_tdlat_3(sK1)
    | ~ l1_pre_topc(sK1)
    | k9_subset_1(u1_struct_0(sK1),X0,k2_pre_topc(sK1,X1)) != k6_domain_1(u1_struct_0(sK1),sK0(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_291])).

cnf(c_296,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_tex_2(X0,sK1)
    | k9_subset_1(u1_struct_0(sK1),X0,k2_pre_topc(sK1,X1)) != k6_domain_1(u1_struct_0(sK1),sK0(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_292,c_14,c_12,c_11])).

cnf(c_297,plain,
    ( v2_tex_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | k9_subset_1(u1_struct_0(sK1),X0,k2_pre_topc(sK1,X1)) != k6_domain_1(u1_struct_0(sK1),sK0(sK1,X0)) ),
    inference(renaming,[status(thm)],[c_296])).

cnf(c_407,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | k9_subset_1(u1_struct_0(sK1),X0,k2_pre_topc(sK1,X1)) != k6_domain_1(u1_struct_0(sK1),sK0(sK1,X0))
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_297])).

cnf(c_408,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,X0)) != k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_407])).

cnf(c_412,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,X0)) != k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_408,c_10])).

cnf(c_515,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
    | k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,X0_44)) != k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)) ),
    inference(subtyping,[status(esa)],[c_412])).

cnf(c_715,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)))) != k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_515])).

cnf(c_716,plain,
    ( k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)))) != k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_715])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1199,c_716,c_513])).


%------------------------------------------------------------------------------
