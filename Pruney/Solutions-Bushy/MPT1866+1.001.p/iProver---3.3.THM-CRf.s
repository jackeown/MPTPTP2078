%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1866+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:42 EST 2020

% Result     : Theorem 0.85s
% Output     : CNFRefutation 0.85s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 486 expanded)
%              Number of clauses        :   44 ( 108 expanded)
%              Number of leaves         :    6 ( 124 expanded)
%              Depth                    :   27
%              Number of atoms          :  421 (4291 expanded)
%              Number of equality atoms :   54 ( 479 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal clause size      :   20 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_tdlat_3(X2)
                    & v1_pre_topc(X2)
                    & ~ v2_struct_0(X2) )
                 => u1_struct_0(X2) != X1 )
              & v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ~ ( ! [X2] :
                    ( ( m1_pre_topc(X2,X0)
                      & v1_tdlat_3(X2)
                      & v1_pre_topc(X2)
                      & ~ v2_struct_0(X2) )
                   => u1_struct_0(X2) != X1 )
                & v2_tex_2(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f5,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ~ ( ! [X2] :
                    ( ( m1_pre_topc(X2,X0)
                      & v1_tdlat_3(X2)
                      & v1_pre_topc(X2)
                      & ~ v2_struct_0(X2) )
                   => u1_struct_0(X2) != X1 )
                & v2_tex_2(X1,X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( u1_struct_0(X2) != X1
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_tdlat_3(X2)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( u1_struct_0(X2) != X1
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_tdlat_3(X2)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( u1_struct_0(X2) != X1
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_tdlat_3(X2)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
     => ( ! [X2] :
            ( u1_struct_0(X2) != sK2
            | ~ m1_pre_topc(X2,X0)
            | ~ v1_tdlat_3(X2)
            | ~ v1_pre_topc(X2)
            | v2_struct_0(X2) )
        & v2_tex_2(sK2,X0)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ! [X2] :
                ( u1_struct_0(X2) != X1
                | ~ m1_pre_topc(X2,X0)
                | ~ v1_tdlat_3(X2)
                | ~ v1_pre_topc(X2)
                | v2_struct_0(X2) )
            & v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ! [X2] :
              ( u1_struct_0(X2) != X1
              | ~ m1_pre_topc(X2,sK1)
              | ~ v1_tdlat_3(X2)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & v2_tex_2(X1,sK1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ! [X2] :
        ( u1_struct_0(X2) != sK2
        | ~ m1_pre_topc(X2,sK1)
        | ~ v1_tdlat_3(X2)
        | ~ v1_pre_topc(X2)
        | v2_struct_0(X2) )
    & v2_tex_2(sK2,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & ~ v1_xboole_0(sK2)
    & l1_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f11,f16,f15])).

fof(f27,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f12,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & v1_pre_topc(X2)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK0(X0,X1)) = X1
        & m1_pre_topc(sK0(X0,X1),X0)
        & v1_pre_topc(sK0(X0,X1))
        & ~ v2_struct_0(sK0(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK0(X0,X1)) = X1
            & m1_pre_topc(sK0(X0,X1),X0)
            & v1_pre_topc(sK0(X0,X1))
            & ~ v2_struct_0(sK0(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f12])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f26,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v2_tex_2(X2,X0)
                <=> v1_tdlat_3(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_tex_2(X2,X0)
                  | ~ v1_tdlat_3(X1) )
                & ( v1_tdlat_3(X1)
                  | ~ v2_tex_2(X2,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ v2_tex_2(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ v2_tex_2(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f22])).

fof(f28,plain,(
    v2_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f24,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f25,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f29,plain,(
    ! [X2] :
      ( u1_struct_0(X2) != sK2
      | ~ m1_pre_topc(X2,sK1)
      | ~ v1_tdlat_3(X2)
      | ~ v1_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(sK0(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK0(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f21,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_8,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_1,plain,
    ( m1_pre_topc(sK0(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_9,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_173,plain,
    ( m1_pre_topc(sK0(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_9])).

cnf(c_174,plain,
    ( m1_pre_topc(sK0(X0,sK2),X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_173])).

cnf(c_5,plain,
    ( ~ v2_tex_2(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_7,negated_conjecture,
    ( v2_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_299,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X0) != sK2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_7])).

cnf(c_300,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(X0) != sK2 ),
    inference(unflattening,[status(thm)],[c_299])).

cnf(c_11,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_10,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_304,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | u1_struct_0(X0) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_300,c_11,c_10])).

cnf(c_6,negated_conjecture,
    ( ~ m1_pre_topc(X0,sK1)
    | ~ v1_tdlat_3(X0)
    | ~ v1_pre_topc(X0)
    | v2_struct_0(X0)
    | u1_struct_0(X0) != sK2 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_pre_topc(sK0(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_209,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_pre_topc(sK0(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_9])).

cnf(c_210,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
    | v1_pre_topc(sK0(X0,sK2))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_209])).

cnf(c_265,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK0(X1,sK2) != X0
    | u1_struct_0(X0) != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_210])).

cnf(c_266,plain,
    ( ~ m1_pre_topc(sK0(X0,sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_tdlat_3(sK0(X0,sK2))
    | v2_struct_0(X0)
    | v2_struct_0(sK0(X0,sK2))
    | ~ l1_pre_topc(X0)
    | u1_struct_0(sK0(X0,sK2)) != sK2 ),
    inference(unflattening,[status(thm)],[c_265])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK0(X1,X0))
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_191,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK0(X1,X0))
    | ~ l1_pre_topc(X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_9])).

cnf(c_192,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK0(X0,sK2))
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_191])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(sK0(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_227,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(sK0(X1,X0)) = X0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_9])).

cnf(c_228,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(sK0(X0,sK2)) = sK2 ),
    inference(unflattening,[status(thm)],[c_227])).

cnf(c_270,plain,
    ( ~ l1_pre_topc(X0)
    | ~ m1_pre_topc(sK0(X0,sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_tdlat_3(sK0(X0,sK2))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_266,c_192,c_228])).

cnf(c_271,plain,
    ( ~ m1_pre_topc(sK0(X0,sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_tdlat_3(sK0(X0,sK2))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(renaming,[status(thm)],[c_270])).

cnf(c_332,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | ~ m1_pre_topc(sK0(X1,sK2),sK1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK0(X1,sK2) != X0
    | u1_struct_0(X0) != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_304,c_271])).

cnf(c_333,plain,
    ( ~ m1_pre_topc(sK0(X0,sK2),sK1)
    | ~ m1_subset_1(u1_struct_0(sK0(X0,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | v2_struct_0(sK0(X0,sK2))
    | ~ l1_pre_topc(X0)
    | u1_struct_0(sK0(X0,sK2)) != sK2 ),
    inference(unflattening,[status(thm)],[c_332])).

cnf(c_337,plain,
    ( ~ l1_pre_topc(X0)
    | ~ m1_pre_topc(sK0(X0,sK2),sK1)
    | ~ m1_subset_1(u1_struct_0(sK0(X0,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_333,c_192,c_228])).

cnf(c_338,plain,
    ( ~ m1_pre_topc(sK0(X0,sK2),sK1)
    | ~ m1_subset_1(u1_struct_0(sK0(X0,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(renaming,[status(thm)],[c_337])).

cnf(c_365,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0(X0,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | sK0(X0,sK2) != sK0(X1,sK2)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_174,c_338])).

cnf(c_366,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0(X0,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK1)
    | sK0(X0,sK2) != sK0(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_365])).

cnf(c_370,plain,
    ( ~ l1_pre_topc(X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(u1_struct_0(sK0(X0,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(X0)
    | sK0(X0,sK2) != sK0(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_366,c_11,c_10,c_8])).

cnf(c_371,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0(X0,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK0(X0,sK2) != sK0(sK1,sK2) ),
    inference(renaming,[status(thm)],[c_370])).

cnf(c_396,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0(X0,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | sK0(X0,sK2) != sK0(sK1,sK2)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_371,c_10])).

cnf(c_397,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | sK0(sK1,sK2) != sK0(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_396])).

cnf(c_176,plain,
    ( m1_pre_topc(sK0(sK1,sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_174])).

cnf(c_194,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_struct_0(sK0(sK1,sK2))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_192])).

cnf(c_230,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(sK0(sK1,sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_228])).

cnf(c_335,plain,
    ( ~ m1_pre_topc(sK0(sK1,sK2),sK1)
    | ~ m1_subset_1(u1_struct_0(sK0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK0(sK1,sK2))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(sK0(sK1,sK2)) != sK2 ),
    inference(instantiation,[status(thm)],[c_333])).

cnf(c_399,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_397,c_11,c_10,c_8,c_176,c_194,c_230,c_335])).

cnf(c_431,plain,
    ( k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(sK0(sK1,sK2)) != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_399])).

cnf(c_432,plain,
    ( k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_431,c_11,c_10,c_8,c_230])).

cnf(c_438,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_432])).


%------------------------------------------------------------------------------
