%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   42 (  82 expanded)
%              Number of leaves         :    9 (  29 expanded)
%              Depth                    :   12
%              Number of atoms          :  223 ( 493 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :   13 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f66,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f29,f27,f28,f30,f31,f32,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))),X0,X1)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f64,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_waybel_9)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))),X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) ) ),
    inference(duplicate_literal_removal,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))),X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ l1_struct_0(X0) ) ),
    inference(resolution,[],[f60,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_waybel_0)).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(u1_waybel_0(X2,k4_waybel_9(X2,X1,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(X2,X1,X0)),u1_struct_0(X2))))
      | m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(X2,X1,X0)),u1_struct_0(X2),u1_waybel_0(X2,k4_waybel_9(X2,X1,X0))),X2,X1)
      | ~ l1_waybel_0(X1,X2)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f39,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))),X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_yellow19(X2,X0,X1)
      | k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) != X2
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_yellow19(X2,X0,X1)
                  | ! [X3] :
                      ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) != X2
                      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
                & ( ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,sK3(X0,X1,X2))),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,sK3(X0,X1,X2)))) = X2
                    & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) )
                  | ~ m1_yellow19(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X4)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X4))) = X2
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,sK3(X0,X1,X2))),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,sK3(X0,X1,X2)))) = X2
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_yellow19(X2,X0,X1)
                  | ! [X3] :
                      ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) != X2
                      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
                & ( ? [X4] :
                      ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X4)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X4))) = X2
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_yellow19(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_yellow19(X2,X0,X1)
                  | ! [X3] :
                      ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) != X2
                      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
                & ( ? [X3] :
                      ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) = X2
                      & m1_subset_1(X3,u1_struct_0(X1)) )
                  | ~ m1_yellow19(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_yellow19(X2,X0,X1)
              <=> ? [X3] :
                    ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) = X2
                    & m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_yellow19(X2,X0,X1)
              <=> ? [X3] :
                    ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) = X2
                    & m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_yellow19(X2,X0,X1)
              <=> ? [X3] :
                    ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) = X2
                    & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow19)).

fof(f32,plain,(
    ~ m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0),u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))),sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0),u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))),sK0,sK1)
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_waybel_0(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f21,f20,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))),X0,X1)
                & m1_subset_1(X2,u1_struct_0(X1)) )
            & l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(sK0,X1,X2)),u1_struct_0(sK0),u1_waybel_0(sK0,k4_waybel_9(sK0,X1,X2))),sK0,X1)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(sK0,X1,X2)),u1_struct_0(sK0),u1_waybel_0(sK0,k4_waybel_9(sK0,X1,X2))),sK0,X1)
            & m1_subset_1(X2,u1_struct_0(X1)) )
        & l1_waybel_0(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ~ m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(sK0,sK1,X2)),u1_struct_0(sK0),u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,X2))),sK0,sK1)
          & m1_subset_1(X2,u1_struct_0(sK1)) )
      & l1_waybel_0(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X2] :
        ( ~ m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(sK0,sK1,X2)),u1_struct_0(sK0),u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,X2))),sK0,sK1)
        & m1_subset_1(X2,u1_struct_0(sK1)) )
   => ( ~ m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0),u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))),sK0,sK1)
      & m1_subset_1(sK2,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))),X0,X1)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))),X0,X1)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))),X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))),X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_yellow19)).

fof(f31,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f30,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f28,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f27,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f29,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n005.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:23:32 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (30775)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (30785)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.47  % (30775)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f29,f27,f28,f30,f31,f32,f65])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))),X0,X1) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X1))) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f64,f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) | (~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X1)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => l1_waybel_0(k4_waybel_9(X0,X1,X2),X0))),
% 0.21/0.47    inference(pure_predicate_removal,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X1)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_waybel_9)).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))),X0,X1) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)) )),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f62])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))),X0,X1) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) | ~l1_struct_0(X0)) )),
% 0.21/0.47    inference(resolution,[],[f60,f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))))),
% 0.21/0.47    inference(pure_predicate_removal,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 0.21/0.47    inference(pure_predicate_removal,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_waybel_0)).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(u1_waybel_0(X2,k4_waybel_9(X2,X1,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(X2,X1,X0)),u1_struct_0(X2)))) | m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(X2,X1,X0)),u1_struct_0(X2),u1_waybel_0(X2,k4_waybel_9(X2,X1,X0))),X2,X1) | ~l1_waybel_0(X1,X2) | v2_struct_0(X1) | ~l1_struct_0(X2) | v2_struct_0(X2) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 0.21/0.47    inference(resolution,[],[f39,f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X0,X3,X1] : (~m1_subset_1(k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X1)) | m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))),X0,X1) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(equality_resolution,[],[f35])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (m1_yellow19(X2,X0,X1) | k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) != X2 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (((m1_yellow19(X2,X0,X1) | ! [X3] : (k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) != X2 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,sK3(X0,X1,X2))),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,sK3(X0,X1,X2)))) = X2 & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))) | ~m1_yellow19(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ! [X2,X1,X0] : (? [X4] : (k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X4)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X4))) = X2 & m1_subset_1(X4,u1_struct_0(X1))) => (k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,sK3(X0,X1,X2))),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,sK3(X0,X1,X2)))) = X2 & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (((m1_yellow19(X2,X0,X1) | ! [X3] : (k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) != X2 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X4)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X4))) = X2 & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_yellow19(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(rectify,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (((m1_yellow19(X2,X0,X1) | ! [X3] : (k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) != X2 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) = X2 & m1_subset_1(X3,u1_struct_0(X1))) | ~m1_yellow19(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : ((m1_yellow19(X2,X0,X1) <=> ? [X3] : (k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) = X2 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : ((m1_yellow19(X2,X0,X1) <=> ? [X3] : (k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) = X2 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_yellow19(X2,X0,X1) <=> ? [X3] : (k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) = X2 & m1_subset_1(X3,u1_struct_0(X1)))))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow19)).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ~m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0),u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))),sK0,sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ((~m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0),u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))),sK0,sK1) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_waybel_0(sK1,sK0) & ~v2_struct_0(sK1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f21,f20,f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (~m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))),X0,X1) & m1_subset_1(X2,u1_struct_0(X1))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(sK0,X1,X2)),u1_struct_0(sK0),u1_waybel_0(sK0,k4_waybel_9(sK0,X1,X2))),sK0,X1) & m1_subset_1(X2,u1_struct_0(X1))) & l1_waybel_0(X1,sK0) & ~v2_struct_0(X1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ? [X1] : (? [X2] : (~m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(sK0,X1,X2)),u1_struct_0(sK0),u1_waybel_0(sK0,k4_waybel_9(sK0,X1,X2))),sK0,X1) & m1_subset_1(X2,u1_struct_0(X1))) & l1_waybel_0(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (~m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(sK0,sK1,X2)),u1_struct_0(sK0),u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,X2))),sK0,sK1) & m1_subset_1(X2,u1_struct_0(sK1))) & l1_waybel_0(sK1,sK0) & ~v2_struct_0(sK1))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ? [X2] : (~m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(sK0,sK1,X2)),u1_struct_0(sK0),u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,X2))),sK0,sK1) & m1_subset_1(X2,u1_struct_0(sK1))) => (~m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0),u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))),sK0,sK1) & m1_subset_1(sK2,u1_struct_0(sK1)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (~m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))),X0,X1) & m1_subset_1(X2,u1_struct_0(X1))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (~m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))),X0,X1) & m1_subset_1(X2,u1_struct_0(X1))) & (l1_waybel_0(X1,X0) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,negated_conjecture,(
% 0.21/0.47    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))),X0,X1))))),
% 0.21/0.47    inference(negated_conjecture,[],[f5])).
% 0.21/0.47  fof(f5,conjecture,(
% 0.21/0.47    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))),X0,X1))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_yellow19)).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    m1_subset_1(sK2,u1_struct_0(sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f22])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    l1_waybel_0(sK1,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f22])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    l1_struct_0(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f22])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ~v2_struct_0(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f22])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ~v2_struct_0(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f22])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (30775)------------------------------
% 0.21/0.47  % (30775)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (30775)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (30775)Memory used [KB]: 6140
% 0.21/0.47  % (30775)Time elapsed: 0.063 s
% 0.21/0.47  % (30775)------------------------------
% 0.21/0.47  % (30775)------------------------------
% 0.21/0.47  % (30784)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (30769)Success in time 0.115 s
%------------------------------------------------------------------------------
