%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:42 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   90 (1607 expanded)
%              Number of leaves         :   11 ( 508 expanded)
%              Depth                    :   23
%              Number of atoms          :  461 (21216 expanded)
%              Number of equality atoms :   51 (1709 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f289,plain,(
    $false ),
    inference(global_subsumption,[],[f129,f282,f288])).

fof(f288,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v1_borsuk_1(sK1,sK0) ),
    inference(resolution,[],[f285,f85])).

fof(f85,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(u1_struct_0(X0),sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v1_borsuk_1(X0,sK0) ) ),
    inference(global_subsumption,[],[f32,f82])).

fof(f82,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(u1_struct_0(X0),sK0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0)
      | v1_borsuk_1(X0,sK0) ) ),
    inference(resolution,[],[f61,f31])).

fof(f31,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( ~ m1_pre_topc(sK2,sK0)
      | ~ v1_borsuk_1(sK2,sK0)
      | ~ m1_pre_topc(sK1,sK0)
      | ~ v1_borsuk_1(sK1,sK0) )
    & ( ( m1_pre_topc(sK2,sK0)
        & v1_borsuk_1(sK2,sK0) )
      | ( m1_pre_topc(sK1,sK0)
        & v1_borsuk_1(sK1,sK0) ) )
    & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f26,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_pre_topc(X2,X0)
                  | ~ v1_borsuk_1(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_borsuk_1(X1,X0) )
                & ( ( m1_pre_topc(X2,X0)
                    & v1_borsuk_1(X2,X0) )
                  | ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) ) )
                & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
                & l1_pre_topc(X2)
                & v2_pre_topc(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,sK0)
                | ~ v1_borsuk_1(X2,sK0)
                | ~ m1_pre_topc(X1,sK0)
                | ~ v1_borsuk_1(X1,sK0) )
              & ( ( m1_pre_topc(X2,sK0)
                  & v1_borsuk_1(X2,sK0) )
                | ( m1_pre_topc(X1,sK0)
                  & v1_borsuk_1(X1,sK0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ m1_pre_topc(X2,sK0)
              | ~ v1_borsuk_1(X2,sK0)
              | ~ m1_pre_topc(X1,sK0)
              | ~ v1_borsuk_1(X1,sK0) )
            & ( ( m1_pre_topc(X2,sK0)
                & v1_borsuk_1(X2,sK0) )
              | ( m1_pre_topc(X1,sK0)
                & v1_borsuk_1(X1,sK0) ) )
            & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
            & l1_pre_topc(X2)
            & v2_pre_topc(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1) )
   => ( ? [X2] :
          ( ( ~ m1_pre_topc(X2,sK0)
            | ~ v1_borsuk_1(X2,sK0)
            | ~ m1_pre_topc(sK1,sK0)
            | ~ v1_borsuk_1(sK1,sK0) )
          & ( ( m1_pre_topc(X2,sK0)
              & v1_borsuk_1(X2,sK0) )
            | ( m1_pre_topc(sK1,sK0)
              & v1_borsuk_1(sK1,sK0) ) )
          & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = X2
          & l1_pre_topc(X2)
          & v2_pre_topc(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X2] :
        ( ( ~ m1_pre_topc(X2,sK0)
          | ~ v1_borsuk_1(X2,sK0)
          | ~ m1_pre_topc(sK1,sK0)
          | ~ v1_borsuk_1(sK1,sK0) )
        & ( ( m1_pre_topc(X2,sK0)
            & v1_borsuk_1(X2,sK0) )
          | ( m1_pre_topc(sK1,sK0)
            & v1_borsuk_1(sK1,sK0) ) )
        & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = X2
        & l1_pre_topc(X2)
        & v2_pre_topc(X2) )
   => ( ( ~ m1_pre_topc(sK2,sK0)
        | ~ v1_borsuk_1(sK2,sK0)
        | ~ m1_pre_topc(sK1,sK0)
        | ~ v1_borsuk_1(sK1,sK0) )
      & ( ( m1_pre_topc(sK2,sK0)
          & v1_borsuk_1(sK2,sK0) )
        | ( m1_pre_topc(sK1,sK0)
          & v1_borsuk_1(sK1,sK0) ) )
      & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,X0)
                | ~ v1_borsuk_1(X2,X0)
                | ~ m1_pre_topc(X1,X0)
                | ~ v1_borsuk_1(X1,X0) )
              & ( ( m1_pre_topc(X2,X0)
                  & v1_borsuk_1(X2,X0) )
                | ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,X0)
                | ~ v1_borsuk_1(X2,X0)
                | ~ m1_pre_topc(X1,X0)
                | ~ v1_borsuk_1(X1,X0) )
              & ( ( m1_pre_topc(X2,X0)
                  & v1_borsuk_1(X2,X0) )
                | ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <~> ( m1_pre_topc(X2,X0)
                  & v1_borsuk_1(X2,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <~> ( m1_pre_topc(X2,X0)
                  & v1_borsuk_1(X2,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( l1_pre_topc(X2)
                  & v2_pre_topc(X2) )
               => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
                 => ( ( m1_pre_topc(X1,X0)
                      & v1_borsuk_1(X1,X0) )
                  <=> ( m1_pre_topc(X2,X0)
                      & v1_borsuk_1(X2,X0) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) )
                <=> ( m1_pre_topc(X2,X0)
                    & v1_borsuk_1(X2,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_tmap_1)).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v4_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v1_borsuk_1(X1,X0) ) ),
    inference(global_subsumption,[],[f45,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_borsuk_1(X1,X0)
      | ~ v4_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v1_borsuk_1(X1,X0)
      | ~ v4_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) )
                  | ~ v4_pre_topc(X2,X0) )
                & ( v4_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_borsuk_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) )
                  | ~ v4_pre_topc(X2,X0) )
                & ( v4_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_borsuk_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <=> v4_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <=> v4_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) )
                <=> v4_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tsep_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f32,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f285,plain,(
    v4_pre_topc(u1_struct_0(sK1),sK0) ),
    inference(subsumption_resolution,[],[f280,f283])).

fof(f283,plain,(
    v1_borsuk_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f38,f282])).

fof(f38,plain,
    ( v1_borsuk_1(sK2,sK0)
    | v1_borsuk_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f280,plain,
    ( v4_pre_topc(u1_struct_0(sK1),sK0)
    | ~ v1_borsuk_1(sK2,sK0) ),
    inference(global_subsumption,[],[f132,f238])).

fof(f238,plain,
    ( v4_pre_topc(u1_struct_0(sK1),sK0)
    | ~ v1_borsuk_1(sK2,sK0)
    | ~ m1_pre_topc(sK2,sK0) ),
    inference(superposition,[],[f107,f158])).

fof(f158,plain,(
    u1_struct_0(sK1) = u1_struct_0(sK2) ),
    inference(trivial_inequality_removal,[],[f153])).

fof(f153,plain,
    ( sK2 != sK2
    | u1_struct_0(sK1) = u1_struct_0(sK2) ),
    inference(superposition,[],[f93,f130])).

fof(f130,plain,(
    sK2 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(subsumption_resolution,[],[f117,f129])).

fof(f117,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | sK2 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(global_subsumption,[],[f36,f116])).

fof(f116,plain,
    ( ~ l1_pre_topc(sK2)
    | sK2 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | ~ m1_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f67,f37])).

fof(f37,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2 ),
    inference(cnf_transformation,[],[f27])).

fof(f67,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
      | ~ m1_pre_topc(X0,sK0) ) ),
    inference(resolution,[],[f64,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f64,plain,(
    ! [X0] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ m1_pre_topc(X0,sK0) ) ),
    inference(resolution,[],[f46,f32])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

fof(f36,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f93,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(X0,X1) != sK2
      | u1_struct_0(sK1) = X0 ) ),
    inference(global_subsumption,[],[f34,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK1) = X0
      | g1_pre_topc(X0,X1) != sK2
      | ~ l1_pre_topc(sK1) ) ),
    inference(resolution,[],[f88,f43])).

fof(f43,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
      | u1_struct_0(sK1) = X0
      | g1_pre_topc(X0,X1) != sK2 ) ),
    inference(superposition,[],[f53,f37])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f34,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f107,plain,(
    ! [X0] :
      ( v4_pre_topc(u1_struct_0(X0),sK0)
      | ~ v1_borsuk_1(X0,sK0)
      | ~ m1_pre_topc(X0,sK0) ) ),
    inference(global_subsumption,[],[f32,f104])).

fof(f104,plain,(
    ! [X0] :
      ( ~ v1_borsuk_1(X0,sK0)
      | v4_pre_topc(u1_struct_0(X0),sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0) ) ),
    inference(resolution,[],[f103,f31])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X1)
      | ~ v1_borsuk_1(X0,X1)
      | v4_pre_topc(u1_struct_0(X0),X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | ~ v1_borsuk_1(X0,X1)
      | v4_pre_topc(u1_struct_0(X0),X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f60,f45])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | v4_pre_topc(u1_struct_0(X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f132,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(subsumption_resolution,[],[f76,f129])).

fof(f76,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f73,f37])).

fof(f73,plain,(
    ! [X0] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK0)
      | ~ m1_pre_topc(X0,sK0) ) ),
    inference(resolution,[],[f47,f32])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f282,plain,(
    ~ v1_borsuk_1(sK1,sK0) ),
    inference(global_subsumption,[],[f129,f131,f281])).

fof(f281,plain,
    ( v1_borsuk_1(sK2,sK0)
    | ~ v1_borsuk_1(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f279,f107])).

fof(f279,plain,
    ( ~ v4_pre_topc(u1_struct_0(sK1),sK0)
    | v1_borsuk_1(sK2,sK0) ),
    inference(global_subsumption,[],[f132,f235])).

fof(f235,plain,
    ( ~ v4_pre_topc(u1_struct_0(sK1),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v1_borsuk_1(sK2,sK0) ),
    inference(superposition,[],[f85,f158])).

fof(f131,plain,
    ( ~ v1_borsuk_1(sK2,sK0)
    | ~ v1_borsuk_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f77,f129])).

fof(f77,plain,
    ( ~ v1_borsuk_1(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v1_borsuk_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f42,f76])).

fof(f42,plain,
    ( ~ v1_borsuk_1(sK2,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v1_borsuk_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f129,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(global_subsumption,[],[f32,f128])).

fof(f128,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(duplicate_literal_removal,[],[f125])).

fof(f125,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | m1_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f123,f41])).

fof(f41,plain,
    ( m1_pre_topc(sK2,sK0)
    | m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f123,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK2,X0)
      | m1_pre_topc(sK1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(global_subsumption,[],[f36,f35,f34,f33,f122])).

fof(f122,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK2)
      | ~ m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK2)
      | m1_pre_topc(sK1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f56,f37])).

fof(f56,plain,(
    ! [X2,X0] :
      ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  | ~ m1_pre_topc(X2,X0) )
                & ( m1_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0) ) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
               => ( m1_pre_topc(X1,X0)
                <=> m1_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tmap_1)).

fof(f33,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f35,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:23:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (6811)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.50  % (6811)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % (6819)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f289,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(global_subsumption,[],[f129,f282,f288])).
% 0.22/0.51  fof(f288,plain,(
% 0.22/0.51    ~m1_pre_topc(sK1,sK0) | v1_borsuk_1(sK1,sK0)),
% 0.22/0.51    inference(resolution,[],[f285,f85])).
% 0.22/0.51  fof(f85,plain,(
% 0.22/0.51    ( ! [X0] : (~v4_pre_topc(u1_struct_0(X0),sK0) | ~m1_pre_topc(X0,sK0) | v1_borsuk_1(X0,sK0)) )),
% 0.22/0.51    inference(global_subsumption,[],[f32,f82])).
% 0.22/0.51  fof(f82,plain,(
% 0.22/0.51    ( ! [X0] : (~v4_pre_topc(u1_struct_0(X0),sK0) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | v1_borsuk_1(X0,sK0)) )),
% 0.22/0.51    inference(resolution,[],[f61,f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    v2_pre_topc(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    (((~m1_pre_topc(sK2,sK0) | ~v1_borsuk_1(sK2,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_borsuk_1(sK1,sK0)) & ((m1_pre_topc(sK2,sK0) & v1_borsuk_1(sK2,sK0)) | (m1_pre_topc(sK1,sK0) & v1_borsuk_1(sK1,sK0))) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2 & l1_pre_topc(sK2) & v2_pre_topc(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f26,f25,f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0)) & ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : ((~m1_pre_topc(X2,sK0) | ~v1_borsuk_1(X2,sK0) | ~m1_pre_topc(X1,sK0) | ~v1_borsuk_1(X1,sK0)) & ((m1_pre_topc(X2,sK0) & v1_borsuk_1(X2,sK0)) | (m1_pre_topc(X1,sK0) & v1_borsuk_1(X1,sK0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ? [X1] : (? [X2] : ((~m1_pre_topc(X2,sK0) | ~v1_borsuk_1(X2,sK0) | ~m1_pre_topc(X1,sK0) | ~v1_borsuk_1(X1,sK0)) & ((m1_pre_topc(X2,sK0) & v1_borsuk_1(X2,sK0)) | (m1_pre_topc(X1,sK0) & v1_borsuk_1(X1,sK0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : ((~m1_pre_topc(X2,sK0) | ~v1_borsuk_1(X2,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_borsuk_1(sK1,sK0)) & ((m1_pre_topc(X2,sK0) & v1_borsuk_1(X2,sK0)) | (m1_pre_topc(sK1,sK0) & v1_borsuk_1(sK1,sK0))) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ? [X2] : ((~m1_pre_topc(X2,sK0) | ~v1_borsuk_1(X2,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_borsuk_1(sK1,sK0)) & ((m1_pre_topc(X2,sK0) & v1_borsuk_1(X2,sK0)) | (m1_pre_topc(sK1,sK0) & v1_borsuk_1(sK1,sK0))) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) => ((~m1_pre_topc(sK2,sK0) | ~v1_borsuk_1(sK2,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_borsuk_1(sK1,sK0)) & ((m1_pre_topc(sK2,sK0) & v1_borsuk_1(sK2,sK0)) | (m1_pre_topc(sK1,sK0) & v1_borsuk_1(sK1,sK0))) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2 & l1_pre_topc(sK2) & v2_pre_topc(sK2))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0)) & ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : ((((~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0)) | (~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0))) & ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <~> (m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f10])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <~> (m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2) & (l1_pre_topc(X2) & v2_pre_topc(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,negated_conjecture,(
% 0.22/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 => ((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)))))))),
% 0.22/0.51    inference(negated_conjecture,[],[f8])).
% 0.22/0.51  fof(f8,conjecture,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 => ((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_tmap_1)).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~v4_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v1_borsuk_1(X1,X0)) )),
% 0.22/0.51    inference(global_subsumption,[],[f45,f58])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v1_borsuk_1(X1,X0) | ~v4_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.51    inference(equality_resolution,[],[f51])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (v1_borsuk_1(X1,X0) | ~v4_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) | ~v4_pre_topc(X2,X0)) & (v4_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) | ~v4_pre_topc(X2,X0)) & (v4_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> v4_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> v4_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> v4_pre_topc(X2,X0))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tsep_1)).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    l1_pre_topc(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f285,plain,(
% 0.22/0.51    v4_pre_topc(u1_struct_0(sK1),sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f280,f283])).
% 0.22/0.51  fof(f283,plain,(
% 0.22/0.51    v1_borsuk_1(sK2,sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f38,f282])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    v1_borsuk_1(sK2,sK0) | v1_borsuk_1(sK1,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f280,plain,(
% 0.22/0.51    v4_pre_topc(u1_struct_0(sK1),sK0) | ~v1_borsuk_1(sK2,sK0)),
% 0.22/0.51    inference(global_subsumption,[],[f132,f238])).
% 0.22/0.51  fof(f238,plain,(
% 0.22/0.51    v4_pre_topc(u1_struct_0(sK1),sK0) | ~v1_borsuk_1(sK2,sK0) | ~m1_pre_topc(sK2,sK0)),
% 0.22/0.51    inference(superposition,[],[f107,f158])).
% 0.22/0.51  fof(f158,plain,(
% 0.22/0.51    u1_struct_0(sK1) = u1_struct_0(sK2)),
% 0.22/0.51    inference(trivial_inequality_removal,[],[f153])).
% 0.22/0.51  fof(f153,plain,(
% 0.22/0.51    sK2 != sK2 | u1_struct_0(sK1) = u1_struct_0(sK2)),
% 0.22/0.51    inference(superposition,[],[f93,f130])).
% 0.22/0.51  fof(f130,plain,(
% 0.22/0.51    sK2 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 0.22/0.51    inference(subsumption_resolution,[],[f117,f129])).
% 0.22/0.51  fof(f117,plain,(
% 0.22/0.51    ~m1_pre_topc(sK1,sK0) | sK2 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 0.22/0.51    inference(global_subsumption,[],[f36,f116])).
% 0.22/0.51  fof(f116,plain,(
% 0.22/0.51    ~l1_pre_topc(sK2) | sK2 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) | ~m1_pre_topc(sK1,sK0)),
% 0.22/0.51    inference(superposition,[],[f67,f37])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    ( ! [X0] : (~l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~m1_pre_topc(X0,sK0)) )),
% 0.22/0.51    inference(resolution,[],[f64,f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    ( ! [X0] : (v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_pre_topc(X0,sK0)) )),
% 0.22/0.51    inference(resolution,[],[f46,f32])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    l1_pre_topc(sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f93,plain,(
% 0.22/0.51    ( ! [X0,X1] : (g1_pre_topc(X0,X1) != sK2 | u1_struct_0(sK1) = X0) )),
% 0.22/0.51    inference(global_subsumption,[],[f34,f92])).
% 0.22/0.51  fof(f92,plain,(
% 0.22/0.51    ( ! [X0,X1] : (u1_struct_0(sK1) = X0 | g1_pre_topc(X0,X1) != sK2 | ~l1_pre_topc(sK1)) )),
% 0.22/0.51    inference(resolution,[],[f88,f43])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.22/0.51  fof(f88,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | u1_struct_0(sK1) = X0 | g1_pre_topc(X0,X1) != sK2) )),
% 0.22/0.51    inference(superposition,[],[f53,f37])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X0 = X2 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    l1_pre_topc(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f107,plain,(
% 0.22/0.51    ( ! [X0] : (v4_pre_topc(u1_struct_0(X0),sK0) | ~v1_borsuk_1(X0,sK0) | ~m1_pre_topc(X0,sK0)) )),
% 0.22/0.51    inference(global_subsumption,[],[f32,f104])).
% 0.22/0.51  fof(f104,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_borsuk_1(X0,sK0) | v4_pre_topc(u1_struct_0(X0),sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(X0,sK0)) )),
% 0.22/0.51    inference(resolution,[],[f103,f31])).
% 0.22/0.51  fof(f103,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v2_pre_topc(X1) | ~v1_borsuk_1(X0,X1) | v4_pre_topc(u1_struct_0(X0),X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X0,X1)) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f102])).
% 0.22/0.51  fof(f102,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | ~v1_borsuk_1(X0,X1) | v4_pre_topc(u1_struct_0(X0),X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1)) )),
% 0.22/0.51    inference(resolution,[],[f60,f45])).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0) | v4_pre_topc(u1_struct_0(X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f59])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v4_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.51    inference(equality_resolution,[],[f50])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (v4_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f30])).
% 0.22/0.51  fof(f132,plain,(
% 0.22/0.51    m1_pre_topc(sK2,sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f76,f129])).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK1,sK0)),
% 0.22/0.51    inference(superposition,[],[f73,f37])).
% 0.22/0.51  fof(f73,plain,(
% 0.22/0.51    ( ! [X0] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK0) | ~m1_pre_topc(X0,sK0)) )),
% 0.22/0.51    inference(resolution,[],[f47,f32])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f282,plain,(
% 0.22/0.52    ~v1_borsuk_1(sK1,sK0)),
% 0.22/0.52    inference(global_subsumption,[],[f129,f131,f281])).
% 0.22/0.52  fof(f281,plain,(
% 0.22/0.52    v1_borsuk_1(sK2,sK0) | ~v1_borsuk_1(sK1,sK0) | ~m1_pre_topc(sK1,sK0)),
% 0.22/0.52    inference(resolution,[],[f279,f107])).
% 0.22/0.52  fof(f279,plain,(
% 0.22/0.52    ~v4_pre_topc(u1_struct_0(sK1),sK0) | v1_borsuk_1(sK2,sK0)),
% 0.22/0.52    inference(global_subsumption,[],[f132,f235])).
% 0.22/0.52  fof(f235,plain,(
% 0.22/0.52    ~v4_pre_topc(u1_struct_0(sK1),sK0) | ~m1_pre_topc(sK2,sK0) | v1_borsuk_1(sK2,sK0)),
% 0.22/0.52    inference(superposition,[],[f85,f158])).
% 0.22/0.52  fof(f131,plain,(
% 0.22/0.52    ~v1_borsuk_1(sK2,sK0) | ~v1_borsuk_1(sK1,sK0)),
% 0.22/0.52    inference(subsumption_resolution,[],[f77,f129])).
% 0.22/0.52  fof(f77,plain,(
% 0.22/0.52    ~v1_borsuk_1(sK2,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_borsuk_1(sK1,sK0)),
% 0.22/0.52    inference(subsumption_resolution,[],[f42,f76])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ~v1_borsuk_1(sK2,sK0) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_borsuk_1(sK1,sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f27])).
% 0.22/0.52  fof(f129,plain,(
% 0.22/0.52    m1_pre_topc(sK1,sK0)),
% 0.22/0.52    inference(global_subsumption,[],[f32,f128])).
% 0.22/0.52  fof(f128,plain,(
% 0.22/0.52    m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f125])).
% 0.22/0.52  fof(f125,plain,(
% 0.22/0.52    m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | m1_pre_topc(sK1,sK0)),
% 0.22/0.52    inference(resolution,[],[f123,f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    m1_pre_topc(sK2,sK0) | m1_pre_topc(sK1,sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f27])).
% 0.22/0.52  fof(f123,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_pre_topc(sK2,X0) | m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(global_subsumption,[],[f36,f35,f34,f33,f122])).
% 0.22/0.52  fof(f122,plain,(
% 0.22/0.52    ( ! [X0] : (~v2_pre_topc(sK2) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK2) | m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(superposition,[],[f56,f37])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    ( ! [X2,X0] : (~v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | m1_pre_topc(X2,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(equality_resolution,[],[f48])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) & (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0))) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(nnf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(flattening,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1 => (m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0))))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tmap_1)).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    v2_pre_topc(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f27])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    v2_pre_topc(sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f27])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (6811)------------------------------
% 0.22/0.52  % (6811)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (6811)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (6811)Memory used [KB]: 6268
% 0.22/0.52  % (6811)Time elapsed: 0.061 s
% 0.22/0.52  % (6811)------------------------------
% 0.22/0.52  % (6811)------------------------------
% 0.22/0.52  % (6798)Success in time 0.145 s
%------------------------------------------------------------------------------
