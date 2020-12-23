%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  135 (1930 expanded)
%              Number of leaves         :   16 ( 593 expanded)
%              Depth                    :   26
%              Number of atoms          :  601 (23173 expanded)
%              Number of equality atoms :   41 (1841 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f448,plain,(
    $false ),
    inference(global_subsumption,[],[f420,f428,f438,f430,f447])).

fof(f447,plain,
    ( ~ v4_pre_topc(k2_struct_0(sK1),sK0)
    | v1_borsuk_1(sK2,sK0) ),
    inference(forward_demodulation,[],[f446,f297])).

fof(f297,plain,(
    k2_struct_0(sK1) = k2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f296,f210])).

fof(f210,plain,(
    r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2)) ),
    inference(resolution,[],[f209,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f209,plain,(
    m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f208,f45])).

fof(f45,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f33,f32,f31])).

fof(f31,plain,
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

fof(f32,plain,
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

fof(f33,plain,
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

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f14])).

% (20434)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_tmap_1)).

fof(f208,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f207,f46])).

fof(f46,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f207,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f206,f90])).

fof(f90,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f56,f55])).

fof(f55,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f56,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f206,plain,
    ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1)))
    | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(resolution,[],[f202,f64])).

fof(f64,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).

fof(f202,plain,(
    ! [X1] :
      ( ~ v4_pre_topc(X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1)))
      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2))) ) ),
    inference(forward_demodulation,[],[f201,f93])).

fof(f93,plain,(
    k2_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(resolution,[],[f57,f89])).

fof(f89,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f58,f48])).

fof(f48,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f58,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f57,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f201,plain,(
    ! [X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1)))
      | ~ v4_pre_topc(X1,sK1) ) ),
    inference(forward_demodulation,[],[f200,f49])).

fof(f49,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2 ),
    inference(cnf_transformation,[],[f34])).

fof(f200,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1)))
      | ~ v4_pre_topc(X1,sK1)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ) ),
    inference(forward_demodulation,[],[f199,f92])).

fof(f92,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f57,f88])).

fof(f88,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f58,f46])).

fof(f199,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v4_pre_topc(X1,sK1)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ) ),
    inference(subsumption_resolution,[],[f194,f46])).

fof(f194,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v4_pre_topc(X1,sK1)
      | ~ l1_pre_topc(sK1)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ) ),
    inference(resolution,[],[f69,f45])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v4_pre_topc(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v4_pre_topc(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v4_pre_topc(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v4_pre_topc(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_pre_topc)).

fof(f296,plain,
    ( ~ r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2))
    | k2_struct_0(sK1) = k2_struct_0(sK2) ),
    inference(resolution,[],[f290,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f290,plain,(
    r1_tarski(k2_struct_0(sK2),k2_struct_0(sK1)) ),
    inference(resolution,[],[f288,f75])).

fof(f288,plain,(
    m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f287,f47])).

fof(f47,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f287,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK1)))
    | ~ v2_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f286,f48])).

fof(f286,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK1)))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f285,f90])).

fof(f285,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK1)))
    | ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(resolution,[],[f279,f64])).

fof(f279,plain,(
    ! [X1] :
      ( ~ v4_pre_topc(X1,sK2)
      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2))) ) ),
    inference(forward_demodulation,[],[f278,f92])).

fof(f278,plain,(
    ! [X1] :
      ( ~ v4_pre_topc(X1,sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2)))
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(forward_demodulation,[],[f277,f49])).

fof(f277,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2)))
      | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(forward_demodulation,[],[f276,f93])).

fof(f276,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(forward_demodulation,[],[f275,f49])).

fof(f275,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
      | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(subsumption_resolution,[],[f269,f46])).

fof(f269,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
      | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ l1_pre_topc(sK1)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(resolution,[],[f71,f45])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f446,plain,
    ( ~ v4_pre_topc(k2_struct_0(sK2),sK0)
    | v1_borsuk_1(sK2,sK0) ),
    inference(forward_demodulation,[],[f445,f93])).

fof(f445,plain,
    ( v1_borsuk_1(sK2,sK0)
    | ~ v4_pre_topc(u1_struct_0(sK2),sK0) ),
    inference(subsumption_resolution,[],[f444,f43])).

fof(f43,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f444,plain,
    ( v1_borsuk_1(sK2,sK0)
    | ~ v4_pre_topc(u1_struct_0(sK2),sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f440,f44])).

fof(f44,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f440,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_borsuk_1(sK2,sK0)
    | ~ v4_pre_topc(u1_struct_0(sK2),sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f430,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v1_borsuk_1(X1,X0)
      | ~ v4_pre_topc(u1_struct_0(X1),X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(global_subsumption,[],[f59,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v1_borsuk_1(X1,X0)
      | ~ v4_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_borsuk_1(X1,X0)
      | ~ v4_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tsep_1)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f430,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(forward_demodulation,[],[f429,f49])).

fof(f429,plain,(
    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0) ),
    inference(subsumption_resolution,[],[f422,f44])).

fof(f422,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f419,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tmap_1)).

fof(f419,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f418,f44])).

fof(f418,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(duplicate_literal_removal,[],[f417])).

fof(f417,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | m1_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f409,f53])).

fof(f53,plain,
    ( m1_pre_topc(sK2,sK0)
    | m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f409,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(sK2,X1)
      | m1_pre_topc(sK1,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(subsumption_resolution,[],[f408,f47])).

fof(f408,plain,(
    ! [X1] :
      ( ~ v2_pre_topc(sK2)
      | ~ m1_pre_topc(sK2,X1)
      | m1_pre_topc(sK1,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(forward_demodulation,[],[f407,f49])).

fof(f407,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(sK2,X1)
      | m1_pre_topc(sK1,X1)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ l1_pre_topc(X1) ) ),
    inference(subsumption_resolution,[],[f406,f48])).

fof(f406,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(sK2)
      | ~ m1_pre_topc(sK2,X1)
      | m1_pre_topc(sK1,X1)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ l1_pre_topc(X1) ) ),
    inference(forward_demodulation,[],[f405,f49])).

fof(f405,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(sK2,X1)
      | m1_pre_topc(sK1,X1)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ l1_pre_topc(X1) ) ),
    inference(forward_demodulation,[],[f404,f49])).

fof(f404,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1)
      | m1_pre_topc(sK1,X1)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ l1_pre_topc(X1) ) ),
    inference(subsumption_resolution,[],[f398,f46])).

fof(f398,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1)
      | ~ l1_pre_topc(sK1)
      | m1_pre_topc(sK1,X1)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f78,f45])).

fof(f78,plain,(
    ! [X2,X0] :
      ( ~ v2_pre_topc(X2)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)
      | ~ l1_pre_topc(X2)
      | m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tmap_1)).

fof(f438,plain,(
    v4_pre_topc(k2_struct_0(sK1),sK0) ),
    inference(forward_demodulation,[],[f437,f92])).

fof(f437,plain,(
    v4_pre_topc(u1_struct_0(sK1),sK0) ),
    inference(subsumption_resolution,[],[f436,f419])).

fof(f436,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v4_pre_topc(u1_struct_0(sK1),sK0) ),
    inference(resolution,[],[f428,f162])).

fof(f162,plain,(
    ! [X0] :
      ( ~ v1_borsuk_1(X0,sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v4_pre_topc(u1_struct_0(X0),sK0) ) ),
    inference(subsumption_resolution,[],[f159,f44])).

fof(f159,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | ~ v1_borsuk_1(X0,sK0)
      | ~ l1_pre_topc(sK0)
      | v4_pre_topc(u1_struct_0(X0),sK0) ) ),
    inference(resolution,[],[f158,f43])).

fof(f158,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(u1_struct_0(X1),X0) ) ),
    inference(subsumption_resolution,[],[f84,f59])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f428,plain,(
    v1_borsuk_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f427,f313])).

fof(f313,plain,
    ( v4_pre_topc(k2_struct_0(sK1),sK0)
    | v1_borsuk_1(sK1,sK0) ),
    inference(superposition,[],[f171,f297])).

fof(f171,plain,
    ( v4_pre_topc(k2_struct_0(sK2),sK0)
    | v1_borsuk_1(sK1,sK0) ),
    inference(forward_demodulation,[],[f170,f93])).

fof(f170,plain,
    ( v4_pre_topc(u1_struct_0(sK2),sK0)
    | v1_borsuk_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f166,f52])).

fof(f52,plain,
    ( v1_borsuk_1(sK1,sK0)
    | m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f166,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v4_pre_topc(u1_struct_0(sK2),sK0)
    | v1_borsuk_1(sK1,sK0) ),
    inference(resolution,[],[f162,f50])).

fof(f50,plain,
    ( v1_borsuk_1(sK2,sK0)
    | v1_borsuk_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f427,plain,
    ( ~ v4_pre_topc(k2_struct_0(sK1),sK0)
    | v1_borsuk_1(sK1,sK0) ),
    inference(forward_demodulation,[],[f426,f92])).

fof(f426,plain,
    ( v1_borsuk_1(sK1,sK0)
    | ~ v4_pre_topc(u1_struct_0(sK1),sK0) ),
    inference(subsumption_resolution,[],[f425,f43])).

fof(f425,plain,
    ( v1_borsuk_1(sK1,sK0)
    | ~ v4_pre_topc(u1_struct_0(sK1),sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f421,f44])).

fof(f421,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_borsuk_1(sK1,sK0)
    | ~ v4_pre_topc(u1_struct_0(sK1),sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f419,f86])).

fof(f420,plain,
    ( ~ v1_borsuk_1(sK2,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_borsuk_1(sK1,sK0) ),
    inference(resolution,[],[f419,f54])).

fof(f54,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ v1_borsuk_1(sK2,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_borsuk_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:46:40 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.54  % (20433)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.54  % (20419)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.54  % (20420)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (20423)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.55  % (20424)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.55  % (20442)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.56  % (20424)Refutation not found, incomplete strategy% (20424)------------------------------
% 0.21/0.56  % (20424)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (20424)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (20424)Memory used [KB]: 6140
% 0.21/0.56  % (20424)Time elapsed: 0.120 s
% 0.21/0.56  % (20424)------------------------------
% 0.21/0.56  % (20424)------------------------------
% 0.21/0.56  % (20429)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.56  % (20425)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.56  % (20419)Refutation not found, incomplete strategy% (20419)------------------------------
% 0.21/0.56  % (20419)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (20419)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (20419)Memory used [KB]: 10618
% 0.21/0.56  % (20419)Time elapsed: 0.131 s
% 0.21/0.56  % (20419)------------------------------
% 0.21/0.56  % (20419)------------------------------
% 0.21/0.56  % (20432)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.56  % (20426)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.56  % (20440)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.56  % (20425)Refutation not found, incomplete strategy% (20425)------------------------------
% 0.21/0.56  % (20425)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (20425)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (20425)Memory used [KB]: 10618
% 0.21/0.56  % (20425)Time elapsed: 0.128 s
% 0.21/0.56  % (20425)------------------------------
% 0.21/0.56  % (20425)------------------------------
% 0.21/0.56  % (20439)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.56  % (20426)Refutation not found, incomplete strategy% (20426)------------------------------
% 0.21/0.56  % (20426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (20426)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (20426)Memory used [KB]: 1663
% 0.21/0.56  % (20426)Time elapsed: 0.074 s
% 0.21/0.56  % (20426)------------------------------
% 0.21/0.56  % (20426)------------------------------
% 0.21/0.56  % (20437)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.56  % (20428)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.56  % (20422)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.57  % (20441)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.57  % (20421)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.57  % (20432)Refutation not found, incomplete strategy% (20432)------------------------------
% 0.21/0.57  % (20432)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (20432)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (20432)Memory used [KB]: 6268
% 0.21/0.57  % (20432)Time elapsed: 0.135 s
% 0.21/0.57  % (20432)------------------------------
% 0.21/0.57  % (20432)------------------------------
% 0.21/0.57  % (20431)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.57  % (20440)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f448,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(global_subsumption,[],[f420,f428,f438,f430,f447])).
% 0.21/0.57  fof(f447,plain,(
% 0.21/0.57    ~v4_pre_topc(k2_struct_0(sK1),sK0) | v1_borsuk_1(sK2,sK0)),
% 0.21/0.57    inference(forward_demodulation,[],[f446,f297])).
% 0.21/0.57  fof(f297,plain,(
% 0.21/0.57    k2_struct_0(sK1) = k2_struct_0(sK2)),
% 0.21/0.57    inference(subsumption_resolution,[],[f296,f210])).
% 0.21/0.57  fof(f210,plain,(
% 0.21/0.57    r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2))),
% 0.21/0.57    inference(resolution,[],[f209,f75])).
% 0.21/0.57  fof(f75,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f42])).
% 0.21/0.57  fof(f42,plain,(
% 0.21/0.57    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.57    inference(nnf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.57  fof(f209,plain,(
% 0.21/0.57    m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK2)))),
% 0.21/0.57    inference(subsumption_resolution,[],[f208,f45])).
% 0.21/0.57  fof(f45,plain,(
% 0.21/0.57    v2_pre_topc(sK1)),
% 0.21/0.57    inference(cnf_transformation,[],[f34])).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    (((~m1_pre_topc(sK2,sK0) | ~v1_borsuk_1(sK2,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_borsuk_1(sK1,sK0)) & ((m1_pre_topc(sK2,sK0) & v1_borsuk_1(sK2,sK0)) | (m1_pre_topc(sK1,sK0) & v1_borsuk_1(sK1,sK0))) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2 & l1_pre_topc(sK2) & v2_pre_topc(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f33,f32,f31])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    ? [X0] : (? [X1] : (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0)) & ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : ((~m1_pre_topc(X2,sK0) | ~v1_borsuk_1(X2,sK0) | ~m1_pre_topc(X1,sK0) | ~v1_borsuk_1(X1,sK0)) & ((m1_pre_topc(X2,sK0) & v1_borsuk_1(X2,sK0)) | (m1_pre_topc(X1,sK0) & v1_borsuk_1(X1,sK0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    ? [X1] : (? [X2] : ((~m1_pre_topc(X2,sK0) | ~v1_borsuk_1(X2,sK0) | ~m1_pre_topc(X1,sK0) | ~v1_borsuk_1(X1,sK0)) & ((m1_pre_topc(X2,sK0) & v1_borsuk_1(X2,sK0)) | (m1_pre_topc(X1,sK0) & v1_borsuk_1(X1,sK0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : ((~m1_pre_topc(X2,sK0) | ~v1_borsuk_1(X2,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_borsuk_1(sK1,sK0)) & ((m1_pre_topc(X2,sK0) & v1_borsuk_1(X2,sK0)) | (m1_pre_topc(sK1,sK0) & v1_borsuk_1(sK1,sK0))) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    ? [X2] : ((~m1_pre_topc(X2,sK0) | ~v1_borsuk_1(X2,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_borsuk_1(sK1,sK0)) & ((m1_pre_topc(X2,sK0) & v1_borsuk_1(X2,sK0)) | (m1_pre_topc(sK1,sK0) & v1_borsuk_1(sK1,sK0))) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) => ((~m1_pre_topc(sK2,sK0) | ~v1_borsuk_1(sK2,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_borsuk_1(sK1,sK0)) & ((m1_pre_topc(sK2,sK0) & v1_borsuk_1(sK2,sK0)) | (m1_pre_topc(sK1,sK0) & v1_borsuk_1(sK1,sK0))) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2 & l1_pre_topc(sK2) & v2_pre_topc(sK2))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    ? [X0] : (? [X1] : (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0)) & ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.57    inference(flattening,[],[f29])).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    ? [X0] : (? [X1] : (? [X2] : ((((~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0)) | (~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0))) & ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.57    inference(nnf_transformation,[],[f16])).
% 0.21/0.57  fof(f16,plain,(
% 0.21/0.57    ? [X0] : (? [X1] : (? [X2] : (((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <~> (m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.57    inference(flattening,[],[f15])).
% 0.21/0.57  fof(f15,plain,(
% 0.21/0.57    ? [X0] : (? [X1] : (? [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <~> (m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2) & (l1_pre_topc(X2) & v2_pre_topc(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f14])).
% 0.21/0.57  % (20434)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.57  fof(f14,negated_conjecture,(
% 0.21/0.57    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 => ((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)))))))),
% 0.21/0.57    inference(negated_conjecture,[],[f13])).
% 0.21/0.57  fof(f13,conjecture,(
% 0.21/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 => ((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)))))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_tmap_1)).
% 0.21/0.57  fof(f208,plain,(
% 0.21/0.57    m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK2))) | ~v2_pre_topc(sK1)),
% 0.21/0.57    inference(subsumption_resolution,[],[f207,f46])).
% 0.21/0.57  fof(f46,plain,(
% 0.21/0.57    l1_pre_topc(sK1)),
% 0.21/0.57    inference(cnf_transformation,[],[f34])).
% 0.21/0.57  fof(f207,plain,(
% 0.21/0.57    m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK2))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)),
% 0.21/0.57    inference(subsumption_resolution,[],[f206,f90])).
% 0.21/0.57  fof(f90,plain,(
% 0.21/0.57    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.57    inference(forward_demodulation,[],[f56,f55])).
% 0.21/0.57  fof(f55,plain,(
% 0.21/0.57    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.57  fof(f56,plain,(
% 0.21/0.57    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.57  fof(f206,plain,(
% 0.21/0.57    ~m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK2))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)),
% 0.21/0.57    inference(resolution,[],[f202,f64])).
% 0.21/0.57  fof(f64,plain,(
% 0.21/0.57    ( ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f24])).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.57    inference(flattening,[],[f23])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f7])).
% 0.21/0.57  fof(f7,axiom,(
% 0.21/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_struct_0(X0),X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).
% 0.21/0.57  fof(f202,plain,(
% 0.21/0.57    ( ! [X1] : (~v4_pre_topc(X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1))) | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2)))) )),
% 0.21/0.57    inference(forward_demodulation,[],[f201,f93])).
% 0.21/0.57  fof(f93,plain,(
% 0.21/0.57    k2_struct_0(sK2) = u1_struct_0(sK2)),
% 0.21/0.57    inference(resolution,[],[f57,f89])).
% 0.21/0.57  fof(f89,plain,(
% 0.21/0.57    l1_struct_0(sK2)),
% 0.21/0.57    inference(resolution,[],[f58,f48])).
% 0.21/0.57  fof(f48,plain,(
% 0.21/0.57    l1_pre_topc(sK2)),
% 0.21/0.57    inference(cnf_transformation,[],[f34])).
% 0.21/0.57  fof(f58,plain,(
% 0.21/0.57    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f18])).
% 0.21/0.57  fof(f18,plain,(
% 0.21/0.57    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.57  fof(f57,plain,(
% 0.21/0.57    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f17])).
% 0.21/0.57  fof(f17,plain,(
% 0.21/0.57    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.57  fof(f201,plain,(
% 0.21/0.57    ( ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1))) | ~v4_pre_topc(X1,sK1)) )),
% 0.21/0.57    inference(forward_demodulation,[],[f200,f49])).
% 0.21/0.57  fof(f49,plain,(
% 0.21/0.57    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2),
% 0.21/0.57    inference(cnf_transformation,[],[f34])).
% 0.21/0.57  fof(f200,plain,(
% 0.21/0.57    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1))) | ~v4_pre_topc(X1,sK1) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) )),
% 0.21/0.57    inference(forward_demodulation,[],[f199,f92])).
% 0.21/0.57  fof(f92,plain,(
% 0.21/0.57    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.21/0.57    inference(resolution,[],[f57,f88])).
% 0.21/0.57  fof(f88,plain,(
% 0.21/0.57    l1_struct_0(sK1)),
% 0.21/0.57    inference(resolution,[],[f58,f46])).
% 0.21/0.57  fof(f199,plain,(
% 0.21/0.57    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~v4_pre_topc(X1,sK1) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f194,f46])).
% 0.21/0.57  fof(f194,plain,(
% 0.21/0.57    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~v4_pre_topc(X1,sK1) | ~l1_pre_topc(sK1) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) )),
% 0.21/0.57    inference(resolution,[],[f69,f45])).
% 0.21/0.57  fof(f69,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f39])).
% 0.21/0.57  fof(f39,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.57    inference(flattening,[],[f38])).
% 0.21/0.57  fof(f38,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.57    inference(nnf_transformation,[],[f28])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.57    inference(flattening,[],[f27])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f8])).
% 0.21/0.57  fof(f8,axiom,(
% 0.21/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_pre_topc)).
% 0.21/0.57  fof(f296,plain,(
% 0.21/0.57    ~r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2)) | k2_struct_0(sK1) = k2_struct_0(sK2)),
% 0.21/0.57    inference(resolution,[],[f290,f74])).
% 0.21/0.57  fof(f74,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.57    inference(cnf_transformation,[],[f41])).
% 0.21/0.57  fof(f41,plain,(
% 0.21/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.57    inference(flattening,[],[f40])).
% 0.21/0.57  fof(f40,plain,(
% 0.21/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.57    inference(nnf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.57  fof(f290,plain,(
% 0.21/0.57    r1_tarski(k2_struct_0(sK2),k2_struct_0(sK1))),
% 0.21/0.57    inference(resolution,[],[f288,f75])).
% 0.21/0.57  fof(f288,plain,(
% 0.21/0.57    m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK1)))),
% 0.21/0.57    inference(subsumption_resolution,[],[f287,f47])).
% 0.21/0.57  fof(f47,plain,(
% 0.21/0.57    v2_pre_topc(sK2)),
% 0.21/0.57    inference(cnf_transformation,[],[f34])).
% 0.21/0.57  fof(f287,plain,(
% 0.21/0.57    m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK1))) | ~v2_pre_topc(sK2)),
% 0.21/0.57    inference(subsumption_resolution,[],[f286,f48])).
% 0.21/0.57  fof(f286,plain,(
% 0.21/0.57    m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK1))) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2)),
% 0.21/0.57    inference(subsumption_resolution,[],[f285,f90])).
% 0.21/0.57  fof(f285,plain,(
% 0.21/0.57    m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK1))) | ~m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2)),
% 0.21/0.57    inference(resolution,[],[f279,f64])).
% 0.21/0.57  fof(f279,plain,(
% 0.21/0.57    ( ! [X1] : (~v4_pre_topc(X1,sK2) | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2)))) )),
% 0.21/0.57    inference(forward_demodulation,[],[f278,f92])).
% 0.21/0.57  fof(f278,plain,(
% 0.21/0.57    ( ! [X1] : (~v4_pre_topc(X1,sK2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2))) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.21/0.57    inference(forward_demodulation,[],[f277,f49])).
% 0.21/0.57  fof(f277,plain,(
% 0.21/0.57    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2))) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.21/0.57    inference(forward_demodulation,[],[f276,f93])).
% 0.21/0.57  fof(f276,plain,(
% 0.21/0.57    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.21/0.57    inference(forward_demodulation,[],[f275,f49])).
% 0.21/0.57  fof(f275,plain,(
% 0.21/0.57    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f269,f46])).
% 0.21/0.57  fof(f269,plain,(
% 0.21/0.57    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK1) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.21/0.57    inference(resolution,[],[f71,f45])).
% 0.21/0.57  fof(f71,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f39])).
% 0.21/0.57  fof(f446,plain,(
% 0.21/0.57    ~v4_pre_topc(k2_struct_0(sK2),sK0) | v1_borsuk_1(sK2,sK0)),
% 0.21/0.57    inference(forward_demodulation,[],[f445,f93])).
% 0.21/0.57  fof(f445,plain,(
% 0.21/0.57    v1_borsuk_1(sK2,sK0) | ~v4_pre_topc(u1_struct_0(sK2),sK0)),
% 0.21/0.57    inference(subsumption_resolution,[],[f444,f43])).
% 0.21/0.57  fof(f43,plain,(
% 0.21/0.57    v2_pre_topc(sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f34])).
% 0.21/0.57  fof(f444,plain,(
% 0.21/0.57    v1_borsuk_1(sK2,sK0) | ~v4_pre_topc(u1_struct_0(sK2),sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.57    inference(subsumption_resolution,[],[f440,f44])).
% 0.21/0.57  fof(f44,plain,(
% 0.21/0.57    l1_pre_topc(sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f34])).
% 0.21/0.57  fof(f440,plain,(
% 0.21/0.57    ~l1_pre_topc(sK0) | v1_borsuk_1(sK2,sK0) | ~v4_pre_topc(u1_struct_0(sK2),sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.57    inference(resolution,[],[f430,f86])).
% 0.21/0.57  fof(f86,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v1_borsuk_1(X1,X0) | ~v4_pre_topc(u1_struct_0(X1),X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.57    inference(global_subsumption,[],[f59,f80])).
% 0.21/0.57  fof(f80,plain,(
% 0.21/0.57    ( ! [X0,X1] : (v1_borsuk_1(X1,X0) | ~v4_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.57    inference(equality_resolution,[],[f66])).
% 0.21/0.57  fof(f66,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (v1_borsuk_1(X1,X0) | ~v4_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f37])).
% 0.21/0.57  fof(f37,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) | ~v4_pre_topc(X2,X0)) & (v4_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.57    inference(flattening,[],[f36])).
% 0.21/0.57  fof(f36,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) | ~v4_pre_topc(X2,X0)) & (v4_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.57    inference(nnf_transformation,[],[f26])).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> v4_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.57    inference(flattening,[],[f25])).
% 0.21/0.57  fof(f25,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> v4_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f10])).
% 0.21/0.57  fof(f10,axiom,(
% 0.21/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> v4_pre_topc(X2,X0))))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tsep_1)).
% 0.21/0.57  fof(f59,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f19])).
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f12])).
% 0.21/0.57  fof(f12,axiom,(
% 0.21/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.21/0.57  fof(f430,plain,(
% 0.21/0.57    m1_pre_topc(sK2,sK0)),
% 0.21/0.57    inference(forward_demodulation,[],[f429,f49])).
% 0.21/0.57  fof(f429,plain,(
% 0.21/0.57    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0)),
% 0.21/0.57    inference(subsumption_resolution,[],[f422,f44])).
% 0.21/0.57  fof(f422,plain,(
% 0.21/0.57    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.57    inference(resolution,[],[f419,f61])).
% 0.21/0.57  fof(f61,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f20])).
% 0.21/0.57  fof(f20,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : ((m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f9])).
% 0.21/0.57  fof(f9,axiom,(
% 0.21/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tmap_1)).
% 0.21/0.57  fof(f419,plain,(
% 0.21/0.57    m1_pre_topc(sK1,sK0)),
% 0.21/0.57    inference(subsumption_resolution,[],[f418,f44])).
% 0.21/0.57  fof(f418,plain,(
% 0.21/0.57    m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f417])).
% 0.21/0.57  fof(f417,plain,(
% 0.21/0.57    m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | m1_pre_topc(sK1,sK0)),
% 0.21/0.57    inference(resolution,[],[f409,f53])).
% 0.21/0.57  fof(f53,plain,(
% 0.21/0.57    m1_pre_topc(sK2,sK0) | m1_pre_topc(sK1,sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f34])).
% 0.21/0.57  fof(f409,plain,(
% 0.21/0.57    ( ! [X1] : (~m1_pre_topc(sK2,X1) | m1_pre_topc(sK1,X1) | ~l1_pre_topc(X1)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f408,f47])).
% 0.21/0.57  fof(f408,plain,(
% 0.21/0.57    ( ! [X1] : (~v2_pre_topc(sK2) | ~m1_pre_topc(sK2,X1) | m1_pre_topc(sK1,X1) | ~l1_pre_topc(X1)) )),
% 0.21/0.57    inference(forward_demodulation,[],[f407,f49])).
% 0.21/0.57  fof(f407,plain,(
% 0.21/0.57    ( ! [X1] : (~m1_pre_topc(sK2,X1) | m1_pre_topc(sK1,X1) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(X1)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f406,f48])).
% 0.21/0.57  fof(f406,plain,(
% 0.21/0.57    ( ! [X1] : (~l1_pre_topc(sK2) | ~m1_pre_topc(sK2,X1) | m1_pre_topc(sK1,X1) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(X1)) )),
% 0.21/0.57    inference(forward_demodulation,[],[f405,f49])).
% 0.21/0.57  fof(f405,plain,(
% 0.21/0.57    ( ! [X1] : (~m1_pre_topc(sK2,X1) | m1_pre_topc(sK1,X1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(X1)) )),
% 0.21/0.57    inference(forward_demodulation,[],[f404,f49])).
% 0.21/0.57  fof(f404,plain,(
% 0.21/0.57    ( ! [X1] : (~m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1) | m1_pre_topc(sK1,X1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(X1)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f398,f46])).
% 0.21/0.57  fof(f398,plain,(
% 0.21/0.57    ( ! [X1] : (~m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1) | ~l1_pre_topc(sK1) | m1_pre_topc(sK1,X1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(X1)) )),
% 0.21/0.57    inference(resolution,[],[f78,f45])).
% 0.21/0.57  fof(f78,plain,(
% 0.21/0.57    ( ! [X2,X0] : (~v2_pre_topc(X2) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0) | ~l1_pre_topc(X2) | m1_pre_topc(X2,X0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~l1_pre_topc(X0)) )),
% 0.21/0.57    inference(equality_resolution,[],[f62])).
% 0.21/0.57  fof(f62,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f35])).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) & (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0))) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.57    inference(nnf_transformation,[],[f22])).
% 0.21/0.57  fof(f22,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.57    inference(flattening,[],[f21])).
% 0.21/0.57  fof(f21,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | ~l1_pre_topc(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f11])).
% 0.21/0.57  fof(f11,axiom,(
% 0.21/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1 => (m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0))))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tmap_1)).
% 0.21/0.57  fof(f438,plain,(
% 0.21/0.57    v4_pre_topc(k2_struct_0(sK1),sK0)),
% 0.21/0.57    inference(forward_demodulation,[],[f437,f92])).
% 0.21/0.57  fof(f437,plain,(
% 0.21/0.57    v4_pre_topc(u1_struct_0(sK1),sK0)),
% 0.21/0.57    inference(subsumption_resolution,[],[f436,f419])).
% 0.21/0.57  fof(f436,plain,(
% 0.21/0.57    ~m1_pre_topc(sK1,sK0) | v4_pre_topc(u1_struct_0(sK1),sK0)),
% 0.21/0.57    inference(resolution,[],[f428,f162])).
% 0.21/0.57  fof(f162,plain,(
% 0.21/0.57    ( ! [X0] : (~v1_borsuk_1(X0,sK0) | ~m1_pre_topc(X0,sK0) | v4_pre_topc(u1_struct_0(X0),sK0)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f159,f44])).
% 0.21/0.57  fof(f159,plain,(
% 0.21/0.57    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~v1_borsuk_1(X0,sK0) | ~l1_pre_topc(sK0) | v4_pre_topc(u1_struct_0(X0),sK0)) )),
% 0.21/0.57    inference(resolution,[],[f158,f43])).
% 0.21/0.57  fof(f158,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0) | ~l1_pre_topc(X0) | v4_pre_topc(u1_struct_0(X1),X0)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f84,f59])).
% 0.21/0.57  fof(f84,plain,(
% 0.21/0.57    ( ! [X0,X1] : (v4_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f81])).
% 0.21/0.57  fof(f81,plain,(
% 0.21/0.57    ( ! [X0,X1] : (v4_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.57    inference(equality_resolution,[],[f65])).
% 0.21/0.57  fof(f65,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (v4_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f37])).
% 0.21/0.57  fof(f428,plain,(
% 0.21/0.57    v1_borsuk_1(sK1,sK0)),
% 0.21/0.57    inference(subsumption_resolution,[],[f427,f313])).
% 0.21/0.57  fof(f313,plain,(
% 0.21/0.57    v4_pre_topc(k2_struct_0(sK1),sK0) | v1_borsuk_1(sK1,sK0)),
% 0.21/0.57    inference(superposition,[],[f171,f297])).
% 0.21/0.57  fof(f171,plain,(
% 0.21/0.57    v4_pre_topc(k2_struct_0(sK2),sK0) | v1_borsuk_1(sK1,sK0)),
% 0.21/0.57    inference(forward_demodulation,[],[f170,f93])).
% 0.21/0.57  fof(f170,plain,(
% 0.21/0.57    v4_pre_topc(u1_struct_0(sK2),sK0) | v1_borsuk_1(sK1,sK0)),
% 0.21/0.57    inference(subsumption_resolution,[],[f166,f52])).
% 0.21/0.57  fof(f52,plain,(
% 0.21/0.57    v1_borsuk_1(sK1,sK0) | m1_pre_topc(sK2,sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f34])).
% 0.21/0.57  fof(f166,plain,(
% 0.21/0.57    ~m1_pre_topc(sK2,sK0) | v4_pre_topc(u1_struct_0(sK2),sK0) | v1_borsuk_1(sK1,sK0)),
% 0.21/0.57    inference(resolution,[],[f162,f50])).
% 0.21/0.57  fof(f50,plain,(
% 0.21/0.57    v1_borsuk_1(sK2,sK0) | v1_borsuk_1(sK1,sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f34])).
% 0.21/0.57  fof(f427,plain,(
% 0.21/0.57    ~v4_pre_topc(k2_struct_0(sK1),sK0) | v1_borsuk_1(sK1,sK0)),
% 0.21/0.57    inference(forward_demodulation,[],[f426,f92])).
% 0.21/0.57  fof(f426,plain,(
% 0.21/0.57    v1_borsuk_1(sK1,sK0) | ~v4_pre_topc(u1_struct_0(sK1),sK0)),
% 0.21/0.57    inference(subsumption_resolution,[],[f425,f43])).
% 0.21/0.57  fof(f425,plain,(
% 0.21/0.57    v1_borsuk_1(sK1,sK0) | ~v4_pre_topc(u1_struct_0(sK1),sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.57    inference(subsumption_resolution,[],[f421,f44])).
% 0.21/0.57  fof(f421,plain,(
% 0.21/0.57    ~l1_pre_topc(sK0) | v1_borsuk_1(sK1,sK0) | ~v4_pre_topc(u1_struct_0(sK1),sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.57    inference(resolution,[],[f419,f86])).
% 0.21/0.57  fof(f420,plain,(
% 0.21/0.57    ~v1_borsuk_1(sK2,sK0) | ~m1_pre_topc(sK2,sK0) | ~v1_borsuk_1(sK1,sK0)),
% 0.21/0.57    inference(resolution,[],[f419,f54])).
% 0.21/0.57  fof(f54,plain,(
% 0.21/0.57    ~m1_pre_topc(sK1,sK0) | ~v1_borsuk_1(sK2,sK0) | ~m1_pre_topc(sK2,sK0) | ~v1_borsuk_1(sK1,sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f34])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (20440)------------------------------
% 0.21/0.57  % (20440)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (20440)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (20440)Memory used [KB]: 6524
% 0.21/0.57  % (20444)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.57  % (20440)Time elapsed: 0.141 s
% 0.21/0.57  % (20440)------------------------------
% 0.21/0.57  % (20440)------------------------------
% 0.21/0.57  % (20438)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.58  % (20418)Success in time 0.214 s
%------------------------------------------------------------------------------
