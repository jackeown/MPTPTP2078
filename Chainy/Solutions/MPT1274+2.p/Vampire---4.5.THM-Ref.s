%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1274+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:15 EST 2020

% Result     : Theorem 1.13s
% Output     : Refutation 1.13s
% Verified   : 
% Statistics : Number of formulae       :   25 (  69 expanded)
%              Number of leaves         :    5 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :   93 ( 353 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3459,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3458,f2654])).

fof(f2654,plain,(
    v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f2510])).

fof(f2510,plain,
    ( ~ v3_tops_1(sK1,sK0)
    & v4_pre_topc(sK1,sK0)
    & v2_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f2236,f2509,f2508])).

fof(f2508,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v3_tops_1(X1,X0)
            & v4_pre_topc(X1,X0)
            & v2_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v3_tops_1(X1,sK0)
          & v4_pre_topc(X1,sK0)
          & v2_tops_1(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2509,plain,
    ( ? [X1] :
        ( ~ v3_tops_1(X1,sK0)
        & v4_pre_topc(X1,sK0)
        & v2_tops_1(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v3_tops_1(sK1,sK0)
      & v4_pre_topc(sK1,sK0)
      & v2_tops_1(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f2236,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tops_1(X1,X0)
          & v4_pre_topc(X1,X0)
          & v2_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2235])).

fof(f2235,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tops_1(X1,X0)
          & v4_pre_topc(X1,X0)
          & v2_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2178])).

fof(f2178,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( v4_pre_topc(X1,X0)
                & v2_tops_1(X1,X0) )
             => v3_tops_1(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f2177])).

% (19693)lrs-11_3_av=off:bs=unit_only:bsr=on:cond=on:gsp=input_only:gs=on:gsem=on:lma=on:nm=2:nwc=1:stl=30:sd=3:ss=axioms:st=1.2:sos=all:sp=reverse_arity:urr=on:updr=off_11 on theBenchmark
fof(f2177,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v4_pre_topc(X1,X0)
              & v2_tops_1(X1,X0) )
           => v3_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_tops_1)).

fof(f3458,plain,(
    ~ v2_tops_1(sK1,sK0) ),
    inference(forward_demodulation,[],[f3167,f3174])).

fof(f3174,plain,(
    sK1 = k2_pre_topc(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f2652,f2655,f2653,f2672])).

fof(f2672,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2251])).

fof(f2251,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2250])).

fof(f2250,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2188])).

fof(f2188,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => k2_pre_topc(X0,X1) = X1 ) ) ) ),
    inference(pure_predicate_removal,[],[f1843])).

fof(f1843,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f2653,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f2510])).

fof(f2655,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f2510])).

fof(f2652,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f2510])).

fof(f3167,plain,(
    ~ v2_tops_1(k2_pre_topc(sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f2652,f2656,f2653,f2658])).

fof(f2658,plain,(
    ! [X0,X1] :
      ( ~ v2_tops_1(k2_pre_topc(X0,X1),X0)
      | v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2511])).

fof(f2511,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tops_1(X1,X0)
              | ~ v2_tops_1(k2_pre_topc(X0,X1),X0) )
            & ( v2_tops_1(k2_pre_topc(X0,X1),X0)
              | ~ v3_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f2237])).

fof(f2237,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2094])).

fof(f2094,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tops_1)).

fof(f2656,plain,(
    ~ v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f2510])).
%------------------------------------------------------------------------------
