%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  150 (4590 expanded)
%              Number of leaves         :   15 (1408 expanded)
%              Depth                    :   42
%              Number of atoms          :  657 (51842 expanded)
%              Number of equality atoms :   44 (4374 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f394,plain,(
    $false ),
    inference(subsumption_resolution,[],[f393,f389])).

fof(f389,plain,(
    v3_pre_topc(k2_struct_0(sK1),sK0) ),
    inference(subsumption_resolution,[],[f366,f388])).

fof(f388,plain,(
    v1_tsep_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f48,f387])).

fof(f387,plain,(
    ~ v1_tsep_1(sK2,sK0) ),
    inference(global_subsumption,[],[f363,f369,f386])).

fof(f386,plain,
    ( v3_pre_topc(k2_struct_0(sK1),sK0)
    | ~ v1_tsep_1(sK2,sK0) ),
    inference(forward_demodulation,[],[f385,f236])).

fof(f236,plain,(
    u1_struct_0(sK2) = k2_struct_0(sK1) ),
    inference(backward_demodulation,[],[f89,f235])).

fof(f235,plain,(
    k2_struct_0(sK1) = k2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f192,f234])).

fof(f234,plain,(
    r1_tarski(k2_struct_0(sK2),k2_struct_0(sK1)) ),
    inference(resolution,[],[f229,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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

fof(f229,plain,(
    m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f228,f45])).

fof(f45,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( ~ m1_pre_topc(sK2,sK0)
      | ~ v1_tsep_1(sK2,sK0)
      | ~ m1_pre_topc(sK1,sK0)
      | ~ v1_tsep_1(sK1,sK0) )
    & ( ( m1_pre_topc(sK2,sK0)
        & v1_tsep_1(sK2,sK0) )
      | ( m1_pre_topc(sK1,sK0)
        & v1_tsep_1(sK1,sK0) ) )
    & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f31,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_pre_topc(X2,X0)
                  | ~ v1_tsep_1(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) )
                & ( ( m1_pre_topc(X2,X0)
                    & v1_tsep_1(X2,X0) )
                  | ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) ) )
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
                | ~ v1_tsep_1(X2,sK0)
                | ~ m1_pre_topc(X1,sK0)
                | ~ v1_tsep_1(X1,sK0) )
              & ( ( m1_pre_topc(X2,sK0)
                  & v1_tsep_1(X2,sK0) )
                | ( m1_pre_topc(X1,sK0)
                  & v1_tsep_1(X1,sK0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ m1_pre_topc(X2,sK0)
              | ~ v1_tsep_1(X2,sK0)
              | ~ m1_pre_topc(X1,sK0)
              | ~ v1_tsep_1(X1,sK0) )
            & ( ( m1_pre_topc(X2,sK0)
                & v1_tsep_1(X2,sK0) )
              | ( m1_pre_topc(X1,sK0)
                & v1_tsep_1(X1,sK0) ) )
            & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
            & l1_pre_topc(X2)
            & v2_pre_topc(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1) )
   => ( ? [X2] :
          ( ( ~ m1_pre_topc(X2,sK0)
            | ~ v1_tsep_1(X2,sK0)
            | ~ m1_pre_topc(sK1,sK0)
            | ~ v1_tsep_1(sK1,sK0) )
          & ( ( m1_pre_topc(X2,sK0)
              & v1_tsep_1(X2,sK0) )
            | ( m1_pre_topc(sK1,sK0)
              & v1_tsep_1(sK1,sK0) ) )
          & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = X2
          & l1_pre_topc(X2)
          & v2_pre_topc(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X2] :
        ( ( ~ m1_pre_topc(X2,sK0)
          | ~ v1_tsep_1(X2,sK0)
          | ~ m1_pre_topc(sK1,sK0)
          | ~ v1_tsep_1(sK1,sK0) )
        & ( ( m1_pre_topc(X2,sK0)
            & v1_tsep_1(X2,sK0) )
          | ( m1_pre_topc(sK1,sK0)
            & v1_tsep_1(sK1,sK0) ) )
        & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = X2
        & l1_pre_topc(X2)
        & v2_pre_topc(X2) )
   => ( ( ~ m1_pre_topc(sK2,sK0)
        | ~ v1_tsep_1(sK2,sK0)
        | ~ m1_pre_topc(sK1,sK0)
        | ~ v1_tsep_1(sK1,sK0) )
      & ( ( m1_pre_topc(sK2,sK0)
          & v1_tsep_1(sK2,sK0) )
        | ( m1_pre_topc(sK1,sK0)
          & v1_tsep_1(sK1,sK0) ) )
      & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,X0)
                | ~ v1_tsep_1(X2,X0)
                | ~ m1_pre_topc(X1,X0)
                | ~ v1_tsep_1(X1,X0) )
              & ( ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0) )
                | ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,X0)
                | ~ v1_tsep_1(X2,X0)
                | ~ m1_pre_topc(X1,X0)
                | ~ v1_tsep_1(X1,X0) )
              & ( ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0) )
                | ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <~> ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <~> ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
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
                      & v1_tsep_1(X1,X0) )
                  <=> ( m1_pre_topc(X2,X0)
                      & v1_tsep_1(X2,X0) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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
                    & v1_tsep_1(X1,X0) )
                <=> ( m1_pre_topc(X2,X0)
                    & v1_tsep_1(X2,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_tmap_1)).

% (3779)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
fof(f228,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK1)))
    | ~ v2_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f227,f46])).

fof(f46,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f227,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK1)))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f226,f81])).

fof(f81,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f54,f53])).

fof(f53,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f54,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

% (3783)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
fof(f226,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK1)))
    | ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(resolution,[],[f220,f60])).

fof(f60,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f220,plain,(
    ! [X1] :
      ( ~ v3_pre_topc(X1,sK2)
      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2))) ) ),
    inference(forward_demodulation,[],[f219,f88])).

fof(f88,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f55,f85])).

% (3776)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
fof(f85,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f56,f44])).

fof(f44,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f56,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f55,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f219,plain,(
    ! [X1] :
      ( ~ v3_pre_topc(X1,sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2)))
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(forward_demodulation,[],[f218,f90])).

fof(f90,plain,(
    sK2 = g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(backward_demodulation,[],[f47,f88])).

fof(f47,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2 ),
    inference(cnf_transformation,[],[f32])).

fof(f218,plain,(
    ! [X1] :
      ( ~ v3_pre_topc(X1,g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2)))
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(forward_demodulation,[],[f217,f88])).

fof(f217,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2)))
      | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(forward_demodulation,[],[f216,f89])).

fof(f216,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(forward_demodulation,[],[f215,f90])).

fof(f215,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)))))
      | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(forward_demodulation,[],[f214,f88])).

fof(f214,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
      | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(subsumption_resolution,[],[f208,f44])).

fof(f208,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
      | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ l1_pre_topc(sK1)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(resolution,[],[f67,f43])).

fof(f43,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v3_pre_topc(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v3_pre_topc(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v3_pre_topc(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v3_pre_topc(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_pre_topc)).

fof(f192,plain,
    ( ~ r1_tarski(k2_struct_0(sK2),k2_struct_0(sK1))
    | k2_struct_0(sK1) = k2_struct_0(sK2) ),
    inference(resolution,[],[f191,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
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

fof(f191,plain,(
    r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2)) ),
    inference(resolution,[],[f185,f71])).

fof(f185,plain,(
    m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f184,f43])).

fof(f184,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f183,f44])).

fof(f183,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f182,f81])).

fof(f182,plain,
    ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1)))
    | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(resolution,[],[f149,f60])).

fof(f149,plain,(
    ! [X1] :
      ( ~ v3_pre_topc(X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1)))
      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2))) ) ),
    inference(forward_demodulation,[],[f148,f89])).

fof(f148,plain,(
    ! [X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1)))
      | ~ v3_pre_topc(X1,sK1) ) ),
    inference(forward_demodulation,[],[f147,f90])).

fof(f147,plain,(
    ! [X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1)))
      | ~ v3_pre_topc(X1,sK1) ) ),
    inference(forward_demodulation,[],[f146,f88])).

fof(f146,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1)))
      | ~ v3_pre_topc(X1,sK1)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ) ),
    inference(forward_demodulation,[],[f145,f88])).

fof(f145,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v3_pre_topc(X1,sK1)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ) ),
    inference(subsumption_resolution,[],[f140,f44])).

fof(f140,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v3_pre_topc(X1,sK1)
      | ~ l1_pre_topc(sK1)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ) ),
    inference(resolution,[],[f65,f43])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f89,plain,(
    u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(resolution,[],[f55,f86])).

fof(f86,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f56,f46])).

fof(f385,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK0)
    | ~ v1_tsep_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f384,f41])).

fof(f41,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f384,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK0)
    | ~ v1_tsep_1(sK2,sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f375,f42])).

fof(f42,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f375,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK0)
    | ~ v1_tsep_1(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f362,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v3_pre_topc(u1_struct_0(X1),X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f80,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f80,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
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
                    & v1_tsep_1(X1,X0) )
                <=> v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).

fof(f362,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(subsumption_resolution,[],[f361,f45])).

fof(f361,plain,
    ( ~ v2_pre_topc(sK2)
    | m1_pre_topc(sK2,sK0) ),
    inference(forward_demodulation,[],[f360,f90])).

fof(f360,plain,
    ( ~ v2_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)))
    | m1_pre_topc(sK2,sK0) ),
    inference(forward_demodulation,[],[f359,f88])).

fof(f359,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(subsumption_resolution,[],[f358,f46])).

fof(f358,plain,
    ( ~ l1_pre_topc(sK2)
    | m1_pre_topc(sK2,sK0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(forward_demodulation,[],[f357,f90])).

fof(f357,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)))
    | m1_pre_topc(sK2,sK0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(forward_demodulation,[],[f356,f88])).

fof(f356,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(forward_demodulation,[],[f355,f90])).

fof(f355,plain,
    ( m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),sK0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(forward_demodulation,[],[f354,f88])).

fof(f354,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(subsumption_resolution,[],[f353,f42])).

fof(f353,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f352,f43])).

fof(f352,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f348,f44])).

fof(f348,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f346,f73])).

fof(f73,plain,(
    ! [X2,X0] :
      ( ~ m1_pre_topc(X2,X0)
      | m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f346,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f345,f42])).

fof(f345,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(duplicate_literal_removal,[],[f344])).

fof(f344,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | m1_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f341,f51])).

fof(f51,plain,
    ( m1_pre_topc(sK2,sK0)
    | m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f341,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(sK2,X1)
      | m1_pre_topc(sK1,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(subsumption_resolution,[],[f340,f46])).

fof(f340,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(sK2)
      | ~ m1_pre_topc(sK2,X1)
      | m1_pre_topc(sK1,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(forward_demodulation,[],[f339,f90])).

fof(f339,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(sK2,X1)
      | ~ l1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)))
      | m1_pre_topc(sK1,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(forward_demodulation,[],[f338,f90])).

fof(f338,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X1)
      | ~ l1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)))
      | m1_pre_topc(sK1,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(subsumption_resolution,[],[f337,f45])).

% (3773)Refutation not found, incomplete strategy% (3773)------------------------------
% (3773)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3773)Termination reason: Refutation not found, incomplete strategy

% (3773)Memory used [KB]: 6140
% (3773)Time elapsed: 0.101 s
% (3773)------------------------------
% (3773)------------------------------
fof(f337,plain,(
    ! [X1] :
      ( ~ v2_pre_topc(sK2)
      | ~ m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X1)
      | ~ l1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)))
      | m1_pre_topc(sK1,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(forward_demodulation,[],[f336,f90])).

fof(f336,plain,(
    ! [X1] :
      ( ~ v2_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X1)
      | ~ l1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)))
      | m1_pre_topc(sK1,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(subsumption_resolution,[],[f335,f43])).

fof(f335,plain,(
    ! [X1] :
      ( ~ v2_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)))
      | m1_pre_topc(sK1,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(subsumption_resolution,[],[f331,f44])).

fof(f331,plain,(
    ! [X1] :
      ( ~ v2_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)))
      | m1_pre_topc(sK1,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(superposition,[],[f74,f88])).

fof(f74,plain,(
    ! [X2,X0] :
      ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f369,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK1),sK0)
    | v1_tsep_1(sK1,sK0) ),
    inference(forward_demodulation,[],[f368,f88])).

fof(f368,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | v1_tsep_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f367,f41])).

fof(f367,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | v1_tsep_1(sK1,sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f350,f42])).

fof(f350,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | v1_tsep_1(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f346,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | v1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f76,f57])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f363,plain,
    ( ~ v1_tsep_1(sK2,sK0)
    | ~ v1_tsep_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f347,f362])).

fof(f347,plain,
    ( ~ v1_tsep_1(sK2,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_tsep_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f52,f346])).

fof(f52,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ v1_tsep_1(sK2,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_tsep_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f48,plain,
    ( v1_tsep_1(sK2,sK0)
    | v1_tsep_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f366,plain,
    ( v3_pre_topc(k2_struct_0(sK1),sK0)
    | ~ v1_tsep_1(sK1,sK0) ),
    inference(forward_demodulation,[],[f365,f88])).

fof(f365,plain,
    ( v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ v1_tsep_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f364,f41])).

fof(f364,plain,
    ( v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ v1_tsep_1(sK1,sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f349,f42])).

fof(f349,plain,
    ( v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ v1_tsep_1(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f346,f83])).

fof(f393,plain,(
    ~ v3_pre_topc(k2_struct_0(sK1),sK0) ),
    inference(forward_demodulation,[],[f392,f236])).

fof(f392,plain,(
    ~ v3_pre_topc(u1_struct_0(sK2),sK0) ),
    inference(subsumption_resolution,[],[f391,f41])).

fof(f391,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK2),sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f390,f42])).

fof(f390,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK2),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f376,f387])).

fof(f376,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK2),sK0)
    | v1_tsep_1(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f362,f82])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:26:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (3777)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.50  % (3774)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.50  % (3771)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (3781)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (3774)Refutation not found, incomplete strategy% (3774)------------------------------
% 0.21/0.50  % (3774)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (3769)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (3778)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.51  % (3773)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (3772)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (3789)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.52  % (3784)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.52  % (3792)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.52  % (3771)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (3774)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (3774)Memory used [KB]: 10618
% 0.21/0.52  % (3774)Time elapsed: 0.085 s
% 0.21/0.52  % (3774)------------------------------
% 0.21/0.52  % (3774)------------------------------
% 0.21/0.52  % (3786)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.52  % (3782)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (3788)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.52  % (3785)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.52  % (3791)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.53  % (3780)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.53  % (3770)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.53  % (3781)Refutation not found, incomplete strategy% (3781)------------------------------
% 0.21/0.53  % (3781)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (3781)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (3781)Memory used [KB]: 6268
% 0.21/0.53  % (3781)Time elapsed: 0.111 s
% 0.21/0.53  % (3781)------------------------------
% 0.21/0.53  % (3781)------------------------------
% 0.21/0.53  % (3793)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f394,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(subsumption_resolution,[],[f393,f389])).
% 0.21/0.53  fof(f389,plain,(
% 0.21/0.53    v3_pre_topc(k2_struct_0(sK1),sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f366,f388])).
% 0.21/0.53  fof(f388,plain,(
% 0.21/0.53    v1_tsep_1(sK1,sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f48,f387])).
% 0.21/0.53  fof(f387,plain,(
% 0.21/0.53    ~v1_tsep_1(sK2,sK0)),
% 0.21/0.53    inference(global_subsumption,[],[f363,f369,f386])).
% 0.21/0.53  fof(f386,plain,(
% 0.21/0.53    v3_pre_topc(k2_struct_0(sK1),sK0) | ~v1_tsep_1(sK2,sK0)),
% 0.21/0.53    inference(forward_demodulation,[],[f385,f236])).
% 0.21/0.53  fof(f236,plain,(
% 0.21/0.53    u1_struct_0(sK2) = k2_struct_0(sK1)),
% 0.21/0.53    inference(backward_demodulation,[],[f89,f235])).
% 0.21/0.53  fof(f235,plain,(
% 0.21/0.53    k2_struct_0(sK1) = k2_struct_0(sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f192,f234])).
% 0.21/0.53  fof(f234,plain,(
% 0.21/0.53    r1_tarski(k2_struct_0(sK2),k2_struct_0(sK1))),
% 0.21/0.53    inference(resolution,[],[f229,f71])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.53    inference(nnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.53  fof(f229,plain,(
% 0.21/0.53    m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK1)))),
% 0.21/0.53    inference(subsumption_resolution,[],[f228,f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    v2_pre_topc(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    (((~m1_pre_topc(sK2,sK0) | ~v1_tsep_1(sK2,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_tsep_1(sK1,sK0)) & ((m1_pre_topc(sK2,sK0) & v1_tsep_1(sK2,sK0)) | (m1_pre_topc(sK1,sK0) & v1_tsep_1(sK1,sK0))) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2 & l1_pre_topc(sK2) & v2_pre_topc(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f31,f30,f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : ((~m1_pre_topc(X2,sK0) | ~v1_tsep_1(X2,sK0) | ~m1_pre_topc(X1,sK0) | ~v1_tsep_1(X1,sK0)) & ((m1_pre_topc(X2,sK0) & v1_tsep_1(X2,sK0)) | (m1_pre_topc(X1,sK0) & v1_tsep_1(X1,sK0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ? [X1] : (? [X2] : ((~m1_pre_topc(X2,sK0) | ~v1_tsep_1(X2,sK0) | ~m1_pre_topc(X1,sK0) | ~v1_tsep_1(X1,sK0)) & ((m1_pre_topc(X2,sK0) & v1_tsep_1(X2,sK0)) | (m1_pre_topc(X1,sK0) & v1_tsep_1(X1,sK0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : ((~m1_pre_topc(X2,sK0) | ~v1_tsep_1(X2,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_tsep_1(sK1,sK0)) & ((m1_pre_topc(X2,sK0) & v1_tsep_1(X2,sK0)) | (m1_pre_topc(sK1,sK0) & v1_tsep_1(sK1,sK0))) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ? [X2] : ((~m1_pre_topc(X2,sK0) | ~v1_tsep_1(X2,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_tsep_1(sK1,sK0)) & ((m1_pre_topc(X2,sK0) & v1_tsep_1(X2,sK0)) | (m1_pre_topc(sK1,sK0) & v1_tsep_1(sK1,sK0))) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) => ((~m1_pre_topc(sK2,sK0) | ~v1_tsep_1(sK2,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_tsep_1(sK1,sK0)) & ((m1_pre_topc(sK2,sK0) & v1_tsep_1(sK2,sK0)) | (m1_pre_topc(sK1,sK0) & v1_tsep_1(sK1,sK0))) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2 & l1_pre_topc(sK2) & v2_pre_topc(sK2))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : ((((~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0)) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) & ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2) & (l1_pre_topc(X2) & v2_pre_topc(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,negated_conjecture,(
% 0.21/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)))))))),
% 0.21/0.53    inference(negated_conjecture,[],[f12])).
% 0.21/0.53  fof(f12,conjecture,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_tmap_1)).
% 0.21/0.53  % (3779)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.53  fof(f228,plain,(
% 0.21/0.53    m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK1))) | ~v2_pre_topc(sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f227,f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    l1_pre_topc(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f227,plain,(
% 0.21/0.53    m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK1))) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f226,f81])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f54,f53])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.53  % (3783)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.53  fof(f226,plain,(
% 0.21/0.53    m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK1))) | ~m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2)),
% 0.21/0.53    inference(resolution,[],[f220,f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).
% 0.21/0.53  fof(f220,plain,(
% 0.21/0.53    ( ! [X1] : (~v3_pre_topc(X1,sK2) | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2)))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f219,f88])).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.21/0.53    inference(resolution,[],[f55,f85])).
% 0.21/0.53  % (3776)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    l1_struct_0(sK1)),
% 0.21/0.53    inference(resolution,[],[f56,f44])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    l1_pre_topc(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.53  fof(f219,plain,(
% 0.21/0.53    ( ! [X1] : (~v3_pre_topc(X1,sK2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2))) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f218,f90])).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    sK2 = g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),
% 0.21/0.53    inference(backward_demodulation,[],[f47,f88])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f218,plain,(
% 0.21/0.53    ( ! [X1] : (~v3_pre_topc(X1,g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2))) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f217,f88])).
% 0.21/0.53  fof(f217,plain,(
% 0.21/0.53    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f216,f89])).
% 0.21/0.53  fof(f216,plain,(
% 0.21/0.53    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f215,f90])).
% 0.21/0.53  fof(f215,plain,(
% 0.21/0.53    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f214,f88])).
% 0.21/0.53  fof(f214,plain,(
% 0.21/0.53    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f208,f44])).
% 0.21/0.53  fof(f208,plain,(
% 0.21/0.53    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK1) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.21/0.53    inference(resolution,[],[f67,f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    v2_pre_topc(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_pre_topc)).
% 0.21/0.53  fof(f192,plain,(
% 0.21/0.53    ~r1_tarski(k2_struct_0(sK2),k2_struct_0(sK1)) | k2_struct_0(sK1) = k2_struct_0(sK2)),
% 0.21/0.53    inference(resolution,[],[f191,f70])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.53    inference(flattening,[],[f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.53  fof(f191,plain,(
% 0.21/0.53    r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2))),
% 0.21/0.53    inference(resolution,[],[f185,f71])).
% 0.21/0.53  fof(f185,plain,(
% 0.21/0.53    m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK2)))),
% 0.21/0.53    inference(subsumption_resolution,[],[f184,f43])).
% 0.21/0.53  fof(f184,plain,(
% 0.21/0.53    m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK2))) | ~v2_pre_topc(sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f183,f44])).
% 0.21/0.53  fof(f183,plain,(
% 0.21/0.53    m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK2))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f182,f81])).
% 0.21/0.53  fof(f182,plain,(
% 0.21/0.53    ~m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK2))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)),
% 0.21/0.53    inference(resolution,[],[f149,f60])).
% 0.21/0.53  fof(f149,plain,(
% 0.21/0.53    ( ! [X1] : (~v3_pre_topc(X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1))) | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2)))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f148,f89])).
% 0.21/0.53  fof(f148,plain,(
% 0.21/0.53    ( ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1))) | ~v3_pre_topc(X1,sK1)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f147,f90])).
% 0.21/0.53  fof(f147,plain,(
% 0.21/0.53    ( ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1))) | ~v3_pre_topc(X1,sK1)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f146,f88])).
% 0.21/0.53  fof(f146,plain,(
% 0.21/0.53    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1))) | ~v3_pre_topc(X1,sK1) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f145,f88])).
% 0.21/0.53  fof(f145,plain,(
% 0.21/0.53    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~v3_pre_topc(X1,sK1) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f140,f44])).
% 0.21/0.53  fof(f140,plain,(
% 0.21/0.53    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~v3_pre_topc(X1,sK1) | ~l1_pre_topc(sK1) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) )),
% 0.21/0.53    inference(resolution,[],[f65,f43])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f37])).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    u1_struct_0(sK2) = k2_struct_0(sK2)),
% 0.21/0.53    inference(resolution,[],[f55,f86])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    l1_struct_0(sK2)),
% 0.21/0.53    inference(resolution,[],[f56,f46])).
% 0.21/0.53  fof(f385,plain,(
% 0.21/0.53    v3_pre_topc(u1_struct_0(sK2),sK0) | ~v1_tsep_1(sK2,sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f384,f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    v2_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f384,plain,(
% 0.21/0.53    v3_pre_topc(u1_struct_0(sK2),sK0) | ~v1_tsep_1(sK2,sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f375,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    l1_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f375,plain,(
% 0.21/0.53    v3_pre_topc(u1_struct_0(sK2),sK0) | ~v1_tsep_1(sK2,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.53    inference(resolution,[],[f362,f83])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v3_pre_topc(u1_struct_0(X1),X0) | ~v1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f80,f57])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f77])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f61])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).
% 0.21/0.53  fof(f362,plain,(
% 0.21/0.53    m1_pre_topc(sK2,sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f361,f45])).
% 0.21/0.53  fof(f361,plain,(
% 0.21/0.53    ~v2_pre_topc(sK2) | m1_pre_topc(sK2,sK0)),
% 0.21/0.53    inference(forward_demodulation,[],[f360,f90])).
% 0.21/0.53  fof(f360,plain,(
% 0.21/0.53    ~v2_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))) | m1_pre_topc(sK2,sK0)),
% 0.21/0.53    inference(forward_demodulation,[],[f359,f88])).
% 0.21/0.53  fof(f359,plain,(
% 0.21/0.53    m1_pre_topc(sK2,sK0) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.21/0.53    inference(subsumption_resolution,[],[f358,f46])).
% 0.21/0.53  fof(f358,plain,(
% 0.21/0.53    ~l1_pre_topc(sK2) | m1_pre_topc(sK2,sK0) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.21/0.53    inference(forward_demodulation,[],[f357,f90])).
% 0.21/0.53  fof(f357,plain,(
% 0.21/0.53    ~l1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))) | m1_pre_topc(sK2,sK0) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.21/0.53    inference(forward_demodulation,[],[f356,f88])).
% 0.21/0.53  fof(f356,plain,(
% 0.21/0.53    m1_pre_topc(sK2,sK0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.21/0.53    inference(forward_demodulation,[],[f355,f90])).
% 0.21/0.53  fof(f355,plain,(
% 0.21/0.53    m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),sK0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.21/0.53    inference(forward_demodulation,[],[f354,f88])).
% 0.21/0.53  fof(f354,plain,(
% 0.21/0.53    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.21/0.53    inference(subsumption_resolution,[],[f353,f42])).
% 0.21/0.53  fof(f353,plain,(
% 0.21/0.53    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f352,f43])).
% 0.21/0.53  fof(f352,plain,(
% 0.21/0.53    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f348,f44])).
% 0.21/0.53  fof(f348,plain,(
% 0.21/0.53    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(resolution,[],[f346,f73])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    ( ! [X2,X0] : (~m1_pre_topc(X2,X0) | m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) & (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0))) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1 => (m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tmap_1)).
% 0.21/0.53  fof(f346,plain,(
% 0.21/0.53    m1_pre_topc(sK1,sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f345,f42])).
% 0.21/0.53  fof(f345,plain,(
% 0.21/0.53    m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f344])).
% 0.21/0.53  fof(f344,plain,(
% 0.21/0.53    m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | m1_pre_topc(sK1,sK0)),
% 0.21/0.53    inference(resolution,[],[f341,f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    m1_pre_topc(sK2,sK0) | m1_pre_topc(sK1,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f341,plain,(
% 0.21/0.53    ( ! [X1] : (~m1_pre_topc(sK2,X1) | m1_pre_topc(sK1,X1) | ~l1_pre_topc(X1)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f340,f46])).
% 0.21/0.53  fof(f340,plain,(
% 0.21/0.53    ( ! [X1] : (~l1_pre_topc(sK2) | ~m1_pre_topc(sK2,X1) | m1_pre_topc(sK1,X1) | ~l1_pre_topc(X1)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f339,f90])).
% 0.21/0.53  fof(f339,plain,(
% 0.21/0.53    ( ! [X1] : (~m1_pre_topc(sK2,X1) | ~l1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))) | m1_pre_topc(sK1,X1) | ~l1_pre_topc(X1)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f338,f90])).
% 0.21/0.53  fof(f338,plain,(
% 0.21/0.53    ( ! [X1] : (~m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X1) | ~l1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))) | m1_pre_topc(sK1,X1) | ~l1_pre_topc(X1)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f337,f45])).
% 0.21/0.53  % (3773)Refutation not found, incomplete strategy% (3773)------------------------------
% 0.21/0.53  % (3773)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (3773)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (3773)Memory used [KB]: 6140
% 0.21/0.53  % (3773)Time elapsed: 0.101 s
% 0.21/0.53  % (3773)------------------------------
% 0.21/0.53  % (3773)------------------------------
% 0.21/0.53  fof(f337,plain,(
% 0.21/0.53    ( ! [X1] : (~v2_pre_topc(sK2) | ~m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X1) | ~l1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))) | m1_pre_topc(sK1,X1) | ~l1_pre_topc(X1)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f336,f90])).
% 0.21/0.53  fof(f336,plain,(
% 0.21/0.53    ( ! [X1] : (~v2_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X1) | ~l1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))) | m1_pre_topc(sK1,X1) | ~l1_pre_topc(X1)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f335,f43])).
% 0.21/0.53  fof(f335,plain,(
% 0.21/0.53    ( ! [X1] : (~v2_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))) | m1_pre_topc(sK1,X1) | ~l1_pre_topc(X1)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f331,f44])).
% 0.21/0.53  fof(f331,plain,(
% 0.21/0.53    ( ! [X1] : (~v2_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))) | m1_pre_topc(sK1,X1) | ~l1_pre_topc(X1)) )),
% 0.21/0.53    inference(superposition,[],[f74,f88])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    ( ! [X2,X0] : (~v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | m1_pre_topc(X2,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f33])).
% 0.21/0.53  fof(f369,plain,(
% 0.21/0.53    ~v3_pre_topc(k2_struct_0(sK1),sK0) | v1_tsep_1(sK1,sK0)),
% 0.21/0.53    inference(forward_demodulation,[],[f368,f88])).
% 0.21/0.53  fof(f368,plain,(
% 0.21/0.53    ~v3_pre_topc(u1_struct_0(sK1),sK0) | v1_tsep_1(sK1,sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f367,f41])).
% 0.21/0.53  fof(f367,plain,(
% 0.21/0.53    ~v3_pre_topc(u1_struct_0(sK1),sK0) | v1_tsep_1(sK1,sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f350,f42])).
% 0.21/0.53  fof(f350,plain,(
% 0.21/0.53    ~v3_pre_topc(u1_struct_0(sK1),sK0) | v1_tsep_1(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.53    inference(resolution,[],[f346,f82])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | v1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f76,f57])).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f62])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f363,plain,(
% 0.21/0.53    ~v1_tsep_1(sK2,sK0) | ~v1_tsep_1(sK1,sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f347,f362])).
% 0.21/0.53  fof(f347,plain,(
% 0.21/0.53    ~v1_tsep_1(sK2,sK0) | ~m1_pre_topc(sK2,sK0) | ~v1_tsep_1(sK1,sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f52,f346])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ~m1_pre_topc(sK1,sK0) | ~v1_tsep_1(sK2,sK0) | ~m1_pre_topc(sK2,sK0) | ~v1_tsep_1(sK1,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    v1_tsep_1(sK2,sK0) | v1_tsep_1(sK1,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f366,plain,(
% 0.21/0.53    v3_pre_topc(k2_struct_0(sK1),sK0) | ~v1_tsep_1(sK1,sK0)),
% 0.21/0.53    inference(forward_demodulation,[],[f365,f88])).
% 0.21/0.53  fof(f365,plain,(
% 0.21/0.53    v3_pre_topc(u1_struct_0(sK1),sK0) | ~v1_tsep_1(sK1,sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f364,f41])).
% 0.21/0.53  fof(f364,plain,(
% 0.21/0.53    v3_pre_topc(u1_struct_0(sK1),sK0) | ~v1_tsep_1(sK1,sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f349,f42])).
% 0.21/0.53  fof(f349,plain,(
% 0.21/0.53    v3_pre_topc(u1_struct_0(sK1),sK0) | ~v1_tsep_1(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.53    inference(resolution,[],[f346,f83])).
% 0.21/0.53  fof(f393,plain,(
% 0.21/0.53    ~v3_pre_topc(k2_struct_0(sK1),sK0)),
% 0.21/0.53    inference(forward_demodulation,[],[f392,f236])).
% 0.21/0.53  fof(f392,plain,(
% 0.21/0.53    ~v3_pre_topc(u1_struct_0(sK2),sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f391,f41])).
% 0.21/0.53  fof(f391,plain,(
% 0.21/0.53    ~v3_pre_topc(u1_struct_0(sK2),sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f390,f42])).
% 0.21/0.53  fof(f390,plain,(
% 0.21/0.53    ~v3_pre_topc(u1_struct_0(sK2),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f376,f387])).
% 0.21/0.53  fof(f376,plain,(
% 0.21/0.53    ~v3_pre_topc(u1_struct_0(sK2),sK0) | v1_tsep_1(sK2,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.53    inference(resolution,[],[f362,f82])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (3771)------------------------------
% 0.21/0.53  % (3771)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (3771)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (3771)Memory used [KB]: 6396
% 0.21/0.53  % (3771)Time elapsed: 0.111 s
% 0.21/0.53  % (3771)------------------------------
% 0.21/0.53  % (3771)------------------------------
% 0.21/0.53  % (3768)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.54  % (3767)Success in time 0.174 s
%------------------------------------------------------------------------------
