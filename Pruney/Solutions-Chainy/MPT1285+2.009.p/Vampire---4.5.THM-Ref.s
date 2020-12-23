%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:06 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  169 (15674 expanded)
%              Number of leaves         :    8 (2923 expanded)
%              Depth                    :   74
%              Number of atoms          :  506 (105844 expanded)
%              Number of equality atoms :  104 (3787 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f517,plain,(
    $false ),
    inference(subsumption_resolution,[],[f516,f505])).

fof(f505,plain,(
    ~ r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) ),
    inference(global_subsumption,[],[f55,f372,f479,f504])).

fof(f504,plain,
    ( ~ r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) ),
    inference(resolution,[],[f496,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f496,plain,(
    r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) ),
    inference(subsumption_resolution,[],[f495,f29])).

fof(f29,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f11])).

% (14410)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,X0)
                        | ~ v3_pre_topc(X2,X0) )
                      & v6_tops_1(X2,X0) )
                    | ( ~ v6_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,X0)
                        | ~ v3_pre_topc(X2,X0) )
                      & v6_tops_1(X2,X0) )
                    | ( ~ v6_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v6_tops_1(X2,X0)
                       => ( v4_tops_1(X2,X0)
                          & v3_pre_topc(X2,X0) ) )
                      & ( ( v4_tops_1(X3,X1)
                          & v3_pre_topc(X3,X1) )
                       => v6_tops_1(X3,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v6_tops_1(X2,X0)
                     => ( v4_tops_1(X2,X0)
                        & v3_pre_topc(X2,X0) ) )
                    & ( ( v4_tops_1(X3,X1)
                        & v3_pre_topc(X3,X1) )
                     => v6_tops_1(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_tops_1)).

fof(f495,plain,
    ( r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f493,f27])).

fof(f27,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f11])).

fof(f493,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f481,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tops_1)).

fof(f481,plain,(
    v4_tops_1(sK3,sK1) ),
    inference(resolution,[],[f479,f373])).

fof(f373,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(resolution,[],[f361,f22])).

fof(f22,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | v4_tops_1(sK3,sK1)
    | ~ v4_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f361,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(backward_demodulation,[],[f64,f359])).

fof(f359,plain,(
    sK2 = k1_tops_1(sK0,sK2) ),
    inference(subsumption_resolution,[],[f358,f76])).

fof(f76,plain,
    ( ~ r1_tarski(sK2,k1_tops_1(sK0,sK2))
    | sK2 = k1_tops_1(sK0,sK2) ),
    inference(resolution,[],[f62,f42])).

fof(f62,plain,(
    r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(subsumption_resolution,[],[f57,f31])).

fof(f31,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f57,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(resolution,[],[f28,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f358,plain,
    ( r1_tarski(sK2,k1_tops_1(sK0,sK2))
    | sK2 = k1_tops_1(sK0,sK2) ),
    inference(subsumption_resolution,[],[f350,f45])).

fof(f45,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f350,plain,
    ( ~ r1_tarski(sK2,sK2)
    | r1_tarski(sK2,k1_tops_1(sK0,sK2))
    | sK2 = k1_tops_1(sK0,sK2) ),
    inference(resolution,[],[f340,f28])).

fof(f340,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(sK2,X0)
      | r1_tarski(sK2,k1_tops_1(sK0,X0))
      | sK2 = k1_tops_1(sK0,sK2) ) ),
    inference(subsumption_resolution,[],[f335,f28])).

fof(f335,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(sK2,X0)
      | r1_tarski(sK2,k1_tops_1(sK0,X0))
      | sK2 = k1_tops_1(sK0,sK2) ) ),
    inference(superposition,[],[f99,f330])).

fof(f330,plain,
    ( sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | sK2 = k1_tops_1(sK0,sK2) ),
    inference(subsumption_resolution,[],[f329,f31])).

fof(f329,plain,
    ( sK2 = k1_tops_1(sK0,sK2)
    | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f328,f28])).

fof(f328,plain,
    ( sK2 = k1_tops_1(sK0,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f327,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v6_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tops_1)).

fof(f327,plain,
    ( v6_tops_1(sK2,sK0)
    | sK2 = k1_tops_1(sK0,sK2) ),
    inference(subsumption_resolution,[],[f325,f66])).

fof(f66,plain,
    ( sK2 != k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | v6_tops_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f60,f31])).

fof(f60,plain,
    ( ~ l1_pre_topc(sK0)
    | sK2 != k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | v6_tops_1(sK2,sK0) ),
    inference(resolution,[],[f28,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1
      | v6_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f325,plain,
    ( sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | sK2 = k1_tops_1(sK0,sK2)
    | v6_tops_1(sK2,sK0) ),
    inference(resolution,[],[f323,f24])).

fof(f24,plain,
    ( ~ v6_tops_1(sK3,sK1)
    | v6_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f323,plain,
    ( v6_tops_1(sK3,sK1)
    | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | sK2 = k1_tops_1(sK0,sK2) ),
    inference(trivial_inequality_removal,[],[f315])).

fof(f315,plain,
    ( sK3 != sK3
    | v6_tops_1(sK3,sK1)
    | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | sK2 = k1_tops_1(sK0,sK2) ),
    inference(superposition,[],[f55,f313])).

fof(f313,plain,
    ( sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | sK2 = k1_tops_1(sK0,sK2) ),
    inference(duplicate_literal_removal,[],[f311])).

fof(f311,plain,
    ( sK2 = k1_tops_1(sK0,sK2)
    | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) ),
    inference(resolution,[],[f285,f136])).

fof(f136,plain,
    ( ~ r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) ),
    inference(resolution,[],[f113,f42])).

fof(f113,plain,
    ( r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3)
    | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f112,f29])).

fof(f112,plain,
    ( sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f110,f27])).

fof(f110,plain,
    ( sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f71,f34])).

fof(f71,plain,
    ( v4_tops_1(sK3,sK1)
    | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f70,f31])).

fof(f70,plain,
    ( v4_tops_1(sK3,sK1)
    | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f69,f28])).

fof(f69,plain,
    ( v4_tops_1(sK3,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f25,f33])).

fof(f25,plain,
    ( v6_tops_1(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f285,plain,
    ( r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | sK2 = k1_tops_1(sK0,sK2)
    | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f284,f31])).

fof(f284,plain,
    ( sK2 = k1_tops_1(sK0,sK2)
    | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f283,f28])).

fof(f283,plain,
    ( sK2 = k1_tops_1(sK0,sK2)
    | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f281,f33])).

fof(f281,plain,
    ( v6_tops_1(sK2,sK0)
    | sK2 = k1_tops_1(sK0,sK2)
    | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) ),
    inference(subsumption_resolution,[],[f279,f66])).

fof(f279,plain,
    ( sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | sK2 = k1_tops_1(sK0,sK2)
    | v6_tops_1(sK2,sK0)
    | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) ),
    inference(resolution,[],[f273,f118])).

fof(f118,plain,
    ( ~ r1_tarski(sK3,k2_pre_topc(sK1,sK3))
    | v6_tops_1(sK2,sK0)
    | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) ),
    inference(resolution,[],[f75,f51])).

fof(f51,plain,(
    m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f46,f29])).

fof(f46,plain,
    ( ~ l1_pre_topc(sK1)
    | m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(resolution,[],[f27,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f75,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | v6_tops_1(sK2,sK0)
      | ~ r1_tarski(sK3,X0)
      | r1_tarski(sK3,k1_tops_1(sK1,X0)) ) ),
    inference(subsumption_resolution,[],[f74,f29])).

fof(f74,plain,(
    ! [X0] :
      ( v6_tops_1(sK2,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_pre_topc(sK1)
      | ~ r1_tarski(sK3,X0)
      | r1_tarski(sK3,k1_tops_1(sK1,X0)) ) ),
    inference(subsumption_resolution,[],[f73,f27])).

fof(f73,plain,(
    ! [X0] :
      ( v6_tops_1(sK2,sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_pre_topc(sK1)
      | ~ r1_tarski(sK3,X0)
      | r1_tarski(sK3,k1_tops_1(sK1,X0)) ) ),
    inference(resolution,[],[f26,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X1,k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

fof(f26,plain,
    ( v3_pre_topc(sK3,sK1)
    | v6_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f273,plain,
    ( r1_tarski(sK3,k2_pre_topc(sK1,sK3))
    | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | sK2 = k1_tops_1(sK0,sK2) ),
    inference(superposition,[],[f115,f268])).

fof(f268,plain,
    ( sK3 = k1_tops_1(sK1,sK3)
    | sK2 = k1_tops_1(sK0,sK2) ),
    inference(resolution,[],[f266,f76])).

fof(f266,plain,
    ( r1_tarski(sK2,k1_tops_1(sK0,sK2))
    | sK3 = k1_tops_1(sK1,sK3) ),
    inference(subsumption_resolution,[],[f259,f45])).

fof(f259,plain,
    ( sK3 = k1_tops_1(sK1,sK3)
    | ~ r1_tarski(sK2,sK2)
    | r1_tarski(sK2,k1_tops_1(sK0,sK2)) ),
    inference(resolution,[],[f178,f28])).

fof(f178,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK3 = k1_tops_1(sK1,sK3)
      | ~ r1_tarski(sK2,X0)
      | r1_tarski(sK2,k1_tops_1(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f177,f31])).

fof(f177,plain,(
    ! [X0] :
      ( sK3 = k1_tops_1(sK1,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ r1_tarski(sK2,X0)
      | r1_tarski(sK2,k1_tops_1(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f176,f28])).

fof(f176,plain,(
    ! [X0] :
      ( sK3 = k1_tops_1(sK1,sK3)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ r1_tarski(sK2,X0)
      | r1_tarski(sK2,k1_tops_1(sK0,X0)) ) ),
    inference(resolution,[],[f170,f38])).

fof(f170,plain,
    ( v3_pre_topc(sK2,sK0)
    | sK3 = k1_tops_1(sK1,sK3) ),
    inference(superposition,[],[f95,f152])).

fof(f152,plain,
    ( sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | sK3 = k1_tops_1(sK1,sK3) ),
    inference(resolution,[],[f123,f72])).

fof(f72,plain,
    ( ~ r1_tarski(sK3,k1_tops_1(sK1,sK3))
    | sK3 = k1_tops_1(sK1,sK3) ),
    inference(resolution,[],[f52,f42])).

fof(f52,plain,(
    r1_tarski(k1_tops_1(sK1,sK3),sK3) ),
    inference(subsumption_resolution,[],[f47,f29])).

fof(f47,plain,
    ( ~ l1_pre_topc(sK1)
    | r1_tarski(k1_tops_1(sK1,sK3),sK3) ),
    inference(resolution,[],[f27,f39])).

fof(f123,plain,
    ( r1_tarski(sK3,k1_tops_1(sK1,sK3))
    | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f122,f31])).

fof(f122,plain,
    ( r1_tarski(sK3,k1_tops_1(sK1,sK3))
    | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f121,f28])).

fof(f121,plain,
    ( r1_tarski(sK3,k1_tops_1(sK1,sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f120,f33])).

fof(f120,plain,
    ( v6_tops_1(sK2,sK0)
    | r1_tarski(sK3,k1_tops_1(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f117,f45])).

fof(f117,plain,
    ( v6_tops_1(sK2,sK0)
    | ~ r1_tarski(sK3,sK3)
    | r1_tarski(sK3,k1_tops_1(sK1,sK3)) ),
    inference(resolution,[],[f75,f27])).

fof(f95,plain,(
    v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0) ),
    inference(subsumption_resolution,[],[f94,f30])).

fof(f30,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f94,plain,
    ( ~ v2_pre_topc(sK0)
    | v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0) ),
    inference(subsumption_resolution,[],[f89,f31])).

fof(f89,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0) ),
    inference(resolution,[],[f61,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f61,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f56,f31])).

fof(f56,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f28,f43])).

fof(f115,plain,
    ( r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3)))
    | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f114,f29])).

fof(f114,plain,
    ( sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3)))
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f111,f27])).

fof(f111,plain,
    ( sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3)))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f71,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f99,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),X0)
      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),k1_tops_1(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f98,f31])).

fof(f98,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),X0)
      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),k1_tops_1(sK0,X0)) ) ),
    inference(resolution,[],[f95,f38])).

fof(f64,plain,(
    v3_pre_topc(k1_tops_1(sK0,sK2),sK0) ),
    inference(subsumption_resolution,[],[f63,f30])).

fof(f63,plain,
    ( ~ v2_pre_topc(sK0)
    | v3_pre_topc(k1_tops_1(sK0,sK2),sK0) ),
    inference(subsumption_resolution,[],[f58,f31])).

fof(f58,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v3_pre_topc(k1_tops_1(sK0,sK2),sK0) ),
    inference(resolution,[],[f28,f37])).

fof(f479,plain,(
    v4_tops_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f478,f465])).

fof(f465,plain,(
    r1_tarski(sK2,k2_pre_topc(sK0,sK2)) ),
    inference(backward_demodulation,[],[f93,f463])).

fof(f463,plain,(
    sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f462,f31])).

fof(f462,plain,
    ( sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f461,f28])).

fof(f461,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f460,f33])).

fof(f460,plain,(
    v6_tops_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f458,f66])).

fof(f458,plain,
    ( sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | v6_tops_1(sK2,sK0) ),
    inference(resolution,[],[f456,f24])).

fof(f456,plain,
    ( v6_tops_1(sK3,sK1)
    | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) ),
    inference(trivial_inequality_removal,[],[f447])).

fof(f447,plain,
    ( sK3 != sK3
    | v6_tops_1(sK3,sK1)
    | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) ),
    inference(superposition,[],[f55,f446])).

fof(f446,plain,
    ( sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) ),
    inference(duplicate_literal_removal,[],[f444])).

fof(f444,plain,
    ( sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) ),
    inference(resolution,[],[f443,f136])).

fof(f443,plain,
    ( r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f442,f31])).

fof(f442,plain,
    ( r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f441,f28])).

fof(f441,plain,
    ( r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f440,f33])).

fof(f440,plain,
    ( v6_tops_1(sK2,sK0)
    | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) ),
    inference(subsumption_resolution,[],[f438,f66])).

fof(f438,plain,
    ( sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | v6_tops_1(sK2,sK0)
    | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) ),
    inference(resolution,[],[f431,f118])).

fof(f431,plain,
    ( r1_tarski(sK3,k2_pre_topc(sK1,sK3))
    | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) ),
    inference(backward_demodulation,[],[f115,f426])).

fof(f426,plain,(
    sK3 = k1_tops_1(sK1,sK3) ),
    inference(subsumption_resolution,[],[f425,f72])).

fof(f425,plain,
    ( sK3 = k1_tops_1(sK1,sK3)
    | r1_tarski(sK3,k1_tops_1(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f417,f45])).

fof(f417,plain,
    ( sK3 = k1_tops_1(sK1,sK3)
    | ~ r1_tarski(sK3,sK3)
    | r1_tarski(sK3,k1_tops_1(sK1,sK3)) ),
    inference(resolution,[],[f403,f27])).

fof(f403,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | sK3 = k1_tops_1(sK1,sK3)
      | ~ r1_tarski(sK3,X0)
      | r1_tarski(sK3,k1_tops_1(sK1,X0)) ) ),
    inference(subsumption_resolution,[],[f402,f29])).

fof(f402,plain,(
    ! [X0] :
      ( sK3 = k1_tops_1(sK1,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_pre_topc(sK1)
      | ~ r1_tarski(sK3,X0)
      | r1_tarski(sK3,k1_tops_1(sK1,X0)) ) ),
    inference(subsumption_resolution,[],[f401,f27])).

fof(f401,plain,(
    ! [X0] :
      ( sK3 = k1_tops_1(sK1,sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_pre_topc(sK1)
      | ~ r1_tarski(sK3,X0)
      | r1_tarski(sK3,k1_tops_1(sK1,X0)) ) ),
    inference(resolution,[],[f387,f38])).

fof(f387,plain,
    ( v3_pre_topc(sK3,sK1)
    | sK3 = k1_tops_1(sK1,sK3) ),
    inference(resolution,[],[f371,f374])).

fof(f374,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | v3_pre_topc(sK3,sK1) ),
    inference(resolution,[],[f361,f21])).

fof(f21,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | v3_pre_topc(sK3,sK1)
    | ~ v4_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f371,plain,
    ( v4_tops_1(sK2,sK0)
    | sK3 = k1_tops_1(sK1,sK3) ),
    inference(subsumption_resolution,[],[f365,f167])).

fof(f167,plain,
    ( r1_tarski(sK2,k2_pre_topc(sK0,sK2))
    | sK3 = k1_tops_1(sK1,sK3) ),
    inference(superposition,[],[f93,f152])).

fof(f365,plain,
    ( ~ r1_tarski(sK2,k2_pre_topc(sK0,sK2))
    | v4_tops_1(sK2,sK0)
    | sK3 = k1_tops_1(sK1,sK3) ),
    inference(backward_demodulation,[],[f172,f359])).

fof(f172,plain,
    ( ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | v4_tops_1(sK2,sK0)
    | sK3 = k1_tops_1(sK1,sK3) ),
    inference(subsumption_resolution,[],[f168,f45])).

fof(f168,plain,
    ( ~ r1_tarski(sK2,sK2)
    | ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | v4_tops_1(sK2,sK0)
    | sK3 = k1_tops_1(sK1,sK3) ),
    inference(superposition,[],[f65,f152])).

fof(f65,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
    | ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | v4_tops_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f59,f31])).

fof(f59,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
    | ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | v4_tops_1(sK2,sK0) ),
    inference(resolution,[],[f28,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | v4_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f93,plain,(
    r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f88,f31])).

fof(f88,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,sK2)) ),
    inference(resolution,[],[f61,f39])).

fof(f478,plain,
    ( ~ r1_tarski(sK2,k2_pre_topc(sK0,sK2))
    | v4_tops_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f470,f45])).

fof(f470,plain,
    ( ~ r1_tarski(sK2,sK2)
    | ~ r1_tarski(sK2,k2_pre_topc(sK0,sK2))
    | v4_tops_1(sK2,sK0) ),
    inference(backward_demodulation,[],[f362,f463])).

fof(f362,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
    | ~ r1_tarski(sK2,k2_pre_topc(sK0,sK2))
    | v4_tops_1(sK2,sK0) ),
    inference(backward_demodulation,[],[f65,f359])).

fof(f372,plain,
    ( ~ v6_tops_1(sK3,sK1)
    | ~ v4_tops_1(sK2,sK0) ),
    inference(resolution,[],[f361,f23])).

fof(f23,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | ~ v6_tops_1(sK3,sK1)
    | ~ v4_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f55,plain,
    ( sK3 != k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | v6_tops_1(sK3,sK1) ),
    inference(subsumption_resolution,[],[f50,f29])).

fof(f50,plain,
    ( ~ l1_pre_topc(sK1)
    | sK3 != k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | v6_tops_1(sK3,sK1) ),
    inference(resolution,[],[f27,f32])).

fof(f516,plain,(
    r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) ),
    inference(subsumption_resolution,[],[f507,f499])).

fof(f499,plain,(
    r1_tarski(sK3,k2_pre_topc(sK1,sK3)) ),
    inference(forward_demodulation,[],[f498,f426])).

fof(f498,plain,(
    r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) ),
    inference(subsumption_resolution,[],[f497,f29])).

fof(f497,plain,
    ( r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3)))
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f494,f27])).

fof(f494,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3)))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f481,f35])).

fof(f507,plain,
    ( ~ r1_tarski(sK3,k2_pre_topc(sK1,sK3))
    | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) ),
    inference(resolution,[],[f492,f51])).

fof(f492,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r1_tarski(sK3,X0)
      | r1_tarski(sK3,k1_tops_1(sK1,X0)) ) ),
    inference(subsumption_resolution,[],[f491,f29])).

fof(f491,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_pre_topc(sK1)
      | ~ r1_tarski(sK3,X0)
      | r1_tarski(sK3,k1_tops_1(sK1,X0)) ) ),
    inference(subsumption_resolution,[],[f490,f27])).

fof(f490,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_pre_topc(sK1)
      | ~ r1_tarski(sK3,X0)
      | r1_tarski(sK3,k1_tops_1(sK1,X0)) ) ),
    inference(resolution,[],[f480,f38])).

fof(f480,plain,(
    v3_pre_topc(sK3,sK1) ),
    inference(resolution,[],[f479,f374])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:42:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (14407)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.49  % (14406)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.50  % (14400)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (14401)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (14416)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.51  % (14398)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (14399)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (14400)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (14397)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (14408)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (14403)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.52  % (14396)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (14415)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.52  % (14417)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.52  % (14395)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.52  % (14414)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f517,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(subsumption_resolution,[],[f516,f505])).
% 0.21/0.52  fof(f505,plain,(
% 0.21/0.52    ~r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))),
% 0.21/0.52    inference(global_subsumption,[],[f55,f372,f479,f504])).
% 0.21/0.52  fof(f504,plain,(
% 0.21/0.52    ~r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))),
% 0.21/0.52    inference(resolution,[],[f496,f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.52  fof(f496,plain,(
% 0.21/0.52    r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f495,f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    l1_pre_topc(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  % (14410)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & (v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,negated_conjecture,(
% 0.21/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v6_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v3_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)) => v6_tops_1(X3,X1)))))))),
% 0.21/0.52    inference(negated_conjecture,[],[f8])).
% 0.21/0.52  fof(f8,conjecture,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v6_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v3_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)) => v6_tops_1(X3,X1)))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_tops_1)).
% 0.21/0.52  fof(f495,plain,(
% 0.21/0.52    r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) | ~l1_pre_topc(sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f493,f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f493,plain,(
% 0.21/0.52    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) | ~l1_pre_topc(sK1)),
% 0.21/0.52    inference(resolution,[],[f481,f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tops_1)).
% 0.21/0.52  fof(f481,plain,(
% 0.21/0.52    v4_tops_1(sK3,sK1)),
% 0.21/0.52    inference(resolution,[],[f479,f373])).
% 0.21/0.52  fof(f373,plain,(
% 0.21/0.52    ~v4_tops_1(sK2,sK0) | v4_tops_1(sK3,sK1)),
% 0.21/0.52    inference(resolution,[],[f361,f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ~v3_pre_topc(sK2,sK0) | v4_tops_1(sK3,sK1) | ~v4_tops_1(sK2,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f361,plain,(
% 0.21/0.52    v3_pre_topc(sK2,sK0)),
% 0.21/0.52    inference(backward_demodulation,[],[f64,f359])).
% 0.21/0.52  fof(f359,plain,(
% 0.21/0.52    sK2 = k1_tops_1(sK0,sK2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f358,f76])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    ~r1_tarski(sK2,k1_tops_1(sK0,sK2)) | sK2 = k1_tops_1(sK0,sK2)),
% 0.21/0.52    inference(resolution,[],[f62,f42])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f57,f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    l1_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 0.21/0.52    inference(resolution,[],[f28,f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f358,plain,(
% 0.21/0.52    r1_tarski(sK2,k1_tops_1(sK0,sK2)) | sK2 = k1_tops_1(sK0,sK2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f350,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.52    inference(equality_resolution,[],[f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f350,plain,(
% 0.21/0.52    ~r1_tarski(sK2,sK2) | r1_tarski(sK2,k1_tops_1(sK0,sK2)) | sK2 = k1_tops_1(sK0,sK2)),
% 0.21/0.52    inference(resolution,[],[f340,f28])).
% 0.21/0.52  fof(f340,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK2,X0) | r1_tarski(sK2,k1_tops_1(sK0,X0)) | sK2 = k1_tops_1(sK0,sK2)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f335,f28])).
% 0.21/0.52  fof(f335,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK2,X0) | r1_tarski(sK2,k1_tops_1(sK0,X0)) | sK2 = k1_tops_1(sK0,sK2)) )),
% 0.21/0.52    inference(superposition,[],[f99,f330])).
% 0.21/0.52  fof(f330,plain,(
% 0.21/0.52    sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) | sK2 = k1_tops_1(sK0,sK2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f329,f31])).
% 0.21/0.52  fof(f329,plain,(
% 0.21/0.52    sK2 = k1_tops_1(sK0,sK2) | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) | ~l1_pre_topc(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f328,f28])).
% 0.21/0.52  fof(f328,plain,(
% 0.21/0.52    sK2 = k1_tops_1(sK0,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) | ~l1_pre_topc(sK0)),
% 0.21/0.52    inference(resolution,[],[f327,f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v6_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((v6_tops_1(X1,X0) <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_tops_1(X1,X0) <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tops_1)).
% 0.21/0.52  fof(f327,plain,(
% 0.21/0.52    v6_tops_1(sK2,sK0) | sK2 = k1_tops_1(sK0,sK2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f325,f66])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    sK2 != k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) | v6_tops_1(sK2,sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f60,f31])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | sK2 != k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) | v6_tops_1(sK2,sK0)),
% 0.21/0.52    inference(resolution,[],[f28,f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1 | v6_tops_1(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f325,plain,(
% 0.21/0.52    sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) | sK2 = k1_tops_1(sK0,sK2) | v6_tops_1(sK2,sK0)),
% 0.21/0.52    inference(resolution,[],[f323,f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ~v6_tops_1(sK3,sK1) | v6_tops_1(sK2,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f323,plain,(
% 0.21/0.52    v6_tops_1(sK3,sK1) | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) | sK2 = k1_tops_1(sK0,sK2)),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f315])).
% 0.21/0.52  fof(f315,plain,(
% 0.21/0.52    sK3 != sK3 | v6_tops_1(sK3,sK1) | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) | sK2 = k1_tops_1(sK0,sK2)),
% 0.21/0.52    inference(superposition,[],[f55,f313])).
% 0.21/0.52  fof(f313,plain,(
% 0.21/0.52    sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) | sK2 = k1_tops_1(sK0,sK2)),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f311])).
% 0.21/0.52  fof(f311,plain,(
% 0.21/0.52    sK2 = k1_tops_1(sK0,sK2) | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))),
% 0.21/0.52    inference(resolution,[],[f285,f136])).
% 0.21/0.52  fof(f136,plain,(
% 0.21/0.52    ~r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))),
% 0.21/0.52    inference(resolution,[],[f113,f42])).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))),
% 0.21/0.52    inference(subsumption_resolution,[],[f112,f29])).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) | ~l1_pre_topc(sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f110,f27])).
% 0.21/0.52  fof(f110,plain,(
% 0.21/0.52    sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) | ~l1_pre_topc(sK1)),
% 0.21/0.52    inference(resolution,[],[f71,f34])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    v4_tops_1(sK3,sK1) | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))),
% 0.21/0.52    inference(subsumption_resolution,[],[f70,f31])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    v4_tops_1(sK3,sK1) | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) | ~l1_pre_topc(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f69,f28])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    v4_tops_1(sK3,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) | ~l1_pre_topc(sK0)),
% 0.21/0.52    inference(resolution,[],[f25,f33])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    v6_tops_1(sK2,sK0) | v4_tops_1(sK3,sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f285,plain,(
% 0.21/0.52    r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) | sK2 = k1_tops_1(sK0,sK2) | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))),
% 0.21/0.52    inference(subsumption_resolution,[],[f284,f31])).
% 0.21/0.52  fof(f284,plain,(
% 0.21/0.52    sK2 = k1_tops_1(sK0,sK2) | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) | ~l1_pre_topc(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f283,f28])).
% 0.21/0.52  fof(f283,plain,(
% 0.21/0.52    sK2 = k1_tops_1(sK0,sK2) | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) | ~l1_pre_topc(sK0)),
% 0.21/0.52    inference(resolution,[],[f281,f33])).
% 0.21/0.52  fof(f281,plain,(
% 0.21/0.52    v6_tops_1(sK2,sK0) | sK2 = k1_tops_1(sK0,sK2) | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))),
% 0.21/0.52    inference(subsumption_resolution,[],[f279,f66])).
% 0.21/0.52  fof(f279,plain,(
% 0.21/0.52    sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) | sK2 = k1_tops_1(sK0,sK2) | v6_tops_1(sK2,sK0) | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))),
% 0.21/0.52    inference(resolution,[],[f273,f118])).
% 0.21/0.52  fof(f118,plain,(
% 0.21/0.52    ~r1_tarski(sK3,k2_pre_topc(sK1,sK3)) | v6_tops_1(sK2,sK0) | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))),
% 0.21/0.52    inference(resolution,[],[f75,f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.52    inference(subsumption_resolution,[],[f46,f29])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ~l1_pre_topc(sK1) | m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.52    inference(resolution,[],[f27,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | v6_tops_1(sK2,sK0) | ~r1_tarski(sK3,X0) | r1_tarski(sK3,k1_tops_1(sK1,X0))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f74,f29])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    ( ! [X0] : (v6_tops_1(sK2,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~r1_tarski(sK3,X0) | r1_tarski(sK3,k1_tops_1(sK1,X0))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f73,f27])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    ( ! [X0] : (v6_tops_1(sK2,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~r1_tarski(sK3,X0) | r1_tarski(sK3,k1_tops_1(sK1,X0))) )),
% 0.21/0.52    inference(resolution,[],[f26,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~r1_tarski(X1,X2) | r1_tarski(X1,k1_tops_1(X0,X2))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    v3_pre_topc(sK3,sK1) | v6_tops_1(sK2,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f273,plain,(
% 0.21/0.52    r1_tarski(sK3,k2_pre_topc(sK1,sK3)) | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) | sK2 = k1_tops_1(sK0,sK2)),
% 0.21/0.52    inference(superposition,[],[f115,f268])).
% 0.21/0.52  fof(f268,plain,(
% 0.21/0.52    sK3 = k1_tops_1(sK1,sK3) | sK2 = k1_tops_1(sK0,sK2)),
% 0.21/0.52    inference(resolution,[],[f266,f76])).
% 0.21/0.52  fof(f266,plain,(
% 0.21/0.52    r1_tarski(sK2,k1_tops_1(sK0,sK2)) | sK3 = k1_tops_1(sK1,sK3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f259,f45])).
% 0.21/0.52  fof(f259,plain,(
% 0.21/0.52    sK3 = k1_tops_1(sK1,sK3) | ~r1_tarski(sK2,sK2) | r1_tarski(sK2,k1_tops_1(sK0,sK2))),
% 0.21/0.52    inference(resolution,[],[f178,f28])).
% 0.21/0.52  fof(f178,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | sK3 = k1_tops_1(sK1,sK3) | ~r1_tarski(sK2,X0) | r1_tarski(sK2,k1_tops_1(sK0,X0))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f177,f31])).
% 0.21/0.52  fof(f177,plain,(
% 0.21/0.52    ( ! [X0] : (sK3 = k1_tops_1(sK1,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~r1_tarski(sK2,X0) | r1_tarski(sK2,k1_tops_1(sK0,X0))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f176,f28])).
% 0.21/0.52  fof(f176,plain,(
% 0.21/0.52    ( ! [X0] : (sK3 = k1_tops_1(sK1,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~r1_tarski(sK2,X0) | r1_tarski(sK2,k1_tops_1(sK0,X0))) )),
% 0.21/0.52    inference(resolution,[],[f170,f38])).
% 0.21/0.52  fof(f170,plain,(
% 0.21/0.52    v3_pre_topc(sK2,sK0) | sK3 = k1_tops_1(sK1,sK3)),
% 0.21/0.52    inference(superposition,[],[f95,f152])).
% 0.21/0.52  fof(f152,plain,(
% 0.21/0.52    sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) | sK3 = k1_tops_1(sK1,sK3)),
% 0.21/0.52    inference(resolution,[],[f123,f72])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    ~r1_tarski(sK3,k1_tops_1(sK1,sK3)) | sK3 = k1_tops_1(sK1,sK3)),
% 0.21/0.52    inference(resolution,[],[f52,f42])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    r1_tarski(k1_tops_1(sK1,sK3),sK3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f47,f29])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ~l1_pre_topc(sK1) | r1_tarski(k1_tops_1(sK1,sK3),sK3)),
% 0.21/0.52    inference(resolution,[],[f27,f39])).
% 0.21/0.52  fof(f123,plain,(
% 0.21/0.52    r1_tarski(sK3,k1_tops_1(sK1,sK3)) | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))),
% 0.21/0.52    inference(subsumption_resolution,[],[f122,f31])).
% 0.21/0.52  fof(f122,plain,(
% 0.21/0.52    r1_tarski(sK3,k1_tops_1(sK1,sK3)) | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) | ~l1_pre_topc(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f121,f28])).
% 0.21/0.52  fof(f121,plain,(
% 0.21/0.52    r1_tarski(sK3,k1_tops_1(sK1,sK3)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) | ~l1_pre_topc(sK0)),
% 0.21/0.52    inference(resolution,[],[f120,f33])).
% 0.21/0.52  fof(f120,plain,(
% 0.21/0.52    v6_tops_1(sK2,sK0) | r1_tarski(sK3,k1_tops_1(sK1,sK3))),
% 0.21/0.52    inference(subsumption_resolution,[],[f117,f45])).
% 0.21/0.52  fof(f117,plain,(
% 0.21/0.52    v6_tops_1(sK2,sK0) | ~r1_tarski(sK3,sK3) | r1_tarski(sK3,k1_tops_1(sK1,sK3))),
% 0.21/0.52    inference(resolution,[],[f75,f27])).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f94,f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    v2_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    ~v2_pre_topc(sK0) | v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f89,f31])).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0)),
% 0.21/0.52    inference(resolution,[],[f61,f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v3_pre_topc(k1_tops_1(X0,X1),X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    inference(subsumption_resolution,[],[f56,f31])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    inference(resolution,[],[f28,f43])).
% 0.21/0.52  fof(f115,plain,(
% 0.21/0.52    r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))),
% 0.21/0.52    inference(subsumption_resolution,[],[f114,f29])).
% 0.21/0.52  fof(f114,plain,(
% 0.21/0.52    sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) | r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) | ~l1_pre_topc(sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f111,f27])).
% 0.21/0.52  fof(f111,plain,(
% 0.21/0.52    sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) | ~l1_pre_topc(sK1)),
% 0.21/0.52    inference(resolution,[],[f71,f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),X0) | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),k1_tops_1(sK0,X0))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f98,f31])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),X0) | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),k1_tops_1(sK0,X0))) )),
% 0.21/0.52    inference(resolution,[],[f95,f38])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    v3_pre_topc(k1_tops_1(sK0,sK2),sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f63,f30])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    ~v2_pre_topc(sK0) | v3_pre_topc(k1_tops_1(sK0,sK2),sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f58,f31])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v3_pre_topc(k1_tops_1(sK0,sK2),sK0)),
% 0.21/0.52    inference(resolution,[],[f28,f37])).
% 0.21/0.52  fof(f479,plain,(
% 0.21/0.52    v4_tops_1(sK2,sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f478,f465])).
% 0.21/0.52  fof(f465,plain,(
% 0.21/0.52    r1_tarski(sK2,k2_pre_topc(sK0,sK2))),
% 0.21/0.52    inference(backward_demodulation,[],[f93,f463])).
% 0.21/0.52  fof(f463,plain,(
% 0.21/0.52    sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))),
% 0.21/0.52    inference(subsumption_resolution,[],[f462,f31])).
% 0.21/0.52  fof(f462,plain,(
% 0.21/0.52    sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) | ~l1_pre_topc(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f461,f28])).
% 0.21/0.52  fof(f461,plain,(
% 0.21/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) | ~l1_pre_topc(sK0)),
% 0.21/0.52    inference(resolution,[],[f460,f33])).
% 0.21/0.52  fof(f460,plain,(
% 0.21/0.52    v6_tops_1(sK2,sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f458,f66])).
% 0.21/0.53  fof(f458,plain,(
% 0.21/0.53    sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) | v6_tops_1(sK2,sK0)),
% 0.21/0.53    inference(resolution,[],[f456,f24])).
% 0.21/0.53  fof(f456,plain,(
% 0.21/0.53    v6_tops_1(sK3,sK1) | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f447])).
% 0.21/0.53  fof(f447,plain,(
% 0.21/0.53    sK3 != sK3 | v6_tops_1(sK3,sK1) | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))),
% 0.21/0.53    inference(superposition,[],[f55,f446])).
% 0.21/0.53  fof(f446,plain,(
% 0.21/0.53    sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f444])).
% 0.21/0.53  fof(f444,plain,(
% 0.21/0.53    sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))),
% 0.21/0.53    inference(resolution,[],[f443,f136])).
% 0.21/0.53  fof(f443,plain,(
% 0.21/0.53    r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))),
% 0.21/0.53    inference(subsumption_resolution,[],[f442,f31])).
% 0.21/0.53  fof(f442,plain,(
% 0.21/0.53    r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f441,f28])).
% 0.21/0.53  fof(f441,plain,(
% 0.21/0.53    r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(resolution,[],[f440,f33])).
% 0.21/0.53  fof(f440,plain,(
% 0.21/0.53    v6_tops_1(sK2,sK0) | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))),
% 0.21/0.53    inference(subsumption_resolution,[],[f438,f66])).
% 0.21/0.53  fof(f438,plain,(
% 0.21/0.53    sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) | v6_tops_1(sK2,sK0) | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))),
% 0.21/0.53    inference(resolution,[],[f431,f118])).
% 0.21/0.53  fof(f431,plain,(
% 0.21/0.53    r1_tarski(sK3,k2_pre_topc(sK1,sK3)) | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))),
% 0.21/0.53    inference(backward_demodulation,[],[f115,f426])).
% 0.21/0.53  fof(f426,plain,(
% 0.21/0.53    sK3 = k1_tops_1(sK1,sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f425,f72])).
% 0.21/0.53  fof(f425,plain,(
% 0.21/0.53    sK3 = k1_tops_1(sK1,sK3) | r1_tarski(sK3,k1_tops_1(sK1,sK3))),
% 0.21/0.53    inference(subsumption_resolution,[],[f417,f45])).
% 0.21/0.53  fof(f417,plain,(
% 0.21/0.53    sK3 = k1_tops_1(sK1,sK3) | ~r1_tarski(sK3,sK3) | r1_tarski(sK3,k1_tops_1(sK1,sK3))),
% 0.21/0.53    inference(resolution,[],[f403,f27])).
% 0.21/0.53  fof(f403,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | sK3 = k1_tops_1(sK1,sK3) | ~r1_tarski(sK3,X0) | r1_tarski(sK3,k1_tops_1(sK1,X0))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f402,f29])).
% 0.21/0.53  fof(f402,plain,(
% 0.21/0.53    ( ! [X0] : (sK3 = k1_tops_1(sK1,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~r1_tarski(sK3,X0) | r1_tarski(sK3,k1_tops_1(sK1,X0))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f401,f27])).
% 0.21/0.53  fof(f401,plain,(
% 0.21/0.53    ( ! [X0] : (sK3 = k1_tops_1(sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~r1_tarski(sK3,X0) | r1_tarski(sK3,k1_tops_1(sK1,X0))) )),
% 0.21/0.53    inference(resolution,[],[f387,f38])).
% 0.21/0.53  fof(f387,plain,(
% 0.21/0.53    v3_pre_topc(sK3,sK1) | sK3 = k1_tops_1(sK1,sK3)),
% 0.21/0.53    inference(resolution,[],[f371,f374])).
% 0.21/0.53  fof(f374,plain,(
% 0.21/0.53    ~v4_tops_1(sK2,sK0) | v3_pre_topc(sK3,sK1)),
% 0.21/0.53    inference(resolution,[],[f361,f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ~v3_pre_topc(sK2,sK0) | v3_pre_topc(sK3,sK1) | ~v4_tops_1(sK2,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f371,plain,(
% 0.21/0.53    v4_tops_1(sK2,sK0) | sK3 = k1_tops_1(sK1,sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f365,f167])).
% 0.21/0.53  fof(f167,plain,(
% 0.21/0.53    r1_tarski(sK2,k2_pre_topc(sK0,sK2)) | sK3 = k1_tops_1(sK1,sK3)),
% 0.21/0.53    inference(superposition,[],[f93,f152])).
% 0.21/0.53  fof(f365,plain,(
% 0.21/0.53    ~r1_tarski(sK2,k2_pre_topc(sK0,sK2)) | v4_tops_1(sK2,sK0) | sK3 = k1_tops_1(sK1,sK3)),
% 0.21/0.53    inference(backward_demodulation,[],[f172,f359])).
% 0.21/0.53  fof(f172,plain,(
% 0.21/0.53    ~r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) | v4_tops_1(sK2,sK0) | sK3 = k1_tops_1(sK1,sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f168,f45])).
% 0.21/0.53  fof(f168,plain,(
% 0.21/0.53    ~r1_tarski(sK2,sK2) | ~r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) | v4_tops_1(sK2,sK0) | sK3 = k1_tops_1(sK1,sK3)),
% 0.21/0.53    inference(superposition,[],[f65,f152])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ~r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2) | ~r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) | v4_tops_1(sK2,sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f59,f31])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ~l1_pre_topc(sK0) | ~r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2) | ~r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) | v4_tops_1(sK2,sK0)),
% 0.21/0.53    inference(resolution,[],[f28,f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | v4_tops_1(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,sK2))),
% 0.21/0.53    inference(subsumption_resolution,[],[f88,f31])).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    ~l1_pre_topc(sK0) | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,sK2))),
% 0.21/0.53    inference(resolution,[],[f61,f39])).
% 0.21/0.53  fof(f478,plain,(
% 0.21/0.53    ~r1_tarski(sK2,k2_pre_topc(sK0,sK2)) | v4_tops_1(sK2,sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f470,f45])).
% 0.21/0.53  fof(f470,plain,(
% 0.21/0.53    ~r1_tarski(sK2,sK2) | ~r1_tarski(sK2,k2_pre_topc(sK0,sK2)) | v4_tops_1(sK2,sK0)),
% 0.21/0.53    inference(backward_demodulation,[],[f362,f463])).
% 0.21/0.53  fof(f362,plain,(
% 0.21/0.53    ~r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2) | ~r1_tarski(sK2,k2_pre_topc(sK0,sK2)) | v4_tops_1(sK2,sK0)),
% 0.21/0.53    inference(backward_demodulation,[],[f65,f359])).
% 0.21/0.53  fof(f372,plain,(
% 0.21/0.53    ~v6_tops_1(sK3,sK1) | ~v4_tops_1(sK2,sK0)),
% 0.21/0.53    inference(resolution,[],[f361,f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ~v3_pre_topc(sK2,sK0) | ~v6_tops_1(sK3,sK1) | ~v4_tops_1(sK2,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    sK3 != k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) | v6_tops_1(sK3,sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f50,f29])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ~l1_pre_topc(sK1) | sK3 != k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) | v6_tops_1(sK3,sK1)),
% 0.21/0.53    inference(resolution,[],[f27,f32])).
% 0.21/0.53  fof(f516,plain,(
% 0.21/0.53    r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))),
% 0.21/0.53    inference(subsumption_resolution,[],[f507,f499])).
% 0.21/0.53  fof(f499,plain,(
% 0.21/0.53    r1_tarski(sK3,k2_pre_topc(sK1,sK3))),
% 0.21/0.53    inference(forward_demodulation,[],[f498,f426])).
% 0.21/0.53  fof(f498,plain,(
% 0.21/0.53    r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3)))),
% 0.21/0.53    inference(subsumption_resolution,[],[f497,f29])).
% 0.21/0.53  fof(f497,plain,(
% 0.21/0.53    r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) | ~l1_pre_topc(sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f494,f27])).
% 0.21/0.53  fof(f494,plain,(
% 0.21/0.53    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) | ~l1_pre_topc(sK1)),
% 0.21/0.53    inference(resolution,[],[f481,f35])).
% 0.21/0.53  fof(f507,plain,(
% 0.21/0.53    ~r1_tarski(sK3,k2_pre_topc(sK1,sK3)) | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))),
% 0.21/0.53    inference(resolution,[],[f492,f51])).
% 0.21/0.53  fof(f492,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~r1_tarski(sK3,X0) | r1_tarski(sK3,k1_tops_1(sK1,X0))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f491,f29])).
% 0.21/0.53  fof(f491,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~r1_tarski(sK3,X0) | r1_tarski(sK3,k1_tops_1(sK1,X0))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f490,f27])).
% 0.21/0.53  fof(f490,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~r1_tarski(sK3,X0) | r1_tarski(sK3,k1_tops_1(sK1,X0))) )),
% 0.21/0.53    inference(resolution,[],[f480,f38])).
% 0.21/0.53  fof(f480,plain,(
% 0.21/0.53    v3_pre_topc(sK3,sK1)),
% 0.21/0.53    inference(resolution,[],[f479,f374])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (14400)------------------------------
% 0.21/0.53  % (14400)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (14400)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (14400)Memory used [KB]: 6524
% 0.21/0.53  % (14400)Time elapsed: 0.109 s
% 0.21/0.53  % (14400)------------------------------
% 0.21/0.53  % (14400)------------------------------
% 0.21/0.53  % (14409)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.53  % (14418)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.53  % (14394)Success in time 0.165 s
%------------------------------------------------------------------------------
